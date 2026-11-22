mod parquet;

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

const DAY_MS: i64 = 86_400_000;
const WEEK_MS: i64 = 7 * DAY_MS;
const GAP_MS: i64 = 1_800_000;
const NP: usize = 256; // partitions

// ---------------- hashing ----------------
#[inline]
fn fold(a: u64, b: u64) -> u64 {
    let r = (a as u128).wrapping_mul(b as u128);
    (r as u64) ^ ((r >> 64) as u64)
}
#[inline]
fn h64(s: &[u8]) -> u64 {
    let mut h: u64 = 0x243f6a8885a308d3 ^ (s.len() as u64).wrapping_mul(0x9e3779b97f4a7c15);
    let mut i = 0;
    while i + 8 <= s.len() {
        let w = u64::from_le_bytes(s[i..i + 8].try_into().unwrap());
        h = fold(h ^ w ^ 0xa0761d6478bd642f, 0xe7037ed1a0b428db);
        i += 8;
    }
    if i < s.len() {
        let mut buf = [0u8; 8];
        buf[..s.len() - i].copy_from_slice(&s[i..]);
        let w = u64::from_le_bytes(buf);
        h = fold(h ^ w ^ 0x8ebc6af09c88c6e3, 0x589965cc75374cc3);
    }
    fold(h ^ 0x1d8e4e27c47d124f, 0x9e3779b97f4a7c15)
}

#[derive(Default)]
struct IdHasher(u64);
impl Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        unreachable!()
    }
    fn write_u64(&mut self, v: u64) {
        self.0 = v;
    }
}
type IdMap<V> = HashMap<u64, V, BuildHasherDefault<IdHasher>>;

#[inline]
fn part_of(h: u64) -> usize {
    (h >> 56) as usize
}

// ---------------- string refs into buffers ----------------
// buf index (16 bits) | len (16 bits) | offset (32 bits)
#[inline]
fn mkref(buf: usize, off: usize, len: usize) -> u64 {
    ((buf as u64) << 48) | ((len as u64) << 32) | off as u64
}
#[inline]
fn deref<'a>(bufs: &'a [&'static [u8]], r: u64) -> &'a [u8] {
    let b = (r >> 48) as usize;
    let l = ((r >> 32) & 0xffff) as usize;
    let o = (r & 0xffff_ffff) as usize;
    &bufs[b][o..o + l]
}

// ---------------- CSV ----------------
#[inline]
fn memchr_nl(s: &[u8], from: usize) -> usize {
    match s[from..].iter().position(|&c| c == b'\n') {
        Some(p) => from + p,
        None => s.len(),
    }
}

/// Split a line into exactly N fields; returns (start,end) of each unquoted value
/// relative to the line. None if malformed.
#[inline]
fn split<const N: usize>(line: &[u8]) -> Option<[(u32, u32); N]> {
    let mut out = [(0u32, 0u32); N];
    let mut k = 0;
    let mut st = 0usize;
    let n = line.len();
    let mut i = 0usize;
    let mut has_q = false;
    loop {
        let end_field = i == n || line[i] == b',';
        if end_field {
            if k >= N {
                return None;
            }
            let (mut a, mut b) = (st, i);
            if has_q {
                if b - a < 2 || line[a] != b'"' || line[b - 1] != b'"' {
                    return None;
                }
                a += 1;
                b -= 1;
                if line[a..b].contains(&b'"') {
                    return None;
                }
            }
            out[k] = (a as u32, b as u32);
            k += 1;
            if i == n {
                break;
            }
            st = i + 1;
            has_q = false;
        } else if line[i] == b'"' {
            has_q = true;
        }
        i += 1;
    }
    if k != N {
        return None;
    }
    Some(out)
}


const LO: u64 = 0x0101010101010101;
const HI: u64 = 0x8080808080808080;
#[inline(always)]
fn has(w: u64, c: u8) -> u64 {
    let x = w ^ (LO * c as u64);
    x.wrapping_sub(LO) & !x & HI
}
#[inline(always)]
fn next_special(buf: &[u8], mut i: usize, e: usize) -> usize {
    while i + 8 <= e {
        let w = u64::from_le_bytes(buf[i..i + 8].try_into().unwrap());
        let m = has(w, b',') | has(w, b'\n') | has(w, b'"');
        if m != 0 {
            return i + (m.trailing_zeros() / 8) as usize;
        }
        i += 8;
    }
    while i < e {
        let c = buf[i];
        if c == b',' || c == b'\n' || c == b'"' {
            return i;
        }
        i += 1;
    }
    e
}

/// Scan lines in buf[s..e). For every well-formed line with exactly N fields,
/// call f(line_start, fields) with absolute (start,end) of unquoted values.
#[inline(always)]
fn scan<const N: usize>(buf: &[u8], s: usize, e: usize, mut f: impl FnMut(usize, &[(u32, u32); N])) {
    let mut fl = [(0u32, 0u32); N];
    let mut ls = s;
    let mut fs = s;
    let mut k = 0usize;
    let mut q = false;
    let mut bad = false;
    let mut i = s;
    loop {
        let j = next_special(buf, i, e);
        let c = if j < e { buf[j] } else { b'\n' };
        if c == b'"' {
            q = true;
            i = j + 1;
            continue;
        }
        // end of field at j
        if !bad {
            if k >= N {
                bad = true;
            } else {
                let (mut a, mut b) = (fs, j);
                if q {
                    if b - a < 2 || buf[a] != b'"' || buf[b - 1] != b'"' || buf[a + 1..b - 1].contains(&b'"') {
                        bad = true;
                    }
                    a += 1;
                    b -= 1;
                }
                fl[k] = (a as u32, b as u32);
                k += 1;
            }
        }
        q = false;
        fs = j + 1;
        if c == b'\n' {
            if !bad && k == N && !(N >= 1 && j == ls) {
                f(ls, &fl);
            }
            if j >= e {
                break;
            }
            ls = j + 1;
            k = 0;
            bad = false;
            if ls >= e {
                break;
            }
        }
        i = j + 1;
    }
}

// ---------------- time ----------------
#[inline]
fn d2(s: &[u8], i: usize) -> Option<i64> {
    let a = s[i].wrapping_sub(b'0');
    let b = s[i + 1].wrapping_sub(b'0');
    if a > 9 || b > 9 {
        return None;
    }
    Some((a * 10 + b) as i64)
}
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}
thread_local! {
    static MONTH_DAYS: Vec<i64> = {
        let mut v = Vec::with_capacity(230 * 12);
        for y in 1970..2200 { for m in 1..=12 { v.push(days_from_civil(y, m, 1)); } }
        v
    };
}
fn is_leap(y: i64) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}
#[inline]
fn parse_dt(s: &[u8]) -> Option<i64> {
    // s[0..19] = YYYY-MM-DDTHH:MM:SS
    if s[4] != b'-' || s[7] != b'-' || s[10] != b'T' || s[13] != b':' || s[16] != b':' {
        return None;
    }
    let y = d2(s, 0)? * 100 + d2(s, 2)?;
    let mo = d2(s, 5)?;
    let d = d2(s, 8)?;
    let h = d2(s, 11)?;
    let mi = d2(s, 14)?;
    let se = d2(s, 17)?;
    if !(1..=12).contains(&mo) || h > 23 || mi > 59 || se > 59 || d < 1 {
        return None;
    }
    let mdays = match mo {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        _ => {
            if is_leap(y) {
                29
            } else {
                28
            }
        }
    };
    if d > mdays {
        return None;
    }
    let days = if (1970..2200).contains(&y) {
        MONTH_DAYS.with(|t| t[((y - 1970) * 12 + mo - 1) as usize]) + d - 1
    } else {
        days_from_civil(y, mo, d)
    };
    Some(days * DAY_MS + (h * 3600 + mi * 60 + se) * 1000)
}
/// Returns None for a bad format. Out-of-range F3 returns i64::MAX (outside any window).
#[inline]
fn parse_ts(s: &[u8]) -> Option<i64> {
    let n = s.len();
    if n == 0 {
        return None;
    }
    if n == 20 && s[19] == b'Z' && s[10] == b'T' {
        return parse_dt(s);
    }
    if n == 25 && (s[19] == b'+' || s[19] == b'-') && s[10] == b'T' {
        let base = parse_dt(s)?;
        if s[22] != b':' {
            return None;
        }
        let oh = d2(s, 20)?;
        let om = d2(s, 23)?;
        if oh > 23 || om > 59 {
            return None;
        }
        let off = (oh * 60 + om) * 60_000;
        return Some(if s[19] == b'+' { base - off } else { base + off });
    }
    // F3
    let mut v: u64 = 0;
    let mut over = false;
    for &c in s {
        let d = c.wrapping_sub(b'0');
        if d > 9 {
            return None;
        }
        if !over {
            match v.checked_mul(10).and_then(|x| x.checked_add(d as u64)) {
                Some(x) => v = x,
                None => over = true,
            }
        }
    }
    if over || v > i64::MAX as u64 {
        return Some(i64::MAX);
    }
    Some(v as i64)
}

// Per-thread cache of "YYYY-MM-DDTHH" prefixes -> base ms (or invalid).
struct TsCache {
    k1: Vec<u64>,
    k2: Vec<u64>,
    v: Vec<i64>, // i64::MIN = invalid
}
const TS_BAD: i64 = i64::MIN;
impl TsCache {
    fn new() -> TsCache {
        TsCache { k1: vec![0; 4096], k2: vec![0; 4096], v: vec![0; 4096] }
    }
    #[inline(always)]
    fn base(&mut self, s: &[u8]) -> i64 {
        let a = u64::from_le_bytes(s[0..8].try_into().unwrap());
        let b = u64::from_le_bytes(s[5..13].try_into().unwrap());
        let i = ((a.wrapping_mul(0x9e3779b97f4a7c15) ^ b.wrapping_mul(0xc2b2ae3d27d4eb4f)) >> 52) as usize;
        if self.k1[i] == a && self.k2[i] == b {
            return self.v[i];
        }
        let mut tmp = [0u8; 20];
        tmp[..13].copy_from_slice(&s[..13]);
        tmp[13..].copy_from_slice(b":00:00Z");
        let v = parse_dt(&tmp).unwrap_or(TS_BAD);
        self.k1[i] = a;
        self.k2[i] = b;
        self.v[i] = v;
        v
    }
    #[inline(always)]
    fn parse(&mut self, s: &[u8]) -> Option<i64> {
        let n = s.len();
        if (n == 20 && s[19] == b'Z') || (n == 25 && (s[19] == b'+' || s[19] == b'-')) {
            if s[13] != b':' || s[16] != b':' {
                return None;
            }
            let mi = d2(s, 14)?;
            let se = d2(s, 17)?;
            if mi > 59 || se > 59 {
                return None;
            }
            let base = self.base(s);
            if base == TS_BAD {
                return None;
            }
            let t = base + (mi * 60 + se) * 1000;
            if n == 20 {
                return Some(t);
            }
            if s[22] != b':' {
                return None;
            }
            let oh = d2(s, 20)?;
            let om = d2(s, 23)?;
            if oh > 23 || om > 59 {
                return None;
            }
            let off = (oh * 60 + om) * 60_000;
            return Some(if s[19] == b'+' { t - off } else { t + off });
        }
        parse_ts(s)
    }
}

#[inline]
fn parse_price(s: &[u8]) -> u32 {
    // 0 = invalid
    if s.is_empty() {
        return 0;
    }
    let mut v: u64 = 0;
    for &c in s {
        let d = c.wrapping_sub(b'0');
        if d > 9 {
            return 0;
        }
        v = v * 10 + d as u64;
        if v > 10_000_000 {
            // keep consuming to validate digits
            for &c2 in s {
                if c2.wrapping_sub(b'0') > 9 {
                    return 0;
                }
            }
            return 0;
        }
    }
    if v >= 1 {
        v as u32
    } else {
        0
    }
}

// ---------------- records ----------------
#[derive(Clone, Copy)]
struct EvRaw {
    eid: u64,
    ingest: i64,
    person: u64,
    ts: i64,
    name: u64,
    price: u32, // >0 => purchase
    cat: u16,
    valid: bool,
}
#[derive(Clone, Copy)]
struct Ev {
    person: u64,
    ts: i64,
    name: u64,
    price: u32,
    cat: u16,
}
#[derive(Clone, Copy)]
struct Ck {
    person: u64,
    ts: i64,
    cref: u64, // click_id string ref
    camp: u32,
}


// Open-addressing map: uid hash -> (person hash, name ref). Key 0 = empty.
#[derive(Clone, Copy, Default)]
#[repr(C, align(32))]
struct Slot {
    key: u64,
    ph: u64,
    nref: u64,
    _pad: u64,
}
struct Flat {
    slots: Vec<Slot>,
    mask: usize,
}
impl Flat {
    fn new(n: usize) -> Flat {
        let cap = (n.max(16) * 2).next_power_of_two();
        Flat { slots: vec![Slot::default(); cap], mask: cap - 1 }
    }
    #[inline(always)]
    fn fix(k: u64) -> u64 {
        if k == 0 { 1 } else { k }
    }
    #[inline(always)]
    fn idx(&self, k: u64) -> usize {
        (k as usize) & self.mask
    }
    fn insert(&mut self, k: u64, ph: u64, nref: u64) {
        let k = Self::fix(k);
        let mut i = self.idx(k);
        loop {
            let s = &mut self.slots[i];
            if s.key == 0 || s.key == k {
                *s = Slot { key: k, ph, nref, _pad: 0 };
                return;
            }
            i = (i + 1) & self.mask;
        }
    }
    #[inline(always)]
    fn prefetch(&self, k: u64) {
        let i = self.idx(Self::fix(k));
        #[cfg(target_arch = "x86_64")]
        unsafe {
            std::arch::x86_64::_mm_prefetch(self.slots.as_ptr().add(i) as *const i8, std::arch::x86_64::_MM_HINT_T0);
        }
    }
    #[inline(always)]
    fn get(&self, k: u64) -> Option<(u64, u64)> {
        let k = Self::fix(k);
        let mut i = self.idx(k);
        loop {
            let s = &self.slots[i];
            if s.key == k {
                return Some((s.ph, s.nref));
            }
            if s.key == 0 {
                return None;
            }
            i = (i + 1) & self.mask;
        }
    }
}

struct Ctx {
    bufs: Vec<&'static [u8]>,
    ws: i64,
    we: i64,
    link_map: Flat,
    prod: IdMap<u16>,         // product hash -> category idx
    unknown_cat: u16,
    camps: IdMap<u32>,        // campaign hash -> idx
}

#[inline(always)]
fn resolve(ctx: &Ctx, h: u64, uref: u64) -> (u64, u64) {
    match ctx.link_map.get(h) {
        Some(x) => x,
        None => (h, uref),
    }
}

fn list_csv(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().map(|x| x == "csv").unwrap_or(false) && p.is_file())
            .collect(),
        Err(_) => vec![],
    };
    v.sort();
    v
}

/// chunks of a buffer (start,end) aligned to line starts, skipping header line.
fn chunks(buf: &[u8], target: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let mut s = memchr_nl(buf, 0);
    if s >= buf.len() {
        return out;
    }
    s += 1;
    while s < buf.len() {
        let mut e = (s + target).min(buf.len());
        if e < buf.len() {
            e = memchr_nl(buf, e);
            if e < buf.len() {
                e += 1;
            }
        }
        out.push((s, e));
        s = e;
    }
    out
}

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn madvise(addr: *mut u8, len: usize, advice: i32) -> i32;
}
/// Map a file read-only (leaked for the life of the process). Falls back to read().
fn map_file(p: &Path) -> &'static [u8] {
    use std::os::fd::AsRawFd;
    if let Ok(f) = std::fs::File::open(p) {
        let len = f.metadata().map(|m| m.len() as usize).unwrap_or(0);
        if len == 0 {
            return &[];
        }
        let ptr = unsafe { mmap(std::ptr::null_mut(), len, 1, 2, f.as_raw_fd(), 0) };
        if ptr as isize != -1 && !ptr.is_null() {
            unsafe {
                madvise(ptr, len, 2); // MADV_SEQUENTIAL
                madvise(ptr, len, 3); // MADV_WILLNEED
                return std::slice::from_raw_parts(ptr, len);
            }
        }
    }
    Box::leak(std::fs::read(p).unwrap_or_default().into_boxed_slice())
}

fn run_par<F: Fn(usize) + Sync>(nthreads: usize, njobs: usize, f: F) {
    let next = AtomicUsize::new(0);
    std::thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| loop {
                let j = next.fetch_add(1, Ordering::Relaxed);
                if j >= njobs {
                    break;
                }
                f(j);
            });
        }
    });
}

fn read_small_csv(path: &Path) -> Vec<(Vec<u8>, Vec<u8>)> {
    let buf = std::fs::read(path).unwrap_or_default();
    let mut out = Vec::new();
    let mut first = true;
    for line in buf.split(|&c| c == b'\n') {
        if first {
            first = false;
            continue;
        }
        if let Some(f) = split::<2>(line) {
            out.push((
                line[f[0].0 as usize..f[0].1 as usize].to_vec(),
                line[f[1].0 as usize..f[1].1 as usize].to_vec(),
            ));
        }
    }
    out
}

fn manifest_val(s: &str, key: &str) -> i64 {
    let k = format!("\"{}\"", key);
    let p = s.find(&k).expect("manifest key");
    let rest = &s[p + k.len()..];
    let q1 = rest.find('"').unwrap();
    let rest2 = &rest[q1 + 1..];
    let q2 = rest2.find('"').unwrap();
    parse_ts(rest2[..q2].as_bytes()).expect("manifest ts")
}

struct UserRow {
    name: u64,
    day: i32,
    sessions: i64,
    events: i64,
    revenue: i64,
    top: i32, // -1 none
}

fn main() {
    let t0 = std::time::Instant::now();
    let data = PathBuf::from(std::env::var("DATA_DIR").unwrap_or("/data".into()));
    let outdir = PathBuf::from(std::env::var("OUTPUT_DIR").unwrap_or("/output".into()));
    let nthreads: usize = std::env::var("NCPU").ok().and_then(|x| x.parse().ok()).unwrap_or_else(|| {
        std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8)
    });
    let dbg = std::env::var("DEBUG_TIMING").is_ok();
    macro_rules! tlog {
        ($($a:tt)*) => { if dbg { eprintln!("[{:>7.3}s] {}", t0.elapsed().as_secs_f64(), format!($($a)*)); } }
    }

    let man = std::fs::read_to_string(data.join("manifest.json")).expect("manifest");
    let ws = manifest_val(&man, "window_start");
    let we = manifest_val(&man, "window_end");

    // products & categories
    let prods = read_small_csv(&data.join("products.csv"));
    let mut cat_names: Vec<Vec<u8>> = Vec::new();
    let mut cat_idx: HashMap<Vec<u8>, u16> = HashMap::new();
    let mut prod: IdMap<u16> = IdMap::default();
    for (p, c) in &prods {
        let ci = *cat_idx.entry(c.clone()).or_insert_with(|| {
            cat_names.push(c.clone());
            (cat_names.len() - 1) as u16
        });
        prod.insert(h64(p), ci);
    }
    let unknown_cat = match cat_idx.get(&b"unknown"[..]) {
        Some(&i) => i,
        None => {
            cat_names.push(b"unknown".to_vec());
            (cat_names.len() - 1) as u16
        }
    };
    // rank by byte order for tie-breaks
    let mut order: Vec<usize> = (0..cat_names.len()).collect();
    order.sort_by(|&a, &b| cat_names[a].cmp(&cat_names[b]));
    let mut cat_rank = vec![0usize; cat_names.len()];
    for (r, &i) in order.iter().enumerate() {
        cat_rank[i] = r;
    }

    // campaigns
    let camp_rows = read_small_csv(&data.join("campaigns.csv"));
    let mut camps: IdMap<u32> = IdMap::default();
    let mut camp_ids: Vec<Vec<u8>> = Vec::new();
    let mut camp_ch: Vec<Vec<u8>> = Vec::new();
    for (c, ch) in &camp_rows {
        camps.insert(h64(c), camp_ids.len() as u32);
        camp_ids.push(c.clone());
        camp_ch.push(ch.clone());
    }
    let organic = camp_ids.len() as u32;
    camp_ids.push(b"organic".to_vec());
    camp_ch.push(b"organic".to_vec());
    let ncamp = camp_ids.len();

    // files
    let lf = list_csv(&data.join("links"));
    let ef = list_csv(&data.join("events"));
    let cf = list_csv(&data.join("clicks"));
    let all: Vec<PathBuf> = lf.iter().chain(ef.iter()).chain(cf.iter()).cloned().collect();
    let nl = lf.len();
    let ne = ef.len();
    // read files in parallel, largest first
    let mut sizes: Vec<(u64, usize)> = all
        .iter()
        .enumerate()
        .map(|(i, p)| (std::fs::metadata(p).map(|m| m.len()).unwrap_or(0), i))
        .collect();
    sizes.sort_by(|a, b| b.cmp(a));
    let slots: Vec<Mutex<&'static [u8]>> = (0..all.len()).map(|_| Mutex::new(&[][..])).collect();
    run_par(nthreads, sizes.len(), |j| {
        let i = sizes[j].1;
        *slots[i].lock().unwrap() = map_file(&all[i]);
    });
    let bufs: Vec<&'static [u8]> = slots.into_iter().map(|m| m.into_inner().unwrap()).collect();
    tlog!("read {} files", bufs.len());

    // ---------------- links ----------------
    let target = 8 << 20;
    let mut lchunks = Vec::new();
    for bi in 0..nl {
        for (s, e) in chunks(bufs[bi], target) {
            lchunks.push((bi, s, e));
        }
    }
    let lres: Vec<Mutex<Vec<(u64, u64, u64, u64)>>> = (0..lchunks.len()).map(|_| Mutex::new(Vec::new())).collect();
    run_par(nthreads, lchunks.len(), |j| {
        let (bi, s, e) = lchunks[j];
        let buf = bufs[bi];
        let mut v = Vec::new();
        scan::<2>(buf, s, e, |_ls, f| {
            let (a0, a1) = (f[0].0 as usize, f[0].1 as usize);
            let (b0, b1) = (f[1].0 as usize, f[1].1 as usize);
            if a1 == a0 || b1 == b0 {
                return;
            }
            let a = &buf[a0..a1];
            let b = &buf[b0..b1];
            v.push((h64(a), mkref(bi, a0, a1 - a0), h64(b), mkref(bi, b0, b1 - b0)));
        });
        *lres[j].lock().unwrap() = v;
    });
    // union find
    let mut idx: IdMap<u32> = IdMap::default();
    let mut ids: Vec<u64> = Vec::new(); // refs
    let mut hs: Vec<u64> = Vec::new();
    let mut parent: Vec<u32> = Vec::new();
    fn find(p: &mut [u32], mut x: u32) -> u32 {
        while p[x as usize] != x {
            let g = p[p[x as usize] as usize];
            p[x as usize] = g;
            x = g;
        }
        x
    }
    for m in lres {
        let v = m.into_inner().unwrap();
        for (ha, ra, hb, rb) in v {
            let ia = *idx.entry(ha).or_insert_with(|| {
                ids.push(ra);
                hs.push(ha);
                parent.push(parent.len() as u32);
                (parent.len() - 1) as u32
            });
            let ib = *idx.entry(hb).or_insert_with(|| {
                ids.push(rb);
                hs.push(hb);
                parent.push(parent.len() as u32);
                (parent.len() - 1) as u32
            });
            let ra_ = find(&mut parent, ia);
            let rb_ = find(&mut parent, ib);
            if ra_ != rb_ {
                parent[ra_ as usize] = rb_;
            }
        }
    }
    // min name per root
    let n_ids = parent.len();
    let mut best: Vec<u32> = vec![u32::MAX; n_ids];
    for i in 0..n_ids as u32 {
        let r = find(&mut parent, i) as usize;
        let b = best[r];
        if b == u32::MAX || deref(&bufs, ids[i as usize]) < deref(&bufs, ids[b as usize]) {
            best[r] = i;
        }
    }
    let mut comp_of_root: Vec<u32> = vec![u32::MAX; n_ids];
    let mut comps: Vec<(u64, u64)> = Vec::new();
    let mut link_map = Flat::new(n_ids);
    for i in 0..n_ids {
        let r = find(&mut parent, i as u32) as usize;
        if comp_of_root[r] == u32::MAX {
            let b = best[r] as usize;
            comp_of_root[r] = comps.len() as u32;
            comps.push((hs[b], ids[b]));
        }
        let c = comps[comp_of_root[r] as usize];
        link_map.insert(hs[i], c.0, c.1);
    }
    drop(idx);
    tlog!("links: {} ids, {} persons", n_ids, comps.len());

    let ctx = Ctx { bufs, ws, we, link_map, prod, unknown_cat, camps };
    let bufs = &ctx.bufs;

    // ---------------- parse events & clicks ----------------
    let mut jobs: Vec<(usize, usize, usize)> = Vec::new();
    for bi in nl..nl + ne + cf.len() {
        for (s, e) in chunks(bufs[bi], target) {
            jobs.push((bi, s, e));
        }
    }
    // biggest first is implicit-ish; fine
    let ev_bytes: usize = (nl..nl + ne).map(|i| bufs[i].len()).sum();
    let ck_bytes: usize = (nl + ne..bufs.len()).map(|i| bufs[i].len()).sum();
    let ev_res = ev_bytes / 55 / NP / nthreads * 3 / 2 + 64;
    let ck_res = ck_bytes / 40 / NP / nthreads * 3 / 2 + 64;
    let ev_parts: Vec<Mutex<Vec<Vec<EvRaw>>>> = (0..NP).map(|_| Mutex::new(Vec::new())).collect();
    let ck_parts: Vec<Mutex<Vec<Vec<Ck>>>> = (0..NP).map(|_| Mutex::new(Vec::new())).collect();
    {
        let next = AtomicUsize::new(0);
        std::thread::scope(|sc| {
            for _ in 0..nthreads {
                sc.spawn(|| {
                    let mut ep: Vec<Vec<EvRaw>> = (0..NP).map(|_| Vec::with_capacity(ev_res)).collect();
                    let mut cp: Vec<Vec<Ck>> = (0..NP).map(|_| Vec::with_capacity(ck_res)).collect();
                    let cws = ctx.ws - WEEK_MS;
                    let mut pend_e: Vec<EvRaw> = Vec::new();
                    let mut tsc = TsCache::new();
                    let mut pend_c: Vec<Ck> = Vec::new();
                    loop {
                        let j = next.fetch_add(1, Ordering::Relaxed);
                        if j >= jobs.len() {
                            break;
                        }
                        let (bi, s, e) = jobs[j];
                        let buf = bufs[bi];
                        if bi < nl + ne {
                            scan::<7>(buf, s, e, |_ls, f| {
                                let g = |k: usize| &buf[f[k].0 as usize..f[k].1 as usize];
                                let eidb = g(0);
                                if eidb.is_empty() {
                                    return;
                                }
                                let eid = h64(eidb);
                                let ingest = tsc.parse(g(3)).unwrap_or(i64::MAX);
                                let mut r = EvRaw { eid, ingest, person: 0, ts: 0, name: 0, price: 0, cat: 0, valid: false };
                                'v: {
                                    let uid = g(1);
                                    if uid.is_empty() {
                                        break 'v;
                                    }
                                    let ts = match tsc.parse(g(2)) {
                                        Some(t) if t >= ctx.ws && t < ctx.we => t,
                                        _ => break 'v,
                                    };
                                    let et = g(4);
                                    let purchase = match et {
                                        b"view" | b"cart" => false,
                                        b"purchase" => true,
                                        _ => break 'v,
                                    };
                                    let pid = g(5);
                                    if pid.is_empty() {
                                        break 'v;
                                    }
                                    if purchase {
                                        let p = parse_price(g(6));
                                        if p == 0 {
                                            break 'v;
                                        }
                                        r.price = p;
                                        r.cat = *ctx.prod.get(&h64(pid)).unwrap_or(&ctx.unknown_cat);
                                    }
                                    if ingest - ts > DAY_MS {
                                        break 'v;
                                    }
                                    let uref = mkref(bi, f[1].0 as usize, uid.len());
                                    r.person = h64(uid);
                                    r.name = uref;
                                    r.ts = ts;
                                    r.valid = true;
                                }
                                if r.valid { pend_e.push(r); } else { ep[part_of(eid)].push(r); }
                            });
                            const PD: usize = 12;
                            for q in 0..pend_e.len() {
                                if q + PD < pend_e.len() {
                                    ctx.link_map.prefetch(pend_e[q + PD].person);
                                }
                                let mut r = pend_e[q];
                                let (p, nm) = resolve(&ctx, r.person, r.name);
                                r.person = p;
                                r.name = nm;
                                ep[part_of(r.eid)].push(r);
                            }
                            pend_e.clear();
                        } else {
                            scan::<4>(buf, s, e, |_ls, f| {
                                let g = |k: usize| &buf[f[k].0 as usize..f[k].1 as usize];
                                let cid = g(0);
                                if cid.is_empty() {
                                    return;
                                }
                                let uid = g(1);
                                if uid.is_empty() {
                                    return;
                                }
                                let ts = match tsc.parse(g(3)) {
                                    Some(t) if t >= cws && t < ctx.we => t,
                                    _ => return,
                                };
                                let camp = match ctx.camps.get(&h64(g(2))) {
                                    Some(&c) => c,
                                    None => return,
                                };
                                let uref = mkref(bi, f[1].0 as usize, uid.len());
                                let _ = uref;
                                let cref = mkref(bi, f[0].0 as usize, cid.len());
                                pend_c.push(Ck { person: h64(uid), ts, cref, camp });
                            });
                            const PD: usize = 12;
                            for q in 0..pend_c.len() {
                                if q + PD < pend_c.len() {
                                    ctx.link_map.prefetch(pend_c[q + PD].person);
                                }
                                let mut c = pend_c[q];
                                c.person = resolve(&ctx, c.person, 0).0;
                                cp[part_of(c.person)].push(c);
                            }
                            pend_c.clear();
                        }
                    }
                    for (i, v) in ep.into_iter().enumerate() {
                        ev_parts[i].lock().unwrap().push(v);
                    }
                    for (i, v) in cp.into_iter().enumerate() {
                        ck_parts[i].lock().unwrap().push(v);
                    }
                });
            }
        });
    }
    tlog!("parsed");

    // ---------------- dedup events, repartition by person ----------------
    let pe_parts: Vec<Mutex<Vec<Vec<Ev>>>> = (0..NP).map(|_| Mutex::new(Vec::new())).collect();
    {
        let next = AtomicUsize::new(0);
        std::thread::scope(|sc| {
            for _ in 0..nthreads {
                sc.spawn(|| {
                    let mut out: Vec<Vec<Ev>> = (0..NP).map(|_| Vec::with_capacity(ev_res)).collect();
                    loop {
                        let j = next.fetch_add(1, Ordering::Relaxed);
                        if j >= NP {
                            break;
                        }
                        let vs = std::mem::take(&mut *ev_parts[j].lock().unwrap());
                        let total: usize = vs.iter().map(|v| v.len()).sum();
                        let mut all: Vec<EvRaw> = Vec::with_capacity(total);
                        for v in vs {
                            all.extend_from_slice(&v);
                        }
                        all.sort_unstable_by(|a, b| a.eid.cmp(&b.eid).then(a.ingest.cmp(&b.ingest)));
                        let mut i = 0;
                        while i < all.len() {
                            let r = all[i];
                            let mut k = i + 1;
                            while k < all.len() && all[k].eid == r.eid {
                                k += 1;
                            }
                            if r.valid {
                                out[part_of(r.person)].push(Ev { person: r.person, ts: r.ts, name: r.name, price: r.price, cat: r.cat });
                            }
                            i = k;
                        }
                    }
                    for (i, v) in out.into_iter().enumerate() {
                        pe_parts[i].lock().unwrap().push(v);
                    }
                });
            }
        });
    }
    drop(ev_parts);
    tlog!("dedup");

    // ---------------- sessions, attribution ----------------
    let ws_day = ctx.ws.div_euclid(DAY_MS);
    let ndays = ((ctx.we - 1).div_euclid(DAY_MS) - ws_day + 1) as usize;
    let ncat = cat_names.len();
    let camp_acc: Mutex<Vec<[i64; 4]>> = Mutex::new(vec![[0; 4]; ncamp * ndays]);
    let user_rows: Mutex<Vec<Vec<UserRow>>> = Mutex::new(Vec::new());
    {
        let next = AtomicUsize::new(0);
        std::thread::scope(|sc| {
            for _ in 0..nthreads {
                sc.spawn(|| {
                    let mut acc: Vec<[i64; 4]> = vec![[0; 4]; ncamp * ndays];
                    let mut rows: Vec<UserRow> = Vec::new();
                    let mut catsum: Vec<i64> = vec![0; ncat];
                    // per-person scratch
                    let mut s_start: Vec<i64> = Vec::new();
                    let mut s_events: Vec<i64> = Vec::new();
                    let mut s_rev: Vec<i64> = Vec::new();
                    let mut s_ev_range: Vec<(usize, usize)> = Vec::new();
                    let mut cc: Vec<(u32, i64)> = Vec::new();
                    loop {
                        let j = next.fetch_add(1, Ordering::Relaxed);
                        if j >= NP {
                            break;
                        }
                        let vs = std::mem::take(&mut *pe_parts[j].lock().unwrap());
                        let total: usize = vs.iter().map(|v| v.len()).sum();
                        let mut evs: Vec<Ev> = Vec::with_capacity(total);
                        for v in vs {
                            evs.extend_from_slice(&v);
                        }
                        evs.sort_unstable_by(|a, b| a.person.cmp(&b.person).then(a.ts.cmp(&b.ts)));
                        let cvs = std::mem::take(&mut *ck_parts[j].lock().unwrap());
                        let total: usize = cvs.iter().map(|v| v.len()).sum();
                        let mut cks: Vec<Ck> = Vec::with_capacity(total);
                        for v in cvs {
                            cks.extend_from_slice(&v);
                        }
                        cks.sort_unstable_by(|a, b| {
                            a.person
                                .cmp(&b.person)
                                .then(a.ts.cmp(&b.ts))
                                .then_with(|| deref(bufs, b.cref).cmp(deref(bufs, a.cref)))
                        });
                        // dedup identical clicks (same person, ts, click id)
                        cks.dedup_by(|b, a| a.person == b.person && a.ts == b.ts && deref(bufs, a.cref) == deref(bufs, b.cref));

                        let mut ci = 0usize;
                        let mut i = 0usize;
                        while i < evs.len() {
                            let p = evs[i].person;
                            let name = evs[i].name;
                            let mut k = i;
                            while k < evs.len() && evs[k].person == p {
                                k += 1;
                            }
                            while ci < cks.len() && cks[ci].person < p {
                                ci += 1;
                            }
                            let c0 = ci;
                            while ci < cks.len() && cks[ci].person == p {
                                ci += 1;
                            }
                            let clicks = &cks[c0..ci];
                            // sessionize
                            s_start.clear();
                            s_events.clear();
                            s_rev.clear();
                            s_ev_range.clear();
                            let mut a = i;
                            while a < k {
                                let st = evs[a].ts;
                                let mut b = a + 1;
                                let mut prev = st;
                                let mut rev = 0i64;
                                if evs[a].price > 0 {
                                    rev += evs[a].price as i64;
                                }
                                while b < k && evs[b].ts - prev <= GAP_MS {
                                    prev = evs[b].ts;
                                    rev += evs[b].price as i64;
                                    b += 1;
                                }
                                s_start.push(st);
                                s_events.push((b - a) as i64);
                                s_rev.push(rev);
                                s_ev_range.push((a, b));
                                a = b;
                            }
                            // user rows
                            let ns = s_start.len();
                            let mut x = 0;
                            while x < ns {
                                let day = s_start[x].div_euclid(DAY_MS);
                                let mut y = x;
                                let mut ne_ = 0i64;
                                let mut rv = 0i64;
                                let mut anyp = false;
                                while y < ns && s_start[y].div_euclid(DAY_MS) == day {
                                    ne_ += s_events[y];
                                    rv += s_rev[y];
                                    if s_rev[y] > 0 {
                                        anyp = true;
                                        let (ea, eb) = s_ev_range[y];
                                        for e in &evs[ea..eb] {
                                            if e.price > 0 {
                                                catsum[e.cat as usize] += e.price as i64;
                                            }
                                        }
                                    }
                                    y += 1;
                                }
                                let mut top = -1i32;
                                if anyp {
                                    let mut bv = -1i64;
                                    for c in 0..ncat {
                                        let v = catsum[c];
                                        if v > 0 && (v > bv || (v == bv && cat_rank[c] < cat_rank[top as usize])) {
                                            bv = v;
                                            top = c as i32;
                                        }
                                        catsum[c] = 0;
                                    }
                                }
                                rows.push(UserRow { name, day: day as i32, sessions: (y - x) as i64, events: ne_, revenue: rv, top });
                                x = y;
                            }
                            // credit
                            let mut cj = 0usize;
                            for x in 0..ns {
                                let s = s_start[x];
                                while cj < clicks.len() && clicks[cj].ts <= s {
                                    cj += 1;
                                }
                                let camp = if cj > 0 && s - clicks[cj - 1].ts <= WEEK_MS { clicks[cj - 1].camp } else { organic };
                                let d = (s.div_euclid(DAY_MS) - ws_day) as usize;
                                let slot = &mut acc[camp as usize * ndays + d];
                                slot[0] += 1;
                                if s_rev[x] > 0 {
                                    slot[1] += 1;
                                }
                                slot[2] += s_rev[x];
                            }
                            // assists
                            if !clicks.is_empty() && ns > 0 {
                                cc.clear();
                                cc.extend(clicks.iter().map(|c| (c.camp, c.ts)));
                                cc.sort_unstable();
                                // day boundaries over sessions
                                let first_day = s_start[0].div_euclid(DAY_MS);
                                let last_day = s_start[ns - 1].div_euclid(DAY_MS);
                                let nd = (last_day - first_day + 1) as usize;
                                // dstart[d] = first session index with day >= first_day + d
                                let mut dstart = vec![0usize; nd + 1];
                                {
                                    let mut q = 0;
                                    for d in 0..nd {
                                        let dd = first_day + d as i64;
                                        while q < ns && s_start[q].div_euclid(DAY_MS) < dd {
                                            q += 1;
                                        }
                                        dstart[d] = q;
                                    }
                                    dstart[nd] = ns;
                                }
                                let mut u = 0;
                                while u < cc.len() {
                                    let camp = cc[u].0;
                                    let mut v = u;
                                    while v < cc.len() && cc[v].0 == camp {
                                        v += 1;
                                    }
                                    // merge intervals [t, t+7d]
                                    let mut w = u;
                                    while w < v {
                                        let lo_t = cc[w].1;
                                        let mut hi_t = lo_t + WEEK_MS;
                                        let mut z = w + 1;
                                        while z < v && cc[z].1 <= hi_t {
                                            hi_t = cc[z].1 + WEEK_MS;
                                            z += 1;
                                        }
                                        // sessions with start in [lo_t, hi_t]
                                        let lo = s_start.partition_point(|&s| s < lo_t);
                                        let hi = s_start.partition_point(|&s| s <= hi_t);
                                        if lo < hi {
                                            for d in 0..nd {
                                                let a = dstart[d].max(lo);
                                                let b = dstart[d + 1].min(hi);
                                                if a < b {
                                                    let dd = (first_day + d as i64 - ws_day) as usize;
                                                    acc[camp as usize * ndays + dd][3] += (b - a) as i64;
                                                }
                                            }
                                        }
                                        w = z;
                                    }
                                    u = v;
                                }
                            }
                            i = k;
                        }
                    }
                    {
                        let mut g = camp_acc.lock().unwrap();
                        for (a, b) in g.iter_mut().zip(acc.iter()) {
                            for q in 0..4 {
                                a[q] += b[q];
                            }
                        }
                    }
                    user_rows.lock().unwrap().push(rows);
                });
            }
        });
    }
    tlog!("sessions");

    // ---------------- outputs ----------------
    let ud = outdir.join("user_daily");
    let cd = outdir.join("campaign_daily");
    std::fs::create_dir_all(&ud).unwrap();
    std::fs::create_dir_all(&cd).unwrap();
    let user_rows = user_rows.into_inner().unwrap();
    let camp_acc = camp_acc.into_inner().unwrap();
    let csv_dir = std::env::var("DEBUG_CSV_DIR").ok();
    std::thread::scope(|sc| {
        for (fi, rows) in user_rows.iter().enumerate() {
            let ud = &ud;
            let cat_names = &cat_names;
            sc.spawn(move || {
                let mut c_name = Vec::with_capacity(rows.len());
                let mut c_day = Vec::with_capacity(rows.len());
                let mut c_s = Vec::with_capacity(rows.len());
                let mut c_e = Vec::with_capacity(rows.len());
                let mut c_r = Vec::with_capacity(rows.len());
                let mut c_t = Vec::with_capacity(rows.len());
                for r in rows {
                    c_name.push(deref(bufs, r.name).to_vec());
                    c_day.push(r.day);
                    c_s.push(r.sessions);
                    c_e.push(r.events);
                    c_r.push(r.revenue);
                    c_t.push(if r.top >= 0 { Some(cat_names[r.top as usize].clone()) } else { None });
                }
                let cols = vec![
                    parquet::Col { name: "user_id", data: parquet::ColData::Str(c_name) },
                    parquet::Col { name: "day", data: parquet::ColData::Date(c_day) },
                    parquet::Col { name: "sessions", data: parquet::ColData::I64(c_s) },
                    parquet::Col { name: "events", data: parquet::ColData::I64(c_e) },
                    parquet::Col { name: "revenue_cents", data: parquet::ColData::I64(c_r) },
                    parquet::Col { name: "top_category", data: parquet::ColData::OptStr(c_t) },
                ];
                parquet::write_file(&ud.join(format!("part-{:03}.parquet", fi)), &cols).unwrap();
            });
        }
        // campaign daily
        sc.spawn(|| {
            let mut c_id = Vec::new();
            let mut c_ch = Vec::new();
            let mut c_day = Vec::new();
            let mut c_s = Vec::new();
            let mut c_p = Vec::new();
            let mut c_r = Vec::new();
            let mut c_a = Vec::new();
            for c in 0..ncamp {
                for d in 0..ndays {
                    let a = camp_acc[c * ndays + d];
                    if a[0] > 0 || a[3] > 0 {
                        c_id.push(camp_ids[c].clone());
                        c_ch.push(camp_ch[c].clone());
                        c_day.push((ws_day + d as i64) as i32);
                        c_s.push(a[0]);
                        c_p.push(a[1]);
                        c_r.push(a[2]);
                        c_a.push(a[3]);
                    }
                }
            }
            let cols = vec![
                parquet::Col { name: "campaign_id", data: parquet::ColData::Str(c_id) },
                parquet::Col { name: "channel", data: parquet::ColData::Str(c_ch) },
                parquet::Col { name: "day", data: parquet::ColData::Date(c_day) },
                parquet::Col { name: "sessions", data: parquet::ColData::I64(c_s) },
                parquet::Col { name: "purchasing_sessions", data: parquet::ColData::I64(c_p) },
                parquet::Col { name: "revenue_cents", data: parquet::ColData::I64(c_r) },
                parquet::Col { name: "assisted_sessions", data: parquet::ColData::I64(c_a) },
            ];
            parquet::write_file(&cd.join("part-000.parquet"), &cols).unwrap();
        });
    });
    if let Some(dir) = csv_dir {
        use std::io::Write;
        let dir = PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        let mut f = std::io::BufWriter::new(std::fs::File::create(dir.join("user_daily.csv")).unwrap());
        writeln!(f, "user_id,day,sessions,events,revenue_cents,top_category").unwrap();
        for rows in &user_rows {
            for r in rows {
                let top = if r.top >= 0 { String::from_utf8_lossy(&cat_names[r.top as usize]).to_string() } else { String::new() };
                writeln!(f, "{},{},{},{},{},{}", String::from_utf8_lossy(deref(bufs, r.name)), fmt_day(r.day as i64), r.sessions, r.events, r.revenue, top).unwrap();
            }
        }
        let mut f = std::io::BufWriter::new(std::fs::File::create(dir.join("campaign_daily.csv")).unwrap());
        writeln!(f, "campaign_id,channel,day,sessions,purchasing_sessions,revenue_cents,assisted_sessions").unwrap();
        for c in 0..ncamp {
            for d in 0..ndays {
                let a = camp_acc[c * ndays + d];
                if a[0] > 0 || a[3] > 0 {
                    writeln!(f, "{},{},{},{},{},{},{}", String::from_utf8_lossy(&camp_ids[c]), String::from_utf8_lossy(&camp_ch[c]), fmt_day(ws_day + d as i64), a[0], a[1], a[2], a[3]).unwrap();
                }
            }
        }
    }
    tlog!("done");
    // skip destructors
    std::process::exit(0);
}

fn fmt_day(z: i64) -> String {
    let z = z + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{:04}-{:02}-{:02}", y, m, d)
}
