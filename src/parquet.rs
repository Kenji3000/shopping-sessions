// Minimal Parquet writer: one row group, one PLAIN uncompressed data page per column.
use std::io::Write;

pub enum ColData {
    Str(Vec<Vec<u8>>),           // required BYTE_ARRAY (UTF8)
    OptStr(Vec<Option<Vec<u8>>>), // optional BYTE_ARRAY (UTF8)
    Date(Vec<i32>),              // required INT32 DATE
    I64(Vec<i64>),               // required INT64
}

pub struct Col {
    pub name: &'static str,
    pub data: ColData,
}

// ---------- thrift compact protocol ----------
struct T {
    b: Vec<u8>,
    last: Vec<i16>,
}
impl T {
    fn new() -> T {
        T { b: Vec::new(), last: vec![0] }
    }
    fn varint(&mut self, mut v: u64) {
        loop {
            if v < 0x80 {
                self.b.push(v as u8);
                break;
            }
            self.b.push((v as u8 & 0x7f) | 0x80);
            v >>= 7;
        }
    }
    fn zz(&mut self, v: i64) {
        self.varint(((v << 1) ^ (v >> 63)) as u64);
    }
    fn fh(&mut self, id: i16, ty: u8) {
        let last = *self.last.last().unwrap();
        let d = id - last;
        if d > 0 && d <= 15 {
            self.b.push(((d as u8) << 4) | ty);
        } else {
            self.b.push(ty);
            self.zz(id as i64);
        }
        *self.last.last_mut().unwrap() = id;
    }
    fn i32f(&mut self, id: i16, v: i32) {
        self.fh(id, 5);
        self.zz(v as i64);
    }
    fn i64f(&mut self, id: i16, v: i64) {
        self.fh(id, 6);
        self.zz(v);
    }
    fn strf(&mut self, id: i16, s: &[u8]) {
        self.fh(id, 8);
        self.varint(s.len() as u64);
        self.b.extend_from_slice(s);
    }
    fn struct_begin(&mut self, id: i16) {
        self.fh(id, 12);
        self.last.push(0);
    }
    fn struct_end(&mut self) {
        self.b.push(0);
        self.last.pop();
    }
    fn list_begin(&mut self, id: i16, elem: u8, n: usize) {
        self.fh(id, 9);
        self.list_hdr(elem, n);
    }
    fn list_hdr(&mut self, elem: u8, n: usize) {
        if n < 15 {
            self.b.push(((n as u8) << 4) | elem);
        } else {
            self.b.push(0xf0 | elem);
            self.varint(n as u64);
        }
    }
    // struct element inside a list
    fn elem_begin(&mut self) {
        self.last.push(0);
    }
    fn stop(&mut self) {
        self.b.push(0);
    }
}

fn phys(c: &ColData) -> i32 {
    match c {
        ColData::Str(_) | ColData::OptStr(_) => 6,
        ColData::Date(_) => 1,
        ColData::I64(_) => 2,
    }
}

fn nrows(c: &ColData) -> usize {
    match c {
        ColData::Str(v) => v.len(),
        ColData::OptStr(v) => v.len(),
        ColData::Date(v) => v.len(),
        ColData::I64(v) => v.len(),
    }
}

fn page_body(c: &ColData) -> Vec<u8> {
    let mut out = Vec::new();
    match c {
        ColData::Str(v) => {
            for s in v {
                out.extend_from_slice(&(s.len() as u32).to_le_bytes());
                out.extend_from_slice(s);
            }
        }
        ColData::OptStr(v) => {
            // definition levels, RLE hybrid, bit width 1, length-prefixed
            let mut lv = Vec::new();
            let mut i = 0;
            while i < v.len() {
                let cur = v[i].is_some();
                let mut j = i;
                while j < v.len() && v[j].is_some() == cur {
                    j += 1;
                }
                let mut run = (j - i) as u64;
                // RLE run header: run_len << 1
                let mut h = run << 1;
                loop {
                    if h < 0x80 {
                        lv.push(h as u8);
                        break;
                    }
                    lv.push((h as u8 & 0x7f) | 0x80);
                    h >>= 7;
                }
                lv.push(cur as u8);
                run = 0;
                let _ = run;
                i = j;
            }
            out.extend_from_slice(&(lv.len() as u32).to_le_bytes());
            out.extend_from_slice(&lv);
            for s in v.iter().flatten() {
                out.extend_from_slice(&(s.len() as u32).to_le_bytes());
                out.extend_from_slice(s);
            }
        }
        ColData::Date(v) => {
            out.reserve(v.len() * 4);
            for x in v {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        ColData::I64(v) => {
            out.reserve(v.len() * 8);
            for x in v {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
    }
    out
}

pub fn write_file(path: &std::path::Path, cols: &[Col]) -> std::io::Result<()> {
    let n = if cols.is_empty() { 0 } else { nrows(&cols[0].data) };
    let mut file: Vec<u8> = Vec::new();
    file.extend_from_slice(b"PAR1");
    struct Meta {
        offset: i64,
        size: i64,
    }
    let mut metas = Vec::new();
    for c in cols {
        let body = page_body(&c.data);
        let mut h = T::new();
        h.i32f(1, 0); // DATA_PAGE
        h.i32f(2, body.len() as i32);
        h.i32f(3, body.len() as i32);
        h.struct_begin(5);
        h.i32f(1, n as i32);
        h.i32f(2, 0); // PLAIN
        h.i32f(3, 3); // RLE
        h.i32f(4, 3); // RLE
        h.struct_end();
        h.stop();
        let off = file.len() as i64;
        file.extend_from_slice(&h.b);
        file.extend_from_slice(&body);
        metas.push(Meta { offset: off, size: (h.b.len() + body.len()) as i64 });
    }
    // footer
    let mut t = T::new();
    t.i32f(1, 1);
    t.list_begin(2, 12, cols.len() + 1);
    // root
    t.elem_begin();
    t.strf(4, b"schema");
    t.i32f(5, cols.len() as i32);
    t.struct_end();
    for c in cols {
        t.elem_begin();
        t.i32f(1, phys(&c.data));
        let rep = if matches!(c.data, ColData::OptStr(_)) { 1 } else { 0 };
        t.i32f(3, rep);
        t.strf(4, c.name.as_bytes());
        match c.data {
            ColData::Str(_) | ColData::OptStr(_) => {
                t.i32f(6, 0); // UTF8
                t.struct_begin(10);
                t.struct_begin(1); // STRING
                t.struct_end();
                t.struct_end();
            }
            ColData::Date(_) => {
                t.i32f(6, 6); // DATE
                t.struct_begin(10);
                t.struct_begin(6); // DATE
                t.struct_end();
                t.struct_end();
            }
            ColData::I64(_) => {}
        }
        t.struct_end();
    }
    t.i64f(3, n as i64);
    t.list_begin(4, 12, 1);
    t.elem_begin();
    t.list_begin(1, 12, cols.len());
    let mut total = 0i64;
    for (c, m) in cols.iter().zip(metas.iter()) {
        total += m.size;
        t.elem_begin();
        t.i64f(2, m.offset);
        t.struct_begin(3);
        t.i32f(1, phys(&c.data));
        t.list_begin(2, 5, if matches!(c.data, ColData::OptStr(_)) { 2 } else { 1 });
        t.zz(0);
        if matches!(c.data, ColData::OptStr(_)) {
            t.zz(3);
        }
        t.list_begin(3, 8, 1);
        t.varint(c.name.len() as u64);
        t.b.extend_from_slice(c.name.as_bytes());
        t.i32f(4, 0);
        t.i64f(5, n as i64);
        t.i64f(6, m.size);
        t.i64f(7, m.size);
        t.i64f(9, m.offset);
        t.struct_end();
        t.struct_end();
    }
    t.i64f(2, total);
    t.i64f(3, n as i64);
    t.struct_end();
    t.strf(6, b"sessions-rs");
    t.stop();
    file.extend_from_slice(&t.b);
    file.extend_from_slice(&(t.b.len() as u32).to_le_bytes());
    file.extend_from_slice(b"PAR1");
    let mut f = std::fs::File::create(path)?;
    f.write_all(&file)?;
    Ok(())
}
