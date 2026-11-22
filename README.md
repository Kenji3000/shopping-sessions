# Shopping Sessions (Builders Buildathon, Databricks track)

A single-binary Rust pipeline (standard library only, no dependencies) that turns the
click-stream CSVs in `$DATA_DIR` into `user_daily` and `campaign_daily` Parquet tables in
`$OUTPUT_DIR`, following `rules.md`.

How it works:
1. Read every CSV in parallel.
2. Parse links and union-find the IDs into people, each named by its byte-wise smallest ID.
3. Parse, validate and hash-partition events and clicks across all cores.
4. Dedup events by `event_id`, keeping the copy with the smallest `ingest_ts`, then repartition by person.
5. Per person: build sessions, credit each one to the latest click (ties go to the smallest
   `click_id`), and count assists with merged 7-day click intervals.
6. Write Parquet with a small built-in writer (PLAIN, uncompressed).

No third-party code or libraries are used. Licensed under MIT.
