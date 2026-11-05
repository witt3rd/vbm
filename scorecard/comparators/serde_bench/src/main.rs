// serde_json `Value` parse throughput on one file (MB/s, median of five 0.6 s windows). Built outside the sandbox by build.sh.
use std::time::Instant;
fn main() {
    let b = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let mut r = [0f64; 5];
    for w in 0..5 {
        let (mut it, a) = (0u64, Instant::now());
        let mut e;
        loop { let v: serde_json::Value = serde_json::from_slice(&b).unwrap(); std::hint::black_box(&v); it += 1; e = a.elapsed().as_secs_f64(); if e >= 0.6 { break; } }
        r[w] = it as f64 * b.len() as f64 / 1e6 / e;
    }
    r.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.1}", r[2]);
}
