// eventsource-stream throughput on one corpus file at one chunk size: `sse_rs FILE CHUNK` prints `MB/S events E` (fastest of five runs; MB = 10^6 bytes).
// The file is cut into `Bytes` chunks before the clock starts; the stream of chunks is driven by a single-threaded executor (futures::executor::block_on).
use bytes::Bytes;
use eventsource_stream::Eventsource;
use futures::{executor::block_on, stream, StreamExt};
use std::convert::Infallible;
use std::time::Instant;

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let data = Bytes::from(std::fs::read(&a[0]).unwrap());
    let chunk: usize = a[1].parse().unwrap();
    let chunks: Vec<Bytes> = (0..data.len()).step_by(chunk).map(|i| data.slice(i..(i + chunk).min(data.len()))).collect();
    let (mut best, mut events) = (f64::INFINITY, 0u64);
    for _ in 0..5 {
        let input = stream::iter(chunks.clone().into_iter().map(Ok::<Bytes, Infallible>));
        let t0 = Instant::now();
        let n = block_on(async { let mut s = input.eventsource(); let mut n = 0u64; while let Some(e) = s.next().await { e.unwrap(); n += 1; } n });
        let dt = t0.elapsed().as_secs_f64();
        if dt < best { best = dt; }
        events = n;
    }
    println!("{:.1} events {}", data.len() as f64 / 1e6 / best, events);
}
