// eventsource-parser throughput on one corpus file at one chunk size: `node bench.mjs FILE CHUNK` prints `MB/S events E` (fastest of nine timed runs after three warm-up runs; MB = 10^6 bytes).
// The file is cut into string chunks before the clock starts (the corpus is ASCII, so a cut at any byte is a cut at a character); the parser's `feed` takes text.
import { readFileSync } from 'node:fs'
import { createParser } from 'eventsource-parser'
const [file, chunkArg] = process.argv.slice(2)
const chunk = Number(chunkArg)
const text = readFileSync(file, 'latin1')
const chunks = []
for (let i = 0; i < text.length; i += chunk) chunks.push(text.slice(i, i + chunk))
let best = Infinity, events = 0
for (let rep = 0; rep < 12; rep++) {   // the first three runs let the JIT settle (a steady state is what a long-lived consumer sees); the fastest of the rest is reported
  let n = 0
  const parser = createParser({ onEvent: () => { n++ } })
  const t0 = process.hrtime.bigint()
  for (const c of chunks) parser.feed(c)
  const dt = Number(process.hrtime.bigint() - t0) / 1e9
  if (rep >= 3 && dt < best) best = dt
  events = n
}
console.log(`${(text.length / 1e6 / best).toFixed(1)} events ${events}`)
