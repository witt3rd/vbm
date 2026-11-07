# vbm-sse: scorecard

**Correctness: ✅ PASS** (2 of 3 primary dimensions measured; Trusted generation not yet defined)

**Landedness: ✅ PASS**

Two verdicts, no blended score. The profile (bare metal, resource efficiency) is in neither: Bare metal pass, Resource efficiency pass.

Subject: [vbm-sse](https://github.com/witt3rd/vbm-sse) at commit `c19cfe96d197`, committed 2026-11-06T13:56:43-09:00. Scorecard `86e312b69466`, adapter `520db9a1849a`, schema `scorecard-3`.

## Correctness

### Verified: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| unproved escapes | ✅ pass | 0 | == 0 |  | Counts places where a proof is skipped or faked; zero means every claim is actually proved. |
| specified share | ✅ pass | 100 | &gt;= 100 |  | How much of the code has a written, machine-checked specification. |
| nonstandard axioms | ✅ pass | 0 | == 0 |  | Counts proofs that quietly rely on assumptions beyond the usual logic; zero means none do. |
| trusted c lines | ✅ pass | 464 | tracked, not floored |  | Lines of hand-written C that must be trusted because no proof covers them; fewer is better. |
| trust ledger entries | ✅ pass | 13 | tracked, not floored |  | How many things the project openly lists as trusted without proof; fewer is better. |
| non vacuity | ✅ pass | 100 | &gt;= 100 |  | Whether the specification has teeth: deliberately broken specs should make the proofs fail. |

### Correct by construction: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| hand written tests | ✅ pass | 0 | == 0 |  | Counts test cases a person wrote by hand; zero means correctness comes from proofs and generated checks. |
| mutation score | ✅ pass | 100 | &gt;= 100 |  | Share of deliberately injected bugs that the checks catch; 100 means none slip through. |

## Landedness

### Velocity (landedness): pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| tier1 seconds warm | ✅ pass | 54.4 s (skipped 14 of 24 gates) | &lt; 60 |  | Seconds the quick check takes for a typical change once caches are warm; this is what a landing costs. |
| tier1 seconds cold | ✅ pass | 67.6 s | &lt;= 600 |  | Seconds the quick check takes on a fresh copy with no caches; this is what a newcomer pays. |
| open prs | ✅ pass | 0 | == 0 |  | How many proposed changes are waiting to be merged; zero means nothing is stuck in review. |
| commits per hour | ✅ pass | 2.274 | tracked, not floored |  | How fast changes land on the main branch, in commits per hour. |
| p90 commit to main seconds | ✅ pass | 4744 | tracked, not floored |  | How long, for 9 in 10 changes, from first authoring to landing on main. |

## Profile (in neither verdict)

### Bare metal: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| freestanding build | ✅ pass | 1 | == 1 |  | Whether the code builds with no operating system or standard library underneath it. |
| wasm freestanding build | ✅ pass | 46526 B | == 1 |  | Whether the code also builds as a standalone WebAssembly module with no outside help. |
| libc symbols | ✅ pass | 0 | == 0 |  | Counts calls the built code makes into the C standard library; zero means fully self-contained. |

### Resource efficiency: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| throughput vs best | ✅ pass | 56.3 | &gt;= 50 | best scalar: eventsource-parser (1.78x faster) | Speed on real data as a percent of the fastest comparable library; 50 means within twice as slow. |

## Comparison

Throughput in MB/s on the floored corpus (the floor: within 2x of the best scalar comparator; the gap to non-scalar parsers is stated, not floored).

| Implementation | MB/s |
|---|---|
| eventsource-parser | 2230.2 |
| vbm-sse (this subject) | 1255.8 |
| eventsource-stream | 349.7 |



Pinned comparators: eventsource-parser 4.1.3, eventsource-stream 0.2.3.

15 of 15 corpora at or above the 50% line (the first is floored, the rest are reported).

| Corpus | KB | vbm-sse | eventsource-parser | eventsource-stream | lean-fast | reference | % of best scalar |
|---|---|---|---|---|---|---|---|
| small-events@1 | 3616 | 26 | 30 | 12.1 | 62.6 | 26.6 | 86.7% |
| small-events@7 | 3616 | 120.5 | 166.9 | 69.8 | 220 | 26.6 | 72.2% |
| small-events@4096 | 3616 | 1255.8 | 2230.2 | 349.7 | 1846.9 | 26.6 | 56.3% |
| large-data@1 | 1500 | 28 | 32.8 | 0.3 | 61.7 | 22.6 | 85.4% |
| large-data@7 | 1500 | 154.6 | 210.8 | 2 | 297.9 | 22.6 | 73.3% |
| large-data@4096 | 1500 | 2416 | 2448.3 | 471.2 | 2989.7 | 22.6 | 98.7% |
| ends-crlf@1 | 3681 | 25.9 | 30.1 | 12 | 64 | 25 | 86% |
| ends-crlf@7 | 3681 | 118.7 | 156 | 69.3 | 212.5 | 25 | 76.1% |
| ends-crlf@4096 | 3681 | 1240.9 | 1469.4 | 398.6 | 1628 | 25 | 84.4% |
| ends-cr@1 | 3616 | 25.9 | 29.9 | 11.9 | 62.7 | 25.7 | 86.6% |
| ends-cr@7 | 3616 | 119.9 | 155.4 | 68.9 | 219 | 25.7 | 77.2% |
| ends-cr@4096 | 3616 | 1334.9 | 1777.8 | 389 | 1836.2 | 25.7 | 75.1% |
| ends-mixed@1 | 3638 | 25.9 | 30 | 11.8 | 62.9 | 25.6 | 86.3% |
| ends-mixed@7 | 3638 | 118.1 | 156.1 | 66.7 | 211.7 | 25.6 | 75.7% |
| ends-mixed@4096 | 3638 | 1166.7 | 1277.5 | 372.6 | 1527.6 | 25.6 | 91.3% |

## Trust ledger

Trusted native code: 464 lines (`abi/vbm_sse.c` 82, `runtime/rt.c` 382); ledger entries: 13.

## Fast gate

Warm run 54.4 s (skipped 14 of 24 gates by design: vectors check, C ABI description check, freestanding native test, wasm32 build test, language bindings test, workflow lint, protected-set gate, lander, commit-on-main guard, parallel test runner, delta test selection, crash-record check, gate-diff judge, relabel-attack suite).

## Reproduce

```
mise exec -- scorecard/scorecard run --repo https://github.com/witt3rd/vbm-sse --commit c19cfe96d19787b7dfdcd47b39db97c1ae27917f --sandbox scorecard/sandbox-bwrap
```

Same pinned commit, same bytes out (the card carries no run timestamp).

## Links

- [One-page PDF](../../docs/cards/vbm-sse-v2.pdf)
- [Raw JSON (the source this page is generated from)](witt3rd__vbm-sse.json)
- Previous cards: [v1](../../docs/cards/vbm-sse-v1.pdf)
