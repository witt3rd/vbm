# vbm-sse: scorecard

**Correctness: ✅ PASS** (3 of 4 primary dimensions measured; Trusted generation not yet defined)

**Landedness: ✅ PASS**

Two verdicts, no blended score. The profile (bare metal, resource efficiency) is in neither: Bare metal pass, Resource efficiency pass.

Subject: [vbm-sse](https://github.com/witt3rd/vbm-sse) at commit `1829fc470376`, committed 2026-11-06T01:03:46-09:00. Scorecard `a4bdb39580e0`, adapter `520db9a1849a`, schema `scorecard-3`.

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

### Process honesty: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| gate selftests | ✅ pass | 100 | &gt;= 100 |  | Share of the project's checks that have a test proving the check can fail. |
| gates self tested | ✅ pass | 100 | &gt;= 100 |  | Share of the project's checks whose can-it-fail test actually ran in this measurement. |
| selftests ran cases | ✅ pass | 2315 | &gt;= 1 |  | Whether the project's checks reported how many cases they ran, and ran at least one, with none skipped. |
| attack suite | ✅ pass | 1 | == 1 |  | Whether an attempt to cheat the checks is caught, and a sabotaged run is correctly reported as failing. |

## Landedness

### Velocity (landedness): pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| tier1 seconds warm | ✅ pass | 29.5 s (skipped 14 of 24 gates) | &lt; 60 |  | Seconds the quick check takes for a typical change once caches are warm; this is what a landing costs. |
| tier1 seconds cold | ✅ pass | 131.5 s | &lt;= 600 |  | Seconds the quick check takes on a fresh copy with no caches; this is what a newcomer pays. |
| open prs | ✅ pass | 0 | == 0 |  | How many proposed changes are waiting to be merged; zero means nothing is stuck in review. |
| commits per hour | ✅ pass | 3.139 | tracked, not floored |  | How fast changes land on the main branch, in commits per hour. |
| p90 commit to main seconds | ✅ pass | 7475 | tracked, not floored |  | How long, for 9 in 10 changes, from first authoring to landing on main. |

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
| throughput vs best | ✅ pass | 55.1 | &gt;= 50 | best scalar: eventsource-parser (1.81x faster) | Speed on real data as a percent of the fastest comparable library; 50 means within twice as slow. |

## Comparison

Throughput in MB/s on the floored corpus (the floor: within 2x of the best scalar comparator; the gap to non-scalar parsers is stated, not floored).

| Implementation | MB/s |
|---|---|
| eventsource-parser | 2553.2 |
| vbm-sse (this subject) | 1408 |
| eventsource-stream | 390.7 |



Pinned comparators: eventsource-parser 4.1.3, eventsource-stream 0.2.3.

15 of 15 corpora at or above the 50% line (the first is floored, the rest are reported).

| Corpus | KB | vbm-sse | eventsource-parser | eventsource-stream | lean-fast | reference | % of best scalar |
|---|---|---|---|---|---|---|---|
| small-events@1 | 3616 | 24.4 | 29.3 | 12.2 | 62.2 | 24.1 | 83.3% |
| small-events@7 | 3616 | 120.8 | 161.9 | 68.6 | 226 | 24.1 | 74.6% |
| small-events@4096 | 3616 | 1408 | 2553.2 | 390.7 | 1863.7 | 24.1 | 55.1% |
| large-data@1 | 1500 | 26.2 | 29.9 | 0.3 | 66.7 | 22.6 | 87.6% |
| large-data@7 | 1500 | 159.9 | 197.8 | 2 | 324.3 | 22.6 | 80.8% |
| large-data@4096 | 1500 | 2458.5 | 2880.6 | 461.3 | 3389 | 22.6 | 85.3% |
| ends-crlf@1 | 3681 | 24.8 | 30 | 12.3 | 63.6 | 23.9 | 82.7% |
| ends-crlf@7 | 3681 | 121.5 | 157.3 | 69.1 | 219.6 | 23.9 | 77.2% |
| ends-crlf@4096 | 3681 | 1263.3 | 1388.4 | 392.7 | 1597.7 | 23.9 | 91% |
| ends-cr@1 | 3616 | 24.1 | 28.7 | 11.8 | 61.9 | 23.5 | 84% |
| ends-cr@7 | 3616 | 120.5 | 155.1 | 68.7 | 223.1 | 23.5 | 77.7% |
| ends-cr@4096 | 3616 | 1371.9 | 1717.4 | 381.9 | 1858.4 | 23.5 | 79.9% |
| ends-mixed@1 | 3638 | 24.6 | 29.3 | 12 | 62.9 | 23.7 | 84% |
| ends-mixed@7 | 3638 | 120.1 | 152.4 | 65.5 | 217.6 | 23.7 | 78.8% |
| ends-mixed@4096 | 3638 | 1206.2 | 1161.5 | 365.9 | 1498.7 | 23.7 | 103.8% |

## Trust ledger

Trusted native code: 464 lines (`abi/vbm_sse.c` 82, `runtime/rt.c` 382); ledger entries: 13.

## Fast gate

Warm run 29.5 s (skipped 14 of 24 gates by design: vectors check, C ABI description check, freestanding native test, wasm32 build test, language bindings test, workflow lint, protected-set gate, lander, commit-on-main guard, parallel test runner, delta test selection, crash-record check, gate-diff judge, relabel-attack suite).

## Reproduce

```
mise exec -- scorecard/scorecard run --repo https://github.com/witt3rd/vbm-sse --commit 1829fc470376e5d6c25d4e29c8dedb7c8a5eeed9 --sandbox scorecard/sandbox-bwrap
```

Same pinned commit, same bytes out (the card carries no run timestamp).

## Links

- [One-page PDF](../../docs/cards/vbm-sse-v1.pdf)
- [Raw JSON (the source this page is generated from)](witt3rd__vbm-sse.json)
- Previous cards: none
