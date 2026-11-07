# vbm-json: scorecard

**Correctness: ❌ FAIL** (2 of 3 primary dimensions measured; Trusted generation not yet defined)

**Landedness: ❌ FAIL** (below its floor: velocity.tier1_seconds_warm)

Correctness below its floor: `verified.nonstandard_axioms`

Two verdicts, no blended score. The profile (bare metal, resource efficiency) is in neither: Bare metal fail, Resource efficiency pass.

Subject: [vbm-json](https://github.com/witt3rd/vbm-json) at commit `b689b52260e5`, committed 2026-11-06T13:55:18-09:00. Scorecard `86e312b69466`, adapter `71c0554249aa`, schema `scorecard-3`.

## Correctness

### Verified: fail

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| unproved escapes | ✅ pass | 0 | == 0 |  | Counts places where a proof is skipped or faked; zero means every claim is actually proved. |
| specified share | ✅ pass | 100 | &gt;= 100 |  | How much of the code has a written, machine-checked specification. |
| nonstandard axioms | ❌ FAIL | - | == 0 |  | Counts proofs that quietly rely on assumptions beyond the usual logic; zero means none do. |
| trusted c lines | ✅ pass | 440 | tracked, not floored |  | Lines of hand-written C that must be trusted because no proof covers them; fewer is better. |
| trust ledger entries | ✅ pass | 14 | tracked, not floored |  | How many things the project openly lists as trusted without proof; fewer is better. |
| non vacuity | ✅ pass | 100 | &gt;= 100 |  | Whether the specification has teeth: deliberately broken specs should make the proofs fail. |

### Correct by construction: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| hand written tests | ✅ pass | 0 | == 0 |  | Counts test cases a person wrote by hand; zero means correctness comes from proofs and generated checks. |
| mutation score | ✅ pass | 100 | &gt;= 100 |  | Share of deliberately injected bugs that the checks catch; 100 means none slip through. |

## Landedness

### Velocity (landedness): fail

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| tier1 seconds warm | ❌ FAIL | 137.1 s (skipped 13 of 24 gates) | &lt; 60 |  | Seconds the quick check takes for a typical change once caches are warm; this is what a landing costs. |
| tier1 seconds cold | ✅ pass | 184.3 s | &lt;= 600 |  | Seconds the quick check takes on a fresh copy with no caches; this is what a newcomer pays. |
| open prs | ✅ pass | 0 | == 0 |  | How many proposed changes are waiting to be merged; zero means nothing is stuck in review. |
| commits per hour | ✅ pass | 1.767 | tracked, not floored |  | How fast changes land on the main branch, in commits per hour. |
| p90 commit to main seconds | ✅ pass | 4514 | tracked, not floored |  | How long, for 9 in 10 changes, from first authoring to landing on main. |

## Profile (in neither verdict)

### Bare metal: fail

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| freestanding build | ✅ pass | 1 | == 1 |  | Whether the code builds with no operating system or standard library underneath it. |
| wasm freestanding build | ✅ pass | 133571 B | == 1 |  | Whether the code also builds as a standalone WebAssembly module with no outside help. |
| libc symbols | ❌ FAIL | 1 | == 0 |  | Counts calls the built code makes into the C standard library; zero means fully self-contained. |

### Resource efficiency: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| throughput vs best | ✅ pass | 223.6 | &gt;= 50 | best scalar: serde_json (0.45x faster) | Speed on real data as a percent of the fastest comparable library; 50 means within twice as slow. |

## Comparison

Throughput in MB/s on the floored corpus (the floor: within 2x of the best scalar comparator; the gap to non-scalar parsers is stated, not floored).

| Implementation | MB/s |
|---|---|
| simdjson | 1559.6 |
| vbm-json (this subject) | 363.1 |
| serde_json | 162.4 |
| python-json | 103 |

Gaps to non-scalar comparators: simdjson 4.3x.

Pinned comparators: python-json 3.14.8, serde_json 1.0.150, simdjson 5.0.5.

6 of 6 corpora at or above the 50% line (the first is floored, the rest are reported).

| Corpus | KB | vbm-json | python-json | serde_json | simdjson | % of best scalar |
|---|---|---|---|---|---|---|
| scorecard-corpus | 1033 | 363.1 | 103 | 162.4 | 1559.6 | 223.6% |
| twitter | 631 | 461.8 | 276.3 | 357.3 | 4990.1 | 129.2% |
| canada | 2251 | 525.5 | 95.6 | 324.3 | 1459.7 | 162% |
| citm_catalog | 1727 | 958.4 | 333.5 | 696.8 | 5185.1 | 137.5% |
| small-objects | 2412 | 242.5 | 118.9 | 94.4 | 1473.1 | 204% |
| string-heavy | 2915 | 610.3 | 329.7 | 314.1 | 3159.9 | 185.1% |

## Trust ledger

Trusted native code: 440 lines (`abi/vbm_json.c` 107, `runtime/rt.c` 333); ledger entries: 14.

## Fast gate

Warm run 137.1 s (skipped 13 of 24 gates by design: C ABI test, wasm32 build test, freestanding native test, language bindings test, workflow lint, protected-set gate, lander, commit-on-main guard, parallel test runner, delta test selection, crash-record check, gate-diff judge, relabel-attack suite).

## Reproduce

```
mise exec -- scorecard/scorecard run --repo https://github.com/witt3rd/vbm-json --commit b689b52260e5cf116e3c472b6c2948872da3a9e2 --sandbox scorecard/sandbox-bwrap
```

Same pinned commit, same bytes out (the card carries no run timestamp).

## Links

- [One-page PDF](../../docs/cards/vbm-json-v13.pdf)
- [Raw JSON (the source this page is generated from)](witt3rd__vbm-json.json)
- Previous cards: [v12](../../docs/cards/vbm-json-v12.pdf), [v11](../../docs/cards/vbm-json-v11.pdf), [v10](../../docs/cards/vbm-json-v10.pdf), [v9](../../docs/cards/vbm-json-v9.pdf), [v8](../../docs/cards/vbm-json-v8.pdf), [v7](../../docs/cards/vbm-json-v7.pdf), [v6](../../docs/cards/vbm-json-v6.pdf), [v5](../../docs/cards/vbm-json-v5.pdf), [v4](../../docs/cards/vbm-json-v4.pdf), [v3](../../docs/cards/vbm-json-v3.pdf), [v2](../../docs/cards/vbm-json-v2.pdf), [v1](../../docs/cards/vbm-json-v1.pdf)
