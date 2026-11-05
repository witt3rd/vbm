# vbm-json: scorecard

**Correctness: ✅ PASS** (3 of 4 primary dimensions measured; Trusted generation not yet defined)

**Landedness: ❌ FAIL** (below its floor: velocity.tier1_seconds_warm)

*Scored before the honesty check (ran-evidence): Process honesty here does not include it.*

Two verdicts, no blended score. The profile (bare metal, resource efficiency) is in neither: Bare metal pass, Resource efficiency pass.

Subject: [vbm-json](https://github.com/witt3rd/vbm-json) at commit `0a6696caa7c2`, committed 2026-11-05T03:06:01-08:00. Scorecard `01ae90b1de09`, adapter `b6ba23ff3ae9`, schema `scorecard-3`.

## Correctness

### Verified: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| unproved escapes | ✅ pass | 0 | == 0 |  | Counts places where a proof is skipped or faked; zero means every claim is actually proved. |
| specified share | ✅ pass | 100 | &gt;= 100 |  | How much of the code has a written, machine-checked specification. |
| nonstandard axioms | ✅ pass | 0 | == 0 |  | Counts proofs that quietly rely on assumptions beyond the usual logic; zero means none do. |
| trusted c lines | ✅ pass | 430 | tracked, not floored |  | Lines of hand-written C that must be trusted because no proof covers them; fewer is better. |
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
| attack suite | ✅ pass | 1 | == 1 |  | Whether an attempt to cheat the checks is caught, and a sabotaged run is correctly reported as failing. |

## Landedness

### Velocity (landedness): fail

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| tier1 seconds warm | ❌ FAIL | 91.2 s (skipped 13 of 24 gates) | &lt; 60 |  | Seconds the quick check takes for a typical change once caches are warm; this is what a landing costs. |
| tier1 seconds cold | ✅ pass | 300.6 s | &lt;= 600 |  | Seconds the quick check takes on a fresh copy with no caches; this is what a newcomer pays. |
| open prs | ✅ pass | 0 | == 0 |  | How many proposed changes are waiting to be merged; zero means nothing is stuck in review. |
| commits per hour | ✅ pass | 4.301 | tracked, not floored |  | How fast changes land on the main branch, in commits per hour. |
| p90 commit to main seconds | ✅ pass | 1301 | tracked, not floored |  | How long, for 9 in 10 changes, from first authoring to landing on main. |

## Profile (in neither verdict)

### Bare metal: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| freestanding build | ✅ pass | 1 | == 1 |  | Whether the code builds with no operating system or standard library underneath it. |
| wasm freestanding build | ✅ pass | 54230 B | == 1 |  | Whether the code also builds as a standalone WebAssembly module with no outside help. |
| libc symbols | ✅ pass | 0 | == 0 |  | Counts calls the built code makes into the C standard library; zero means fully self-contained. |

### Resource efficiency: pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| throughput vs best | ✅ pass | 71.2 | &gt;= 50 | best scalar: serde_json (1.4x faster) | Speed on real data as a percent of the fastest comparable library; 50 means within twice as slow. |

## Comparison

Throughput in MB/s on the floored corpus (the floor: within 2x of the best scalar comparator; the gap to non-scalar parsers is stated, not floored).

| Implementation | MB/s |
|---|---|
| simdjson | 374.8 |
| serde_json | 36.8 |
| vbm-json (this subject) | 26.2 |
| python-json | 23 |

Gaps to non-scalar comparators: simdjson 14.3x.

Pinned comparators: python-json 3.14.8, serde_json 1.0.150, simdjson 5.0.5.

4 of 6 corpora at or above the 50% line (the first is floored, the rest are reported).

| Corpus | KB | vbm-json | python-json | serde_json | simdjson | % of best scalar |
|---|---|---|---|---|---|---|
| scorecard-corpus | 1033 | 26.2 | 23 | 36.8 | 374.8 | 71.2% |
| twitter | 631 | 45 | 58.7 | 83.4 | 1231.9 | 54% |
| canada | 2251 | 33.7 | 23.6 | 91.2 | 362.9 | 37% |
| citm_catalog | 1727 | 64.6 | 65.4 | 147 | 1233.7 | 43.9% |
| small-objects | 2412 | 21 | 27.3 | 29.1 | 541.8 | 72.2% |
| string-heavy | 2915 | 117.6 | 146.2 | 161 | 1712.6 | 73% |

## Trust ledger

Trusted native code: 430 lines (`abi/vbm_json.c` 107, `runtime/rt.c` 323); ledger entries: 13.

## Fast gate

Warm run 91.2 s (skipped 13 of 24 gates by design: C ABI test, wasm32 build test, freestanding native test, language bindings test, workflow lint, protected-set gate, lander, commit-on-main guard, parallel test runner, delta test selection, crash-record check, gate-diff judge, relabel-attack suite).

## Reproduce

```
mise exec -- scorecard/scorecard run --repo https://github.com/witt3rd/vbm-json --commit 0a6696caa7c2eee79b6c323a900c51405193a392 --sandbox scorecard/sandbox-bwrap
```

Same pinned commit, same bytes out (the card carries no run timestamp).

## Links

- [One-page PDF](../../docs/cards/vbm-json-v9.pdf)
- [Raw JSON (the source this page is generated from)](witt3rd__vbm-json.json)
- Previous cards: [v8](../../docs/cards/vbm-json-v8.pdf), [v7](../../docs/cards/vbm-json-v7.pdf), [v6](../../docs/cards/vbm-json-v6.pdf), [v5](../../docs/cards/vbm-json-v5.pdf), [v4](../../docs/cards/vbm-json-v4.pdf), [v3](../../docs/cards/vbm-json-v3.pdf), [v2](../../docs/cards/vbm-json-v2.pdf), [v1](../../docs/cards/vbm-json-v1.pdf)
