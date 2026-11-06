# vbm-json: scorecard

**Correctness: ✅ PASS** (3 of 4 primary dimensions measured; Trusted generation not yet defined)

**Landedness: ✅ PASS**

Two verdicts, no blended score. The profile (bare metal, resource efficiency) is in neither: Bare metal pass, Resource efficiency pass.

Subject: [vbm-json](https://github.com/witt3rd/vbm-json) at commit `3685dc1dc3fb`, committed 2026-11-05T23:21:38-08:00. Scorecard `a4bdb39580e0`, adapter `71c0554249aa`, schema `scorecard-3`.

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
| selftests ran cases | ✅ pass | 25556 | &gt;= 1 |  | Whether the project's checks reported how many cases they ran, and ran at least one, with none skipped. |
| attack suite | ✅ pass | 1 | == 1 |  | Whether an attempt to cheat the checks is caught, and a sabotaged run is correctly reported as failing. |

## Landedness

### Velocity (landedness): pass

| Metric | Status | Value | Floor | Comparator | Meaning |
|---|---|---|---|---|---|
| tier1 seconds warm | ✅ pass | 30.6 s (skipped 13 of 24 gates) | &lt; 60 |  | Seconds the quick check takes for a typical change once caches are warm; this is what a landing costs. |
| tier1 seconds cold | ✅ pass | 285.9 s | &lt;= 600 |  | Seconds the quick check takes on a fresh copy with no caches; this is what a newcomer pays. |
| open prs | ✅ pass | 0 | == 0 |  | How many proposed changes are waiting to be merged; zero means nothing is stuck in review. |
| commits per hour | ✅ pass | 1.834 | tracked, not floored |  | How fast changes land on the main branch, in commits per hour. |
| p90 commit to main seconds | ✅ pass | 7373 | tracked, not floored |  | How long, for 9 in 10 changes, from first authoring to landing on main. |

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
| throughput vs best | ✅ pass | 80.8 | &gt;= 50 | best scalar: serde_json (1.24x faster) | Speed on real data as a percent of the fastest comparable library; 50 means within twice as slow. |

## Comparison

Throughput in MB/s on the floored corpus (the floor: within 2x of the best scalar comparator; the gap to non-scalar parsers is stated, not floored).

| Implementation | MB/s |
|---|---|
| simdjson | 676.2 |
| serde_json | 143.3 |
| vbm-json (this subject) | 115.8 |
| python-json | 91.3 |

Gaps to non-scalar comparators: simdjson 5.8x.

Pinned comparators: python-json 3.14.8, serde_json 1.0.150, simdjson 5.0.5.

4 of 6 corpora at or above the 50% line (the first is floored, the rest are reported).

| Corpus | KB | vbm-json | python-json | serde_json | simdjson | % of best scalar |
|---|---|---|---|---|---|---|
| scorecard-corpus | 1033 | 115.8 | 91.3 | 143.3 | 676.2 | 80.8% |
| twitter | 631 | 77.6 | 109.6 | 112.3 | 1367.5 | 69.1% |
| canada | 2251 | 54 | 29.7 | 127.4 | 452.5 | 42.4% |
| citm_catalog | 1727 | 151.9 | 189.1 | 306.8 | 2246.3 | 49.5% |
| small-objects | 2412 | 54.2 | 82.1 | 63.9 | 1008.2 | 66% |
| string-heavy | 2915 | 214.8 | 249.5 | 209.7 | 2304.6 | 86.1% |

## Trust ledger

Trusted native code: 430 lines (`abi/vbm_json.c` 107, `runtime/rt.c` 323); ledger entries: 13.

## Fast gate

Warm run 30.6 s (skipped 13 of 24 gates by design: C ABI test, wasm32 build test, freestanding native test, language bindings test, workflow lint, protected-set gate, lander, commit-on-main guard, parallel test runner, delta test selection, crash-record check, gate-diff judge, relabel-attack suite).

## Reproduce

```
mise exec -- scorecard/scorecard run --repo https://github.com/witt3rd/vbm-json --commit 3685dc1dc3fb5a494669030a4da3ddb0d56479a1 --sandbox scorecard/sandbox-bwrap
```

Same pinned commit, same bytes out (the card carries no run timestamp).

## Links

- [One-page PDF](../../docs/cards/vbm-json-v12.pdf)
- [Raw JSON (the source this page is generated from)](witt3rd__vbm-json.json)
- Previous cards: [v11](../../docs/cards/vbm-json-v11.pdf), [v10](../../docs/cards/vbm-json-v10.pdf), [v9](../../docs/cards/vbm-json-v9.pdf), [v8](../../docs/cards/vbm-json-v8.pdf), [v7](../../docs/cards/vbm-json-v7.pdf), [v6](../../docs/cards/vbm-json-v6.pdf), [v5](../../docs/cards/vbm-json-v5.pdf), [v4](../../docs/cards/vbm-json-v4.pdf), [v3](../../docs/cards/vbm-json-v3.pdf), [v2](../../docs/cards/vbm-json-v2.pdf), [v1](../../docs/cards/vbm-json-v1.pdf)
