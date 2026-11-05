---
title: vbm-json: scorecard (sandboxed run)
subtitle: Subject commit 3dbd0175ddf0, scorecard fcf60f18fbfe, adapter f50070f5c2b7
kicker: Scorecard · one card
footer: vbm-json-v6 · subject 3dbd0175ddf0 committed 2026-11-04 12:59 -0800, 9 min before this card
---

**Strict result: FAIL**. 11 metrics pass, 5 fail, 3 are not measurable. Failing dimensions: Bare metal, By construction, Efficiency, Velocity, Honesty. Subject commands ran in the sandbox only.

| Dimension | Metric | Status | Value | Floor |
|---|---|---|---|---|
| Verified | unproved escapes | pass | 0 | == 0 |
| Verified | specified share | pass | 100 | >= 100 |
| Verified | nonstandard axioms | pass | 0 | == 0 |
| Verified | trusted c lines | pass | 350 | tracked |
| Verified | trust ledger entries | pass | 13 | tracked |
| Verified | non vacuity | pass | 100 | >= 100 |
| Bare metal | freestanding build | **FAIL** | 0 | == 1 |
| Bare metal | wasm freestanding build | pass | 60745 B | == 1 |
| Bare metal | libc symbols | **FAIL** | 5 | == 0 |
| By construction | hand written tests | **FAIL** | 11 | == 0 |
| By construction | mutation score | **FAIL** | 61.3 | >= 100 |
| Efficiency | throughput vs best | not measurable (1) | - | >= 80 |
| Velocity | tier1 seconds | **FAIL** | 71.4 | < 60 |
| Velocity | open prs | pass | 0 | == 0 |
| Velocity | commits per hour | pass | 1.737 | tracked |
| Velocity | p90 commit to main seconds | pass | 565 | tracked |
| Honesty | gate selftests | pass | 100 | >= 100 |
| Honesty | gates self tested | not measurable (2) | - | >= 100 |
| Honesty | attack suite | not measurable (2) | - | == 1 |

**Not measurable, and why.** (1) required comparators did not report: simdjson, serde_json (partial numbers: subject 53.5 MB/s, python-json 121.3). (2) not implemented in this runner version.

**Notes.** Libc symbols the artifact needs (5): `free`, `malloc`, `memcpy`, `memset`, `pthread_once`. Hand-written cases (11): `bindings/rust/tests/vectors.rs` 3, `tests/abi_test.c` 1, `tests/bindings/test_python.py` 4, `tests/wasm/wasm_test.mjs` 3. Drivers, 0 cases, not counted: `tests/abi_dump.c`, `tests/wasm/vbm_json.mjs`. Fast gate timed: `scripts/tier1.sh`, cold, 2 CPUs.
