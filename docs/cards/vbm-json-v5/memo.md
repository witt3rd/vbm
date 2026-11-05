---
title: vbm-json: scorecard (sandboxed run)
subtitle: Subject commit 3d95e74f1f40, scorecard 00a9fde54c25, adapter 0726805cf097
kicker: Scorecard · one card
footer: vbm-json-v5 · subject 3d95e74f1f40 committed 2026-11-04 12:06 -0800, 44 min before this card
---

**Strict result: FAIL** (measurable metrics alone: FAIL). 11 metrics pass, 5 fail, 3 are not measurable. Failing dimensions: Bare metal, By construction, Efficiency, Velocity, Honesty. Subject commands ran only inside the sandbox (attestations are in the card).

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
| By construction | hand written tests | **FAIL** | 6 | == 0 |
| By construction | mutation score | **FAIL** | 61.3 | >= 100 |
| Efficiency | throughput vs best | not measurable (1) | - | >= 80 |
| Velocity | tier1 seconds | **FAIL** | 69.6 | < 60 |
| Velocity | open prs | pass | 0 | == 0 |
| Velocity | commits per hour | pass | 1.788 | tracked |
| Velocity | p90 commit to main seconds | pass | 565 | tracked |
| Honesty | gate selftests | pass | 100 | >= 100 |
| Honesty | gates self tested | not measurable (2) | - | >= 100 |
| Honesty | attack suite | not measurable (2) | - | == 1 |

**Not measurable, and why.** (1) required comparators did not report: simdjson, serde_json (partial numbers: subject 54.8 MB/s, python-json 129.4). (2) not implemented in this runner version.

**Notes.** Libc symbols the artifact needs (5): `free`, `malloc`, `memcpy`, `memset`, `pthread_once`. The 6 hand-written tests of the subject's code and the 7 gate self-test files are listed in the card.
