---
title: vbm-json: scorecard (sandboxed run)
subtitle: Subject commit f1f585c8c5e2, scorecard 9e10e7f65d34, adapter 9210be3088f5
kicker: Scorecard · one card
footer: vbm-json-v4 · subject f1f585c8c5e2 committed 2026-11-04 11:56 -0800, 10 min before this card
---

**Strict result: FAIL** (measurable metrics alone: FAIL). 8 metrics pass, 5 fail, 6 are not measurable. Failing dimensions: Verified, Bare metal, By construction, Efficiency, Velocity, Honesty. Subject commands ran only inside the sandbox (attestations are in the card).

| Dimension | Metric | Status | Value | Floor |
|---|---|---|---|---|
| Verified | unproved escapes | pass | 0 | == 0 |
| Verified | specified share | pass | 100 | >= 100 |
| Verified | nonstandard axioms | pass | 0 | == 0 |
| Verified | trusted c lines | pass | 350 | tracked |
| Verified | trust ledger entries | pass | 11 | tracked |
| Verified | non vacuity | not measurable (2) | - | >= 100 |
| Bare metal | freestanding build | **FAIL** | 0 | == 1 |
| Bare metal | wasm freestanding build | pass | 60745 B | == 1 |
| Bare metal | libc symbols | **FAIL** | 5 | == 0 |
| By construction | hand written tests | **FAIL** | 4 | == 0 |
| By construction | mutation score | not measurable (2) | - | >= 100 |
| Efficiency | throughput vs best | not measurable (2) | - | >= 80 |
| Velocity | tier1 seconds | **FAIL** | 66 | < 60 |
| Velocity | open prs | **FAIL** | 1 | == 0 |
| Velocity | commits per hour | pass | 1.625 | tracked |
| Velocity | p90 commit to main seconds | not measurable (1) | - | tracked |
| Honesty | gate selftests | pass | 100 | >= 100 |
| Honesty | gates self tested | not measurable (2) | - | >= 100 |
| Honesty | attack suite | not measurable (2) | - | == 1 |

**Not measurable, and why.** (1) the change's first authored commit is not recorded on main (rebase and squash rewrite the dates, which read 0 under direct landing). (2) not implemented in this runner version.

**Notes.** Libc symbols the artifact needs (5): `free`, `malloc`, `memcpy`, `memset`, `pthread_once`. The 4 hand-written tests of the subject's code and the 6 gate self-test files are listed in the card.
