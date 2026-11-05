---
title: vbm-json: scorecard (sandboxed run)
subtitle: Subject commit 6b239dea3bf9, scorecard 9dbe735d44cd, adapter a74bb4ad6523
kicker: Scorecard · one card
footer: vbm-json-v3
---

**Strict result: FAIL.** Implemented-and-measurable result: FAIL. 9 metrics pass, 3 fail, 6 are not measurable. Failing dimensions: Verified, Bare metal, By construction, Efficiency, Honesty. Subject commands ran only inside the sandbox (attestations are in the card).

| Dimension | Metric | Status | Value | Floor |
|---|---|---|---|---|
| Verified | unproved escapes | pass | 0 | == 0 |
| Verified | specified share | pass | 100 | >= 100 |
| Verified | nonstandard axioms | pass | 0 | == 0 |
| Verified | trusted c lines | pass | 76 | tracked |
| Verified | trust ledger entries | pass | 9 | tracked |
| Verified | non vacuity | not measurable (2) | - | >= 100 |
| Bare metal | freestanding build | **FAIL** | 0 | == 1 |
| Bare metal | libc symbols | **FAIL** | 5 | == 0 |
| By construction | hand written tests | **FAIL** | 1 | == 0 |
| By construction | mutation score | not measurable (2) | - | >= 100 |
| Efficiency | throughput vs best | not measurable (2) | - | >= 80 |
| Velocity | tier1 seconds | pass | 58.8 | < 60 |
| Velocity | open prs | pass | 0 | == 0 |
| Velocity | commits per hour | pass | 1.218 | tracked |
| Velocity | p90 commit to main seconds | not measurable (1) | - | tracked |
| Honesty | gate selftests | pass | 100 | >= 100 |
| Honesty | gates self tested | not measurable (2) | - | >= 100 |
| Honesty | attack suite | not measurable (2) | - | == 1 |

**Not measurable, and why.** (1) the change's first authored commit is not recorded on main (rebase and squash rewrite the dates, which read 0 under direct landing). (2) not implemented in this runner version.

**Hand-written tests of the subject's code counted (1):** `tests/abi_test.c`. 5 gate self-test files are counted under process honesty instead.
