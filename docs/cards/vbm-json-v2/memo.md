---
title: vbm-json: scorecard (static metrics)
subtitle: Subject commit 6b239dea3bf9, scorecard 459c5ce10e46, adapter dc397582256a
kicker: Scorecard · one card
footer: vbm-json-v2
---

**Strict result: FAIL.** Implemented-and-measurable result: FAIL. 6 metrics pass, 1 fail, 10 are not measurable. Failing dimensions: Verified, Bare metal, By construction, Efficiency, Velocity, Honesty. Nothing of the subject was executed.

| Dimension | Metric | Status | Value | Floor |
|---|---|---|---|---|
| Verified | unproved escapes | pass | 0 | == 0 |
| Verified | specified share | not measurable (3) | - | >= 100 |
| Verified | trusted c lines | pass | 76 | tracked |
| Verified | trust ledger entries | pass | 9 | tracked |
| Verified | non vacuity | not measurable (2) | - | >= 100 |
| Bare metal | freestanding build | not measurable (2) | - | == 1 |
| Bare metal | libc symbols | not measurable (2) | - | == 0 |
| By construction | hand written tests | **FAIL** | 1 | == 0 |
| By construction | mutation score | not measurable (2) | - | >= 100 |
| Efficiency | throughput vs best | not measurable (2) | - | >= 80 |
| Velocity | tier1 seconds | not measurable (3) | - | < 60 |
| Velocity | open prs | pass | 0 | == 0 |
| Velocity | commits per hour | pass | 1.218 | tracked |
| Velocity | p90 commit to main seconds | not measurable (1) | - | tracked |
| Honesty | gate selftests | pass | 100 | >= 100 |
| Honesty | gates self tested | not measurable (2) | - | >= 100 |
| Honesty | attack suite | not measurable (2) | - | == 1 |

: Every value is read from the pinned commit by the runner; none is self-reported.

**Not measurable, and why.** (1) a change's first authored commit is not recorded on main (squash merges and rebases rewrite author and committer dates, so a date difference reads 0 under direct landing): the lander's start-to-landing log is needed. (2) not implemented in this runner version. (3) subject code runs only inside the sandbox and no launcher is configured (--sandbox): nothing was executed.

**Hand-written tests of the subject's code counted (1):** `tests/abi_test.c`. 5 gate self-test files are counted under process honesty instead.
