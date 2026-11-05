---
title: vbm-json: scorecard (static metrics)
subtitle: Subject commit 6b239dea3bf9, scorecard 1295a427d9b9, adapter 882dc95116a6
kicker: Scorecard · one card
footer: vbm-json-v1
---

**Strict result: FAIL.** Implemented-and-measurable result: FAIL. 6 metrics pass, 1 fail, 9 are not measurable. A dimension below its floor fails the whole card, and not-measurable fails its floor. Failing dimensions: Verified, Bare metal, By construction, Efficiency, Velocity, Honesty. Nothing of the subject was executed.

| Dimension | Metric | Status | Value | Floor |
|---|---|---|---|---|
| Verified | unproved escapes | pass | 0 | == 0 |
| Verified | specified share | not measurable (B) | - | >= 100 |
| Verified | trusted c lines | pass | 76 | tracked |
| Verified | trust ledger entries | pass | 9 | tracked |
| Verified | non vacuity | not measurable (A) | - | >= 100 |
| Bare metal | freestanding build | not measurable (A) | - | == 1 |
| Bare metal | libc symbols | not measurable (A) | - | == 0 |
| By construction | hand written tests | **FAIL** | 6 | == 0 |
| By construction | mutation score | not measurable (A) | - | >= 100 |
| Efficiency | throughput vs best | not measurable (A) | - | >= 80 |
| Velocity | tier1 seconds | not measurable (B) | - | < 60 |
| Velocity | open prs | pass | 0 | == 0 |
| Velocity | commits per hour | pass | 1.218 | tracked |
| Velocity | p90 commit to main seconds | pass | 0 | tracked |
| Honesty | gates self tested | not measurable (A) | - | >= 100 |
| Honesty | attack suite | not measurable (A) | - | == 1 |

: Every value is read from the pinned commit by the runner; none is self-reported.

**Not measurable, and why.** (A) not implemented in this runner version. (B) subject code runs only inside the sandbox and no launcher is configured (--sandbox): nothing was executed.

**Hand-written tests counted (6):** `scripts/test_abi.sh`, `scripts/test_githook.sh`, `scripts/test_land_direct.sh`, `scripts/test_protected_set.sh`, `scripts/test_run_parallel.sh`, `tests/abi_test.c`.
