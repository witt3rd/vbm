# A fast gate and small changes

The gate is the ceiling on throughput: a five-minute gate with one change at a time lands at most twelve an hour. Split verification in two tiers.
- **Tier 1** (before landing, under a minute): type check, zero-warning build, forbidden-construct scans, the negative self-tests, the affected tests.
- **Tier 2** (after the merge, a few minutes): the full suites, fuzzing, independent proof checkers.

Keep changes small: about 150 lines of production code, and no worktree older than 45 minutes without a passing build; past either, stop and decompose into changes that land in order (branch by abstraction, expand and contract).
Small changes conflict far less than large ones; that is the measurable reason to keep them small.
