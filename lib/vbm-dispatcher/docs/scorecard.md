# Scorecard

Status: draft by a worker, 2026-11-18; goals and targets are the owner's to set.

## Goals as the repository states them

1. **A work dispatcher written once in Lean 4 and machine-checked**: the pool's guard (`ready`) and chooser (`choose`) with the queue's port laws, and the two pure machines (tick, run). Source: `AGENTS.md:31`; `README.md:3` ("Proved in Lean 4"); `docs/decisions/0001-vbm-dispatcher.md:3`.
2. **Every claim is proved, and the proofs are listed in a generated ledger**: "Only `proved` may be called verified". Source: `README.md:13`; `docs/proof-ledger.md:5`; `AGENTS.md:40` (a theorem with a hypothesis carries a witness that it can hold).
3. **The tick and the run behave as specified**: the guard comes first and a refusal writes nothing; a claim is only for the chosen item; the lease is renewed at every beat; the item is finished once with the worker's typed outcome; a lost lease stops the worker and reports nothing; cleanup happens exactly once. Source: `docs/decisions/0001-vbm-dispatcher.md:15`, `:17`; `README.md:3`.
4. **Any interpreter can be checked against language-neutral conformance vectors**, generated from the Lean reference and checked in. Source: `README.md:9`; `docs/vectors.md:3`; `docs/decisions/0001-vbm-dispatcher.md:23`.
5. **The core is pure and small in what it trusts**: no input or output, no clock, no model, no network, no storage; imports `Init` and the pinned `VbmWork` only; nothing is trusted that is not in the trust ledger. Source: `AGENTS.md:33`; `AGENTS.md:49`; `docs/trust-ledger.md:3`.
6. **No cap, no heuristic**: every number (beat period, lease length, ceilings, floors) is the host's data, and control depends on typed data only. Source: the rule is at `AGENTS.md:50` and `docs/decisions/0001-vbm-dispatcher.md:19`.
7. **No forbidden construct in Lean** (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`), zero build warnings, no constant beyond the three standard axioms. Source: `AGENTS.md:39`; `scripts/tier1.sh:18-26` (forbidden scan), `scripts/check-zero-warning.sh:1`, `.land/lean.conf` (axiom gate).
8. **Public-ready, always**: no private name, no path of ours, no e-mail. Source: `AGENTS.md:43`; `CONTRIBUTING.md:11`.
9. **Every gate runs something and can fail**: ran-evidence and a negative self-test per gate. Source: `AGENTS.md:41`; `CONTRIBUTING.md:9`.
10. **Small diffs, landed directly, everything before the push once**: at most 150 production lines per change, 45 minutes to a passing build. Source: `AGENTS.md:44`; `CONTRIBUTING.md:10`; `AGENTS.md:42`.
11. **That the ports meet their laws is the application's conformance suite**, not a theorem here (a declared limit). Source: `docs/decisions/0001-vbm-dispatcher.md:23`; `docs/proof-ledger.md:23`.
12. **Still to come** (as AGENTS.md states them): non-interference, the reference model and the conformance vectors. Source: `AGENTS.md:36`. (The model and the vectors exist in the tree; see the questions.)

## Metrics

All commands are run from the repository root with the pinned toolchain on the path (`mise exec -- COMMAND`; here the toolchain `bin/` directory was put on `PATH` instead). Measured 2026-11-18 at commit `244d274` (tag `v0.3.0` plus 3 commits).

| metric | direction (higher or lower is better) | goal it serves | how to measure (the exact command, from the repository root) | now (value and date) | floor (= now) | target (blank: the owner sets it) |
|---|---|---|---|---|---|---|
| proved-claims-count | higher | 2, 3 | `.land/tool/bin/land-lean ledger \| sed -nE 's/^ledger: ([0-9]+) proved.*/\1/p'` | 21 (2026-11-18) | 21 | |
| proof-ledger-gaps-count (partial + open claims) | lower | 2 | `.land/tool/bin/land-lean ledger \| sed -nE 's/^ledger: [0-9]+ proved, ([0-9]+) partial, ([0-9]+) open.*/\1+\2/p' \| bc` | 0 (2026-11-18) | 0 | |
| proof-ledger-limits-count | lower | 2, 11 | `.land/tool/bin/land-lean ledger \| sed -nE 's/.* ([0-9]+) limit,.*/\1/p'` | 1 (2026-11-18) | 1 | |
| theorems-count (size of what is proved) | higher | 2 | `grep -rhE '^(protected \|private )?(theorem\|lemma) ' VbmDispatcher VbmDispatcherProofs VbmDispatcherWire.lean \| wc -l` | 84 (2026-11-18) | 84 | |
| witness-examples-count | higher | 2 | `grep -rhE '^example' VbmDispatcher VbmDispatcherProofs \| wc -l` | 22 (2026-11-18) | 22 | |
| theorems-without-witness-count | lower | 2 | no cheap command: needs a check that pairs each theorem that has a hypothesis with a witness (`AGENTS.md:40`) | unmeasured (needs such a pairing check; none exists) | | |
| axiom-offending-constants-count | lower | 5, 7 | `.land/tool/bin/land-lean axiom \| sed -nE 's/.*, ([0-9]+) offending.*/\1/p'` | 0 (2026-11-18) | 0 | |
| axiom-constants-checked-count (size of the verified core) | higher | 1, 5 | `.land/tool/bin/land-lean axiom \| sed -nE 's/.*: ([0-9]+) constants checked.*/\1/p'` | 1641 (2026-11-18) | 1641 | |
| verified-core-lean-lines | lower | 5, 10 | `cat VbmDispatcher.lean VbmDispatcher/*.lean \| wc -l` | 1154 (2026-11-18) | 1154 | |
| forbidden-constructs-count | lower | 7 | `grep -rnE '\b(sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp)\b' VbmDispatcher VbmDispatcherProofs VbmDispatcher.lean VbmDispatcherProofs.lean VbmDispatcherWire.lean vectors \| grep -v tier1-allow \| wc -l` | 0 (2026-11-18) | 0 | |
| build-warnings-count | lower | 7 | `rm -rf .lake/build && lake build VbmDispatcher VbmDispatcherProofs VbmDispatcherWire LandLedger vbm-dispatcher-vectors 2>&1 \| grep -ci warning` (a clean build: a cached one reports none) | 0 (2026-11-18) | 0 | |
| clean-build-seconds | lower | 10 | `rm -rf .lake/build && time lake build VbmDispatcher VbmDispatcherProofs VbmDispatcherWire LandLedger vbm-dispatcher-vectors` | 5 (2026-11-18) | 5 | |
| vectors-count | higher | 4 | `wc -l < vectors/vbm-dispatcher-vectors-1.jsonl` | 32 (2026-11-18) | 32 | |
| vector-gate-cases-count | higher | 4, 9 | `scripts/test_vectors.sh \| sed -nE 's/^ran: test_vectors: ([0-9]+) cases/\1/p'` | 11 (2026-11-18) | 11 | |
| vector-test-seconds | lower | 4, 10 | `time scripts/test_vectors.sh` | 4 (2026-11-18) | 4 | |
| public-lint-violations-count | lower | 8 | `scripts/lint-public \| wc -l` | 0 (2026-11-18) | 0 | |
| public-lint-gate-cases-count | higher | 8, 9 | `scripts/test_lint_public.sh \| sed -nE 's/^ran: test_lint_public: ([0-9]+) cases/\1/p'` | 8 (2026-11-18) | 8 | |
| trust-entries-count | higher (every trusted thing is named) | 5 | `grep -c '^### T' docs/trust-ledger.md` | 3 (2026-11-18) | 3 | |
| trust-gaps-count (entries with no written contract or no test) | lower | 5 | `.land/tool/bin/land-lean trust \| sed -nE 's/.*; ([0-9]+) with no written contract.*/\1/p'` | 3 (2026-11-18) | 3 | |
| commits-since-release-count | lower | 10 | `git rev-list "v$(cat VERSION)"..HEAD --count` | 3 (2026-11-18) | 3 | |
| tier1-seconds | lower | 9, 10 | `time mise exec -- scripts/tier1.sh` | unmeasured (the worker is told not to run Tier 1; needs a full run on the rebased tree) | | |
| port-conformance-claims-count (the application's suite for the ports' laws) | higher | 11 | none in this repository: the suite belongs to the application | unmeasured (needs the application's suite) | | |
| max-production-lines-per-change | lower | 10 | `git log --format=%h -n 20 -- VbmDispatcher \| while read c; do git diff --shortstat $c^ $c -- VbmDispatcher; done` (read the largest insertions) | unmeasured (not run; the history is short and mixed with renames) | | |

## Health today

- **Regressed:** nothing is regressed; the table has no earlier value, so every floor is today's value and the history starts here.
- **Clean on every measured gate:** no open or partial claim, no offending constant, no forbidden construct, no build warning, no public-lint violation, 32 vectors passing.
- **Unmeasured:** the time of the whole gate (`tier1-seconds`), the witness for every theorem with a hypothesis (`theorems-without-witness-count`, a rule in `AGENTS.md:40` that no script checks), the size of each change (`max-production-lines-per-change`), and the ports' conformance (the application's).
- **Far from where the goals point:** the trust ledger has 3 entries and all 3 are gaps (no written contract or no test beyond the tool's own); one claim is a declared limit (`the-ports-meet-their-laws`) and no machine in this repository can close it; `AGENTS.md:36` still lists the machines' proofs, the reference model and the vectors as "next", though they exist, so the stated plan and the tree disagree; the release is 3 commits behind `v0.3.0` (all are lander updates).

## What a steward would do first

1. Close the witness gap: add a check (or a ledger field) that every theorem with a hypothesis has a witness, so `theorems-without-witness-count` can be measured and held at 0.
2. Write a contract and a test for each trust-ledger entry, or record why none can exist, to move `trust-gaps-count` down from 3.
3. Measure `tier1-seconds` and `max-production-lines-per-change` on each landing and record them here, so the goals "everything before the push, once" and "small diffs" have a history; and bring `AGENTS.md:36` in line with the tree.

## Questions for the owner

- What are the targets? Every target cell is blank; none can be taken from the repository (it states rules and a plan, not numbers).
- Is the plan at `AGENTS.md:36` ("Next: the two machines and their proofs, non-interference, the reference model and the conformance vectors") current? The machines, their proofs, the model and 32 vectors are in the tree; is non-interference still to do, and is it a goal this scorecard should measure?
- Should the declared limit (`the-ports-meet-their-laws`) be counted as a gap, or as the boundary of the project? And is a conformance suite for the ports to be shipped here or stay in the application?
- Is a trust-ledger entry without a test (the toolchain, the tools) a gap to close or an accepted state?
- Is a release cadence a goal (the tag is `v0.3.0`; `README.md:5` says pre-release and nothing published)? What should a first public release require?
- Which time of the gate is acceptable (`tier1-seconds`)? `AGENTS.md:44` gives 45 minutes only to reach a passing build.
