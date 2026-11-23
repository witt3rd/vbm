# Scorecard

Status: draft by a worker, 2026-11-19; goals and targets are the owner's to set.

This file measures vbm-rng against what its own files say it is for. It invents no goal; every goal below cites where the repository states it. Every metric is an integer; the unit is in its name. Every command runs from the repository root. A floor is the worst value the project accepts: it starts equal to `now` and only moves toward better. The history starts with the `now` column; a later measure adds a dated row below the table.

## Goals as the repository states them

- **G1** Deterministic, splittable generators with specified streams; exactly reproducible sampling (uniform integers in a range, uniform fractions in exact arithmetic) for simulation and experiments: `README.md:3`, `AGENTS.md:16`, `docs/decisions/0001-vbm-rng.md:6`.
- **G2** The same seed always gives the same output, bit for bit, on every machine; known-answer vectors are the conformance evidence, each kernel-checked, and a change to a vector is a breaking change: `docs/spec.md:6`, `docs/spec.md:229`, `README.md:11`.
- **G3** The raw stream of key 0 reproduces the published SplitMix64 outputs: `README.md:11`, `docs/spec.md:51`.
- **G4** Exact deterministic integer arithmetic only, no floating point in the specification, the code or the proofs: `docs/spec.md:10`.
- **G5** Every claim is a theorem and the ledger is the authority: only `proved` may be called verified; the axiom set is the three standard ones: `docs/proof-ledger.md:5`, `docs/spec.md:309`, `scripts/tier1.sh:47`.
- **G6** What cannot be proved is marked as trusted, with a contract and a test where one can exist: `docs/trust-ledger.md:3`, `docs/trust-ledger.md:5`, `docs/spec.md:309`.
- **G7** No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp` in Lean: `AGENTS.md:24`, `CONTRIBUTING.md:8`.
- **G8** The core is pure data and total functions over `Init`; `VbmRng` imports `Init` and itself only: `AGENTS.md:18`, `AGENTS.md:33`.
- **G9** A zero-warning build: `lakefile.lean:5`, `scripts/tier1.sh:43`.
- **G10** Public-ready always: no private name, no path of ours, no number of ours, no e-mail: `AGENTS.md:28`.
- **G11** Small and fast: at most 150 production lines per change, 45 minutes without a passing build, one gate run before the push: `CONTRIBUTING.md:10`, `AGENTS.md:29`, `AGENTS.md:27`.
- **G12** Open questions of the specification get settled: `docs/spec.md:315`.
- **G13** Release: the library is pre-release, version 0.1.0, nothing published: `README.md:5`, `VERSION:1`.

## Metrics

| metric | direction (higher or lower is better) | goal it serves | how to measure (the exact command, from the repository root) | now (value and date) | floor (= now) | target (blank: the owner sets it) |
|---|---|---|---|---|---|---|
| proof-ledger-gaps (count of claims partial or open) | lower | every claim proved or marked `limit` (G5) | `awk '/\*\*(partial|open)\*\*/{n++} END{print n+0}' docs/proof-ledger.md` | 0 (2026-11-19) | 0 | |
| proved-claims (count) | higher | G5 | `awk '/\*\*proved\*\*/{n++} END{print n+0}' docs/proof-ledger.md` | 34 (2026-11-19) | 34 | |
| proved-share-hundredths-of-percent (proved claims of all ledger claims) | higher | G5 | `awk '/\*\*proved\*\*/{p++} /^\| `/{t++} END{print int(p*10000/t)}' docs/proof-ledger.md` | 8947 (2026-11-19) | 8947 | |
| limit-claims (count of claims no machine decides: Q1-Q3, S5) | lower | G5, G6 | `awk '/^\| `/ && !/\*\*proved\*\*/{n++} END{print n+0}' docs/proof-ledger.md` | 4 (2026-11-19) | 4 | |
| trust-ledger-gaps (trusted items with no written contract or no test) | lower | G6 | `.land/tool/bin/land-lean trust \| sed -nE 's/.*; ([0-9]+) with no written contract.*/\1/p'` | 2 (2026-11-19) | 2 | |
| axiom-offenders (constants on a non-standard axiom) | lower | G5 | `.land/tool/bin/land-lean axiom \| sed -nE 's/.*checked, ([0-9]+) offending.*/\1/p'` | 0 (2026-11-19) | 0 | |
| forbidden-constructs (count of lines) | lower | G7 | `grep -rEw 'sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp\|native_decide' VbmRng VbmRngProofs VbmRng.lean VbmRngProofs.lean vectors \| grep -vc tier1-allow \|\| true` | 0 (2026-11-19) | 0 | |
| floating-point-uses (count of lines naming `Float` in the core) | lower | G4 | `grep -rwh 'Float' VbmRng VbmRng.lean \| wc -l` | 0 (2026-11-19) | 0 | |
| core-imports-outside-init (count) | lower | G8 | `grep -rhE '^[[:space:]]*(import\|prelude\|public import)' VbmRng VbmRng.lean \| grep -vcE '^import VbmRng' \|\| true` | 0 (2026-11-19) | 0 | |
| vectors (known-answer lines) | higher | G2, G3 | `awk '!/^[[:space:]]*(#\|$)/{n++} END{print n+0}' vectors/known-answers.txt` | 61 (2026-11-19) | 61 | |
| vector-gate-cases (ran-evidence of the vector test) | higher | G2 | `scripts/test_vectors.sh \| tail -1` | 65 (2026-11-19) | 65 | |
| build-warnings (count of warning lines of the build) | lower | G9 | `lake build VbmRng VbmRngProofs LandLedger 2>&1 \| grep -ci warning \|\| true` | 0 (2026-11-19) | 0 | |
| public-lint-violations (count of findings) | lower | G10 | `scripts/lint-public \| grep -c ':' \|\| true` | 0 (2026-11-19) | 0 | |
| core-lines (lines of the verified core, `VbmRng/` and its root) | lower | G11 | `cat VbmRng.lean VbmRng/*.lean \| wc -l` | 235 (2026-11-19) | 235 | |
| proof-to-core-permille (proof lines per 1000 core lines) | higher | G5 | `echo $(( $(cat VbmRngProofs.lean VbmRngProofs/*.lean \| wc -l) * 1000 / $(cat VbmRng.lean VbmRng/*.lean \| wc -l) ))` | 6749 (2026-11-19) | 6749 | |
| open-questions (count in `docs/spec.md`) | lower | G12 | `grep -cE '^[0-9]+\. `\[open question\]`' docs/spec.md` | 4 (2026-11-19) | 4 | |
| release-tags (count of `v*` tags) | higher | G13 | `git tag -l 'v*' \| wc -l` | 0 (2026-11-19) | 0 | |
| vector-test-seconds (`scripts/test_vectors.sh`) | lower | G11 | `s=$(date +%s); scripts/test_vectors.sh >/dev/null; echo $(( $(date +%s) - s ))` | 1 (2026-11-19) | 1 | |
| recheck-seconds (`land-lean recheck --selftest`, one run, over a minute) | lower | G11 | `s=$(date +%s); .land/tool/bin/land-lean recheck --selftest >/dev/null; echo $(( $(date +%s) - s ))` | 169 (2026-11-19) | 169 | |
| tier1-seconds (the whole gate) | lower | G11 | `s=$(date +%s); mise exec -- scripts/tier1.sh >/dev/null; echo $(( $(date +%s) - s ))` | unmeasured: needs `mise exec` to reach the pinned toolchain (offline here, the jail cannot fetch it) and the work rules forbid running Tier 1 | unmeasured | |

Measured in the worker's jail on 2026-11-19 with the pinned Lean 4.35.0 on the path. The commands that end in `|| true` print 0 and would otherwise exit 1 on a zero count. `build-warnings` reads a cached build; the build treats any warning as an error (`lakefile.lean:5`), so a successful build is zero warnings. `scripts/ledger-baseline.txt` already keeps a ratchet for `proved`, `open` and `total` (the lander refuses a fall); this table adds the rest.

## Health today

- Regressed: nothing. Every measured value is at the best end of its direction where a best end exists: no gap in the ledger, 0 axiom offenders, 0 forbidden constructs, 0 floating-point uses, 0 imports outside `Init`, 0 warnings, 0 lint findings.
- Unmeasured: `tier1-seconds`, the one number that says how long the whole gate takes against the 45-minute limit. It needs the pinned toolchain through `mise exec`. `recheck-seconds` (169) is the one heavy part measured and is the likely bulk of the gate.
- Far from where the goals point: `proved-share-hundredths-of-percent` is 8947, not 10000, because 4 claims are `limit` (Q1, Q2, Q3 trusted; S5 stated, not proved); `trust-ledger-gaps` is 2, since both trust entries have no written contract or no test (`docs/trust-ledger.md:10`, `:19`); `open-questions` is 4; `release-tags` is 0 with the library still pre-release.
- Not measured by anything: the statistical quality of the streams (Q1). The repository states that no test battery is run or claimed (`docs/trust-ledger.md:29`).

## What a steward would do first

1. Measure `tier1-seconds` in a place where `mise exec` works and record it as the first history row, because it is the only unmeasured metric and the only one that watches the 45-minute limit (G11).
2. Move `open-questions` down by having the owner decide the four items of `docs/spec.md:315` (default answers are already written there), which also settles whether `limit-claims` should fall (S5) or whether Q1 gets an offline battery.
3. Lower `trust-ledger-gaps` from 2 by adding a written contract or a test to T1 and T2 of `docs/trust-ledger.md`, or by recording why none can exist; then decide `release-tags` (cut the first signed tag when the owner wants a pinnable 0.1.0).

## Questions for the owner

- What are the targets? The target column is blank for every metric. Candidates the repository suggests but does not set: `proof-ledger-gaps` 0 held, `limit-claims` 4 or 1 (is S5, the shuffle's uniformity, to be proved: `docs/spec.md:317`), `trust-ledger-gaps` 0, `open-questions` 0.
- Is a statistical battery on the reference model wanted as evidence for Q1 (`docs/spec.md:316`)? If yes, it needs a metric (for example `battery-failures`) and a place to record the run; the repository names neither.
- Is publishing a signed release a goal, and when (`README.md:5`)? The repository says only that it is pre-release.
- Is there a goal for speed of the generators or for the size of the proofs? The repository states none (only the gate-time and diff-size limits of G11), so no such metric is here.
- Is a multi-word bound above 2^64 for `uniformBelow` wanted (`docs/spec.md:318`)? It would add a goal and a metric.
