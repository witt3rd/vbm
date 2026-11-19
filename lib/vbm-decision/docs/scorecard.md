# Scorecard

Status: draft by a worker, 2026-11-19; goals and targets are the owner's to set.

## Goals as the repository states them

Every goal below is quoted or paraphrased from a line of this repository. Nothing here is the worker's invention.

- **G1. A typed decision-model layer**: the typed questions (choice, noul, score, box) and typed answers with probabilities. `AGENTS.md:16`, `README.md:3`, `docs/spec.md:9`.
- **G2. The wire contract decodes and encodes exactly, and refuses what it does not recognise** (a sibling library does the bytes). `docs/spec.md:10`, `docs/spec.md:381`.
- **G3. A threshold truth table that fails closed.** `AGENTS.md:16`, `docs/spec.md:11`.
- **G4. Per-model calibration of thresholds from a labelled sample.** `AGENTS.md:16`, `docs/spec.md:12`; its properties C1 to C7 are at `docs/spec.md:366` onward and slice S5 at `docs/spec.md:428`.
- **G5. An audit record that every use can produce.** `docs/spec.md:13`.
- **G6. Everything not trusted is a theorem, and what is trusted is marked.** "Nothing else is trusted: every other claim is a theorem" `docs/spec.md:23`; "Proofs, not tests" `AGENTS.md:11`; the trust ledger `docs/trust-ledger.md:3`. Every theorem has a non-vacuity witness, `AGENTS.md:25`; no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`, `AGENTS.md:24`.
- **G7. Pure and small**: pure data and total functions over `Init`, no input or output, no network, no model call, `VbmDecision` imports `Init` and itself only. `AGENTS.md:18`, `AGENTS.md:33`, `docs/spec.md:15`.
- **G8. Real provider vectors**: every refusal code is reachable by a vector or a test, and the real provider examples are stored and decided as expected (slice S9, `vectors/`). `docs/spec.md:343`, `docs/spec.md:436`.
- **G9. Mechanical gates pass, with ran-evidence, and the build has zero warnings.** `CONTRIBUTING.md:7`, `CONTRIBUTING.md:9`, `scripts/tier1.sh:2`, `lakefile.lean:5` (`warningAsError`).
- **G10. Public-ready always**: no private name, path or secret in the tree. `AGENTS.md:28`, `AGENTS.md:30`.
- **G11. Small diffs**: at most 150 production lines under `VbmDecision/` per change. `CONTRIBUTING.md:10`, `AGENTS.md:2`.
- **G12. Released**: today "pre-release; nothing is published", so a release is where the repository points. `README.md:5`, `VERSION`.

## Metrics

Units are in the metric name. "Floor" starts equal to "now" and only moves toward better. Commands run from the repository root; `mise exec --` is the repository's own way to get the pinned Lean (`mise.toml`). `|` inside a command is written `\|` for the table.

| metric | direction | goal it serves | how to measure (from the repository root) | now (value and date) | floor (= now) | target |
|---|---|---|---|---|---|---|
| proof-ledger-gaps (count of claims not `proved`) | lower | G6, G2 | `grep -cE '^\| `[^`]+` \| (\*\*)?(partial\|open\|limit)' docs/proof-ledger.md` | 2 (`decode-refuses-unknown`, `battery-check-sound-complete`), 2026-11-19 | 2 | |
| proved-claims-share-hundredths-percent (proved over all ledger claims) | higher | G6 | `echo $((10000 * $(grep -c '\*\*proved\*\*' docs/proof-ledger.md) / $(grep -cE '^\| `[^`]+` \| ' docs/proof-ledger.md)))` | 9545 (42 of 44), 2026-11-19 | 9545 | |
| spec-properties-without-ledger-claim (count of properties named in `docs/spec.md` section 10 and 14.6 with no ledger claim) | lower | G4, G6 | `grep -oP '^- [A-Z]+[0-9]+ \x60\K[a-z0-9-]+' docs/spec.md \| while read s; do grep -qP "\x60$s\x60" docs/proof-ledger.md \|\| echo $s; done \| grep -c .` | 7 (C1 to C7, calibration: `VbmDecision/Calibrate.lean` does not exist), 2026-11-19 | 7 | |
| build-warnings (count, cold build) | lower | G9 | `rm -rf .lake/build && mise exec -- lake build VbmDecision VbmDecisionProofs 2>&1 \| grep -ci warning` | 0, 2026-11-19 | 0 | |
| forbidden-construct-hits (count of unmarked `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` in Lean) | lower | G6 | `grep -rhE '\b(sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp)\b' VbmDecision VbmDecisionProofs VbmDecision.lean VbmDecisionProofs.lean \| grep -vc tier1-allow` | 0, 2026-11-19 | 0 | |
| axiom-offending-constants (count) | lower | G6 | `mise exec -- .land/tool/bin/land-lean axiom` (reads `N offending`; 2940 constants checked) | 0, 2026-11-19 | 0 | |
| trust-ledger-gaps (count of trusted items with no written contract or no test) | lower | G6 | `mise exec -- .land/tool/bin/land-lean trust` (reads `2 with no written contract or no test`) | 2 (T1, T2), 2026-11-19 | 2 | |
| public-lint-violations (count of findings) | lower | G10 | `scripts/lint-public \| grep -c .` | 0, 2026-11-19 | 0 | |
| vectors-stored (count of files under `vectors/`) | higher | G8 | `find vectors -type f 2>/dev/null \| wc -l` | 0 (the directory does not exist; vectors V1 to V14 and BV1 to BV18 are only shapes in `docs/spec.md`), 2026-11-19 | 0 | |
| conformance-cases (count in `ran: conformance: N cases`) | higher | G8 | no command yet: slice S9 adds the runner (`docs/spec.md:436`) | unmeasured (the runner does not exist; needs S8 and S9) | unmeasured | |
| verified-core-lines (lines of Lean under `VbmDecision/`, the verified core) | lower | G7, G11 | `find VbmDecision -name '*.lean' \| xargs cat \| wc -l` | 1437, 2026-11-19 | 1437 | |
| spec-open-questions (count in `docs/spec.md` section 13) | lower | G2, G4 | `sed -n '/^## 13\./,/^## 14\./p' docs/spec.md \| grep -cE '^[0-9]+\. '` | 10, 2026-11-19 | 10 | |
| oversize-slices (count of commits touching `VbmDecision/` with more than 150 lines added; the history cannot improve, new ones must not appear) | lower | G11 | `git log --format='@%h' --numstat -- VbmDecision \| awk '/^@/{c=$1;next} {a[c]+=$1} END{for(k in a) if(a[k]>150) n++; print n+0}'` | 4 (S10 335, S7a 249, S6 187, S7b 153 lines), 2026-11-19 | 4 | |
| release-tags (count of git tags) | higher | G12 | `git tag --list \| wc -l` | 0 (VERSION 0.0.0), 2026-11-19 | 0 | |
| gate-seconds (wall time of the whole gate, warm build) | lower | G9 | `time mise exec -- scripts/tier1.sh` | 169 (exit 0, `tier1: ok`), 2026-11-19 | 169 | |

## Health today

- **Green and held**: zero warnings, zero forbidden constructs, zero offending axioms (2940 constants), zero public-lint findings, and the gate passes; 42 of 44 ledger claims are `proved` (9545 hundredths of a percent).
- **Not yet started**: calibration (G4). Seven properties C1 to C7 are written in the spec and have no ledger claim and no code; `VbmDecision/Calibrate.lean` does not exist. This is the largest gap between the goals and the tree. The spec's own battery section says it has no calibration module (`docs/spec.md:467`), so S5 is the only calibration slice.
- **Not yet started**: provider vectors (G8). `vectors/` does not exist (0 stored) and the conformance runner does not exist, so `conformance-cases` is unmeasured. The spec says every refusal code is reachable by a vector or a test; no metric here checks that yet.
- **Partial**: two claims are `partial` (nested extra keys in the decoders are witnessed by examples only; the battery check's refusal paths are witnessed by one example per code, not proved). The trust ledger names two items with no written contract or no test (the Lean toolchain and the scripts' tools); they are accepted on purpose.
- **Unreleased**: no tag, VERSION 0.0.0, README says pre-release.
- **Size discipline**: four slices went over the 150-line limit (S10 335, S7a 249, S6 187, S7b 153); the history is fixed, so the floor is the count.
- **Gate time**: 169 seconds for one run, warm; no target says what is too slow.

## What a steward would do first

1. Write slice S5 (calibration, `VbmDecision/Calibrate.lean` and its proofs C1 to C7) to bring `spec-properties-without-ledger-claim` from 7 to 0 and raise `proved-claims-share-hundredths-percent`.
2. Close the two partial claims (the nested-object unknown-key proof and the battery refusal-path proof) to bring `proof-ledger-gaps` from 2 to 0.
3. Store the first real provider vectors under `vectors/` and add the conformance runner (slice S9) to move `vectors-stored` from 0 and make `conformance-cases` measurable; then cut a first tag to move `release-tags`.

## Questions for the owner

- Targets: none is in the repository. What is the target for each metric above (for example, `proof-ledger-gaps` 0, `vectors-stored` at least one per refusal code)?
- Is calibration (G4) still wanted in this library? The spec keeps it (`docs/spec.md:12`, S5) but the battery section hands calibration of battery cuts to a forecast library (`docs/spec.md:467`).
- Is `verified-core-lines` better lower (less to trust) or is growth expected as slices land? The worker chose "lower" for want of a stated direction.
- What counts as a release for G12 (a tag, a version, a publication)? The repository says only "pre-release".
- Is there a limit on the gate time (`gate-seconds`)? None is stated; `LAND_STEP_TIMEOUT=1800` is the only bound (`.land/land.conf`).
- Should the number of test cases be a metric? `AGENTS.md:11` says "Proofs, not tests", so the worker left it out (the single test script runs 8 cases).
- The sibling wire library (S8, `docs/spec.md:435`) is in another repository: is its state part of this scorecard?
