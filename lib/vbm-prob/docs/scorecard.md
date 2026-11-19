# Scorecard

Status: draft by a worker, 2026-11-19; goals and targets are the owner's to set.

Measured in a clean worktree at the tip of `main` (Lean 4.35.0 from `PATH`, offline; `mise exec` could not fetch the toolchain, the same pinned `lake` was used directly). Every metric is an integer; the unit is in its name.

## Goals as the repository states them
- Exact probabilities and discrete distributions: a probability as an exact value, validation and refusals, normalisation, mixture, mean, cumulative distribution and quantile, with proofs. (`README.md:3`, `AGENTS.md:16`, `docs/decisions/0001-vbm-prob.md:6`)
- Exact discrete probability, valid by construction and kept valid by every operation. (`docs/spec.md:6`)
- Every function is total; a refusal is a typed `Refusal`, never a default, a panic or an `Option`; no floating point. (`docs/spec.md:20`, `docs/spec.md:22`)
- Every specified property is proved, each with a non-vacuity witness, and the proof ledger is closed (every label has an obligation); the known-answer vectors are proved as examples. (`AGENTS.md:25`, `docs/spec.md:154`, `docs/spec.md:379`)
- No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp`; the proofs rest only on the standard axioms. (`AGENTS.md:24`, `docs/trust-ledger.md:11`)
- Pure data and total functions over `Init` only: no input or output, network, storage or model call; a small verified core. (`AGENTS.md:18`, `AGENTS.md:33`)
- Public-ready always: no private name, path or e-mail. (`AGENTS.md:28`)
- A zero-warning build, and a gate (Tier 1) that runs once before each push, with ran-evidence. (`AGENTS.md:10`, `AGENTS.md:26`, `scripts/tier1.sh:66`)
- Small diffs: at most 150 production lines under `VbmProb/` per change, at most 45 minutes without a passing build. (`AGENTS.md:29`, `CONTRIBUTING.md:10`)
- What is relied on without proof is written down as a trust ledger. (`docs/trust-ledger.md:3`)
- The slices S1 to S15 land the whole specified library; then a release so consumers can pin it. (`docs/spec.md:360`, `docs/spec.md:347`, `README.md:5`)
- Open questions of the specification are decided, not left standing. (`docs/spec.md:3`, `docs/spec.md:383`)

## Metrics
| metric | direction (higher or lower is better) | goal it serves | how to measure (the exact command, from the repository root) | now (value and date) | floor (= now) | target (blank: the owner sets it) |
|---|---|---|---|---|---|---|
| `proof-ledger-gaps` | lower | every claim proved (AGENTS.md:25; spec.md:379) | `sed -nE 's/^\*\*[0-9]+ proved, ([0-9]+) partial, ([0-9]+) open, ([0-9]+) limit, of [0-9]+\..*/\1 \2 \3/p' docs/proof-ledger.md \| awk '{print $1+$2+$3}'` | 0 (2026-11-19) | 0 | |
| `proof-ledger-proved-claims` | higher | same | `sed -nE 's/^\*\*([0-9]+) proved,.*/\1/p' docs/proof-ledger.md` | 30 (2026-11-19) | 30 | |
| `spec-labels-without-ledger-claim` | lower | every spec property proved (AGENTS.md:25; spec.md:154,379) | `comm -23 <(grep -oE '^- \*\*[PFD][RXS][0-9]+' docs/spec.md \| grep -oE '[PFD][RXS][0-9]+' \| sort -u) <(grep -oE '[PFD][RXS][0-9]+-' docs/proof-ledger.md \| grep -oE '[PFD][RXS][0-9]+' \| sort -u) \| wc -l` | 18 of 41 (2026-11-19) | 18 | |
| `slices-unlanded` | lower | the whole specified library (spec.md:360-379) | `echo $((15 - $(git log --format=%s \| grep -oE 'slice: S[0-9]+ ' \| sort -u \| wc -l)))` | 9 (2026-11-19) | 9 | |
| `known-answer-vectors-proved` | higher | the specified vectors proved (spec.md:206,379) | `cat VbmProbProofs/Vectors.lean 2>/dev/null \| grep -c '^example'` | 0 (2026-11-19) | 0 | |
| `forbidden-constructs` | lower | no sorry, admit, axiom, unsafe, implemented_by, csimp (AGENTS.md:24) | `grep -rHnE '\b(sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp)\b' VbmProb VbmProbProofs VbmProb.lean VbmProbProofs.lean \| grep -v tier1-allow \| wc -l` | 0 (2026-11-19) | 0 | |
| `axiom-offending-constants` | lower | proofs rest only on the three standard axioms (AGENTS.md:24; trust-ledger.md:11) | `.land/tool/bin/land-lean axiom \| sed -nE 's/.*checked, ([0-9]+) offending.*/\1/p'` | 0 of 581 (2026-11-19) | 0 | |
| `build-warnings` | lower | zero-warning build (tier1.sh:66; lakefile.lean:5) | `rm -rf .lake/build && lake build VbmProb VbmProbProofs LandLedger 2>&1 \| grep -ci warning` | 0 (2026-11-19) | 0 | |
| `public-lint-violations` | lower | public-ready always (AGENTS.md:28) | `scripts/lint-public \| grep -cE ':[0-9]+: '` | 0 (2026-11-19) | 0 | |
| `trust-ledger-gaps` | lower | say what is relied on without proof (trust-ledger.md:3) | `.land/tool/bin/land-lean trust \| sed -nE 's/.*; ([0-9]+) with no written contract.*/\1/p'` | 2 of 2 entries (2026-11-19) | 2 | |
| `float-or-second-ratio-hits` | lower | no float, no second ratio (spec.md:22, 204) | `(grep -rw Float VbmProb; grep -rnE '^\s+(num\|den)\s*:' VbmProb) \| wc -l` | 0 (2026-11-19) | 0 | |
| `open-questions` | lower | spec decided, not guessed (spec.md:3, 383) | `grep -o '\[open question\]' docs/spec.md \| wc -l` | 8 (2026-11-19) | 8 | |
| `verified-core-lines` | lower | small, total, Init-only core (AGENTS.md:18) | `find VbmProb VbmProb.lean -name '*.lean' \| xargs cat \| wc -l` | 381 (2026-11-19) | 381 | |
| `max-landed-diff-lines` | lower | small diffs, at most 150 (AGENTS.md:29; CONTRIBUTING.md:10) | `for c in $(git rev-list HEAD); do git diff --numstat $c^ $c -- VbmProb 2>/dev/null \| awk '{s+=$1} END{print s+0}'; done \| sort -rn \| head -1` | 128 (2026-11-19) | 128 | |
| `release-tags` | higher | a release consumers can pin (spec.md:347; README.md:5) | `git tag \| wc -l` | 0 (2026-11-19) | 0 | |
| `tier1-seconds` | lower | a gate fast enough to run once before every push (AGENTS.md:10, 29) | `s=$(date +%s); scripts/tier1.sh >/dev/null 2>&1; echo $(( $(date +%s) - s ))` | 179 (2026-11-19) | 179 | |

Notes. `spec-labels-without-ledger-claim` counts the 41 labelled properties (PR, FX, DS) of `docs/spec.md` whose label does not yet appear in a ledger claim name; it approximates the open part of the spec, because the ledger only lists claims already written. `slices-unlanded` counts the slices S1-S15 not yet in a commit subject (S0 is the skeleton). `float-or-second-ratio-hits` is the intended RL1 scan (`docs/spec.md:204`), which is not yet in Tier 1 (S15). `tier1-seconds` is one full run (cold build included) on a shared 4-core box; it is noisy, and the `recheck` gate alone took about 170 s. `release-tags` has floor 0 as the baseline; the first release moves it to 1.

## Health today
- Regressed: nothing. The ledger has 0 gaps over 30 claims, there are no forbidden constructs, no offending axiom, no build warning and no public-lint violation, and the largest landed diff (128 lines) is under 150.
- Far from where the goals point: the specified library is only partly written. 9 of 15 slices are unlanded, 18 of the 41 labelled properties have no ledger claim (all of the distribution properties DS1-DS3 and DS5-DS17, and FX13, FX14), and the known-answer vectors are at 0 proved examples. The ledger reads 30 of 30 proved only because it lists the claims written so far.
- Unmeasured: none. (No test or lint reports an item as skipped; the RL1 scan is not in Tier 1 yet.)
- Standing: no release tag (0), 8 open questions in the specification, 2 trust-ledger entries with no written contract or no test. The gate takes about 3 minutes.

## What a steward would do first
1. Land the remaining slices in the order of `docs/spec.md:391`, starting with S6 (`Dist`) and S7 (queries), because they move `slices-unlanded` and `spec-labels-without-ledger-claim` down and `proof-ledger-proved-claims` up.
2. Land S15 (the vectors as proved examples and the RL1 scan), which moves `known-answer-vectors-proved` up from 0 and gives `float-or-second-ratio-hits` a real gate.
3. Cut the first release (M0) once S15 is in, which moves `release-tags` from 0 and lets consumers pin the library; settle the 8 open questions on the way (`open-questions`).

## Questions for the owner
- Targets: the repository gives no target for any metric. What are the targets for `proof-ledger-proved-claims` (all 41 labelled properties plus the support claims?), `known-answer-vectors-proved` (the spec lists no count), `slices-unlanded` (0 at S15?), `open-questions` and `release-tags`?
- Is `verified-core-lines` to be tracked at all, and which way is better: the specification wants a small core, but the library is growing toward its specified size (381 lines now), so I left it with direction `lower` and no target.
- Is `tier1-seconds` a goal? The repository states a 45-minute budget for a change, not a gate time; what is the acceptable gate time?
- The two trust-ledger entries have no written contract or test (`trust-ledger-gaps` 2): is that to be accepted (the entries say accept) or driven to 0?
- Should the scorecard cover the consumers' migration (M1-M18, `docs/spec.md:347`)? They land in other repositories, so I did not measure them.
- Which goals should be added: performance of the exact `Rat` arithmetic under the named limits (`docs/spec.md:140`) has no measure in the repository, so I added none.
