# Scorecard

Status: draft by a worker, 2026-11-18; goals and targets are the owner's to set.

## Goals as the repository states them

1. **A project's scorecard, written once in Lean 4 and machine-checked**: named metrics, each with a direction, a floor that only moves toward better, a target the owner sets, and an append-only history. (`AGENTS.md:16`, `README.md:3`)
2. **A check refuses a regression; banking never records a worse number; a floor is loosened only by an explicit, reasoned reset.** (`AGENTS.md:16`, `README.md:3`, `docs/decisions/0001-vbm-scoreboard.md:6`)
3. **A check fails closed on an unmeasured metric**; the ratchet's rules stay out of every project's glue. (`docs/decisions/0001-vbm-scoreboard.md:6`)
4. **Every claim is proved, not tested**: "Behaviour lands as a specification and its proofs"; every theorem with a hypothesis carries a witness that the hypothesis can hold. (`AGENTS.md:25`, `AGENTS.md:11`)
5. **The core stays pure and small**: data and total functions over `Init`, no input or output, no dependency; `VbmScoreboard` imports `Init` and itself only, `VbmScoreboardWire` imports `Lean`, `VbmScoreboard` and itself only. (`AGENTS.md:18`, `AGENTS.md:33`, `README.md:9`)
6. **Nothing unverified is hidden**: no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`; what cannot be proved is listed in the trust ledger. (`AGENTS.md:24`, `docs/trust-ledger.md:3`)
7. **Every gate can fail and shows it ran**: a negative self-test and `ran: NAME: N cases` with N > 0. (`AGENTS.md:26`, `CONTRIBUTING.md:9`)
8. **Zero build warnings.** (`AGENTS.md:37`, `CONTRIBUTING.md:7`)
9. **Public-ready, always**: no private name, no path, no number of ours, no e-mail. (`AGENTS.md:28`)
10. **Small diffs**: at most 150 production lines under `VbmScoreboard/` per change; 45 minutes without a passing build is a stop. (`CONTRIBUTING.md:10`, `AGENTS.md:29`)
11. **The wire formats (provider protocol, baseline and history files) are specified and round-trip**; their words are kept exactly once released. (`docs/decisions/0001-vbm-scoreboard.md:14`, `AGENTS.md:33`)
12. **The command-line tool (slice S3) replaces the first consumer's shell script.** (`docs/decisions/0001-vbm-scoreboard.md:15`)
13. **Pre-release now; something others can pin.** "Pre-release ... Nothing is published to a package registry." (`README.md:5`, `SECURITY.md:3`)

## Metrics

All commands run from the repository root with the pinned toolchain (`lake` and `lean` 4.35.0 on `PATH`; the repository's own wrapper is `mise exec -- ...`, which could not fetch the toolchain offline here). Values measured 2026-11-18.

| metric | direction (higher or lower is better) | goal it serves | how to measure (the exact command, from the repository root) | now (value and date) | floor (= now) | target (blank: the owner sets it) |
|---|---|---|---|---|---|---|
| `proof-ledger-claims-proved` (count) | higher | 4 | `grep -c '\*\*proved\*\*' docs/proof-ledger.md` | 26, 2026-11-18 | 26 | |
| `proof-ledger-claims-unproved` (count of partial, open or limit claims) | lower | 4 | `grep '^\| `' docs/proof-ledger.md \| grep -vc '\*\*proved\*\*'` | 0, 2026-11-18 | 0 | |
| `theorems` (count in `VbmScoreboardProofs/`) | higher | 4 | `cat VbmScoreboardProofs/*.lean \| grep -cE '^[[:space:]]*(protected \|private )?theorem'` | 60, 2026-11-18 | 60 | |
| `non-vacuity-witnesses` (count of `example` in `VbmScoreboardProofs/`) | higher | 4 | `cat VbmScoreboardProofs/*.lean \| grep -cE '^[[:space:]]*example'` | 39, 2026-11-18 | 39 | |
| `forbidden-construct-hits` (count) | lower | 6 | `grep -rnE '\b(sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp)\b' $(find VbmScoreboard VbmScoreboardWire VbmScoreboardProofs -name '*.lean') VbmScoreboard.lean VbmScoreboardWire.lean VbmScoreboardProofs.lean \| grep -v tier1-allow \| grep -c .` | 0, 2026-11-18 | 0 | |
| `axiom-gate-offending-constants` (count; 761 checked) | lower | 6 | `.land/tool/bin/land-lean axiom --selftest` (read the line `N constants checked, M offending`) | 0, 2026-11-18 | 0 | |
| `trust-ledger-gaps` (count of entries with no written contract or no test) | lower | 6 | `.land/tool/bin/land-lean trust` (read `N with no written contract or no test`) | 2, 2026-11-18 | 2 | |
| `build-warnings` (count) | lower | 8 | `for f in $(find VbmScoreboard VbmScoreboardWire VbmScoreboardProofs -name '*.lean'); do lake env lean "$f" 2>&1; done \| grep -ciE 'warning\|error'` | 0, 2026-11-18 | 0 | |
| `import-rule-violations` (count) | lower | 5 | `grep -HnE '^[[:space:]]*((public\|meta\|private)[[:space:]]+)*(import\|prelude)\b' $(find VbmScoreboard -name '*.lean') VbmScoreboard.lean \| grep -vE ':[0-9]+:import VbmScoreboard(\.[A-Za-z0-9_]+)*[[:space:]]*$' \| grep -c .` (core only; the wire layer has its own scan in `scripts/tier1.sh`) | 0, 2026-11-18 | 0 | |
| `core-code-lines` (non-blank, non-comment lines under `VbmScoreboard/`; the verified core) | lower | 5, 10 | `cat VbmScoreboard/*.lean \| grep -vcE '^[[:space:]]*(--\|/-\|$)'` | 113, 2026-11-18 | 113 | |
| `wire-lines` (all lines under `VbmScoreboardWire/`) | lower | 11 | `cat VbmScoreboardWire/*.lean \| wc -l` | 363, 2026-11-18 | 363 | |
| `public-lint-violations` (count of findings) | lower | 9 | `scripts/lint-public \| grep -c .` | 0, 2026-11-18 | 0 | |
| `public-lint-selftest-cases` (count) | higher | 7, 9 | `scripts/test_lint_public.sh \| grep '^ran:'` | 8, 2026-11-18 | 8 | |
| `proof-recheck-seconds` (replay of every proof in a fresh process; well over a minute) | lower | 4 | `.land/tool/bin/land-lean recheck --selftest` (wall clock) | 211, 2026-11-18 | 211 | |
| `slices-landed` (count of S0..S3 marked landed) | higher | 11, 12 | `grep -cE '^- S[0-9] \(landed\)' docs/decisions/0001-vbm-scoreboard.md` | 2, 2026-11-18 | 2 | |
| `release-tags` (count) | higher | 13 | `git tag \| wc -l` | 0, 2026-11-18 | 0 | |
| `tier1-seconds` (wall clock of the whole gate) | lower | 7, 10 | `mise exec -- scripts/tier1.sh` (wall clock) | unmeasured | unmeasured | |

Notes on measurement:
- `tier1-seconds` is `unmeasured`: it needs the toolchain through `mise` (not installable offline here) and a whole Tier 1 run, which the harness runs at landing. Its slowest known part, `proof-recheck-seconds`, is 211 s; the rest ran in under 10 s each (the warm build took about 10 s).
- The wire layer's `#guard` facts (the one trusted fact, that the JSON parser reads back what the compressor writes) are not counted as a metric: no command in the repository counts them apart from the trust ledger.
- The gates already hold floors of their own: `scripts/ledger-baseline.txt` (proved 26, open 0, total 26) is the existing ratchet for the first two rows.
- Direction of `core-code-lines` and `wire-lines` is a guess from goals 5 and 10 (small and pure); the owner may rather want them unconstrained.

## Health today

- **Nothing regressed**: every measured metric is at its floor by construction (first reading), and the ledger gates (26 of 26 proved, 0 open), the axiom gate (0 of 761 constants offending), the zero-warning build and the public lint are all clean.
- **Unmeasured**: `tier1-seconds`, the time of the whole pre-landing gate.
- **Far from where the goals point**:
  - Goal 12 (the command-line tool) has not started: `slices-landed` is 2, and S3 is the only named slice left (S0 is still labelled "this commit" in the decision, which counts it as not landed).
  - Goal 13 (something others can pin): `release-tags` is 0 and `VERSION` is 0.0.0; the README says pre-release.
  - Goal 6: `trust-ledger-gaps` is 2, the toolchain entry and the tools entry have no written contract or no test beyond the tools' own (accepted in the ledger, so a plan exists rather than a defect).
  - Goal 4 is only partly measured: the ledger counts claims, not whether each hypothesis-carrying theorem has a witness (39 witnesses for 60 theorems; theorems without a hypothesis need none, and no command tells which are which).
- **Slow**: `proof-recheck-seconds` is 211, far the longest part of the gate.

## What a steward would do first

1. Make `tier1-seconds` measurable (record the wall clock of the gate on landing) and bank it, because it is the only metric with no reading and goal 7/10 depend on the gate staying cheap.
2. Start slice S3, the command-line tool, to move `slices-landed` from 2 toward 4, since goal 12 is the one the decision names and nothing yet exists for it.
3. Cut a first signed release tag so `release-tags` rises from 0, which is what a consumer needs to pin the library (goal 13); this waits on the owner's word that pre-release is over.

## Questions for the owner

- Targets: every target is blank. What should `proof-ledger-claims-proved`, `theorems`, `slices-landed` and `release-tags` reach, and by when? Are 0 the right targets for `build-warnings`, `forbidden-construct-hits`, `public-lint-violations`, `import-rule-violations` and `axiom-gate-offending-constants` (the repository says "zero warnings", "forbidden", "no", so I take them as 0 but they are yours to set)?
- Is a smaller core or wire layer better (`core-code-lines`, `wire-lines`), or are they just sizes to watch? The repository caps a change at 150 lines, not the total.
- `trust-ledger-gaps`: the ledger accepts both entries (the Lean toolchain, the scripts' tools); is 2 the floor for good, or should a contract and a test be written for them?
- Is there a goal for how much the proofs cover beyond the ledger's own list of claims (for example a witness for every hypothesis-carrying theorem)? The repository requires it (`AGENTS.md:25`) but has no command that counts it.
- A time budget for the gate (`tier1-seconds`, `proof-recheck-seconds`): the repository only says "fast and best-effort" (`AGENTS.md:5`).
- Release: the repository says pre-release and publishes nothing; when is the first tag due, and is a registry in scope? Slice S3 has no stated date or shape.
- A scorecard of the consumers (how many projects keep their scorecard through this library) would serve the stated purpose "lets a manager compare projects" (`README.md:3`) but nothing in the repository measures it.
