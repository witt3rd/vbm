## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Diff ≤150 production lines, ≤45 min without a passing build; over either, stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `.land/land-direct`; never push main yourself, never force-push it, never open a PR.
- New behaviour lands behind a flag that defaults OFF. Interface changes: add beside the old, migrate callers, delete at zero references.
- Everything runs before the push, once (Tier 1 on the rebased tree, fast and best-effort); nothing runs after it. If main is ever red, whoever sees it reverts the offending commit with `git revert` and lands the revert; the author fixes forward in a new worktree. A landing must not add a failure. Before a release the release candidate runs the project's full suite (`LAND_RC_CMD`); fix on main until it is green.
- `.land/tool/` is a pinned copy of vbm-land: never edit it (`.land/tool/bin/land-check` fails the gate). Change the tool upstream, then `.land/tool/bin/land-update <tag>`.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

## Principles (the VBM + HVTBD family)
- Everything runs before the push, once, on the commit rebased onto main. Nothing runs after the push.
- Proofs, not tests. A test exists only for what the proofs do not cover (the boundary), never for the development tooling.
- A failure is a root-cause question, never a reason to add a check, gate, script or document. Nothing is added to the process without deleting something.
- The worker owns its change: when the lander refuses it, the worker fixes it and lands again until it converges.
# AGENTS.md: vbm-scoreboard

A project's scorecard, written once in Lean 4 and machine-checked: a set of named metrics, each with a direction (higher or lower is better), a floor that only ever moves toward better, a target the owner sets, and an append-only history. A check refuses a regression; banking records an improvement and never a worse number; loosening a floor takes an explicit, reasoned reset. Every vbm-* project, and every project that vendors the family, keeps its own scorecard against its own goals; this library is the part they share.

**Scope.** Pure data and total functions over `Init`. No input or output, no wire format, no model call, no network, no storage. It decides whether a floor held and what the history says; it measures nothing (providers measure) and decides nothing about what to build (a steward judges that). The wire formats of the provider protocol and the baseline and history files are a separate library, `VbmScoreboardWire`, which may import `Lean`.

## Status
Seeded 2026-11-18 from the scoreboard specifications of the family's first consumer. Slices (docs/decisions/0001-vbm-scoreboard.md): S0 the skeleton and the direction order; S1 the core (check, bank, reset, history, progress); S2 the wire formats (`VbmScoreboardWire`); planned: S3 the command-line tool.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **Spec first.** Behaviour lands as a specification and its proofs. A theorem with a hypothesis carries a witness that the hypothesis can hold (a theorem whose hypothesis cannot be met is not a theorem).
- **Ran-evidence.** A gate or test that runs zero cases fails: every test script ends with `ran: NAME: N cases` (N > 0) and every concurrent gate reports its own count (`scripts/ran-gates.txt`). A refused tool, a `SKIPPED` line or an early exit is never a pass.
- **Nothing runs after the push.** Everything runs before it, once, in Tier 1 on the rebased tree; there is no workflow and no runner in this repository.
- **Public-ready, always.** No private name, no path of ours, no number of ours, no e-mail anywhere; write generic. Names are kept as hashes (`scripts/public-banned-hashes.txt`).
- **Small diffs** and Conventional Commits; TTL 45 minutes without a passing build: abort and decompose.
- **No secrets in the repository.** No paid model call and no network call from a test or a gate.

## Library rules
- **Module roots:** `VbmScoreboard` imports `Init` and itself only (Tier 1 scans the imports); `VbmScoreboardWire` (the wire formats, linked) imports `Lean`, `VbmScoreboard` and itself only (Tier 1 scans them); `VbmScoreboardProofs` may import `Std` and `Lean` and is never linked, and nothing in `VbmScoreboard` or `VbmScoreboardWire` may import it. **The words of the wire formats are kept exactly once released** (the keys, the version, `higher`/`lower`, `banked`/`added`/`reset`, the refusals): a change to one needs the consumers' word.
- **A metric is a name and an integer.** The unit is the provider's, said in the metric's name (a share in hundredths of a percent, a ratio in permille, a count, a duration in seconds). Nothing here names a project, a language or a vendor.

## Gates
**Tier 1** (`scripts/tier1.sh`): forbidden-constructs scan, import scan, pipefail lint, the vendored lander's drift check, zero-warning build, axiom gate, trust ledger, proof recheck, public-readiness lint, ran-evidence self-tests. It runs before every landing, on the commit rebased onto main.

## Layout
`VbmScoreboard/` spec and code · `VbmScoreboardWire/` the wire formats (linked) · `VbmScoreboardProofs/` proofs and the obligation ledger (never linked) · `docs/decisions/` design · `scripts/` gates, lints and their self-tests, `.land/land.d/` the lander's hooks, the pinned lander.
