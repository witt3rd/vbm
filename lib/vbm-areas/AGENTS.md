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
# AGENTS.md: vbm-areas

which declared areas a change touches, where areas overlap, and when a landing's verdict can be reused: the pure selection logic of a landing, specified and proved.

**Scope.** Pure data and total functions over `Init`: no input or output, no network, no storage, no model call. A wire layer, if the library needs one, is a separate sibling library that may import `Lean`. It decides what its specification says and nothing else; a boundary only moves bytes.

## Status
Seeded 2026-11-21 by `bin/new-vbm-lib` (S0: the skeleton and one proved claim). The first slice item writes `docs/spec.md` BEFORE any Lean (the inputs, the outputs, every named limit, every typed refusal, one sentence per property to prove), then the specification, the proofs and the ledger.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **Spec first.** Behaviour lands as a specification and its proofs. A theorem with a hypothesis carries a witness that the hypothesis can hold.
- **Ran-evidence.** A gate or test that runs zero cases fails: every test script ends with `ran: NAME: N cases` (N > 0).
- **Nothing runs after the push.** Everything runs before it, once, in Tier 1 on the rebased tree.
- **Public-ready, always.** No private name, no path of ours, no number of ours, no e-mail anywhere; write generic.
- **Small diffs** and Conventional Commits; TTL 45 minutes without a passing build: abort and decompose.
- **No secrets in the repository.** No paid model call and no network call from a test or a gate.

## Library rules
- **Module roots:** `VbmAreas` imports `Init` and itself only (Tier 1 scans the imports); `VbmAreasProofs` may import `Std` and `Lean` and is never linked.
- **Core first, then the family.** Before defining a type or a function, check Lean's core and `Std` (`Rat`, `List.mergeSort` with its lemmas, `Std.Time`, the `List` lemmas): USE what exists and prove only what is missing on top. A general thing the family already has is DEPENDED on (vendored, pinned), never redefined; if you must write a general thing first, mark it `incubating: candidate vbm-NAME` in its docstring. A general thing defined in a second repository is a defect (the rule of two).

## Layout
`VbmAreas/` spec and code · `VbmAreasProofs/` proofs and the obligation ledger (never linked) · `docs/` the specification and decisions · `scripts/` gates, lints and their self-tests · `.land/` the pinned lander.
