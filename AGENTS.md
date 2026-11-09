## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Diff ≤150 production lines, ≤45 min without a passing build; over either, stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `.land/land-direct`; never push main yourself, never force-push it, never open a PR.
- New behaviour lands behind a flag that defaults OFF. Interface changes: add beside the old, migrate callers, delete at zero references.
- Everything runs before the push, once (Tier 1 on the rebased tree); nothing runs after it. If main is ever red, whoever sees it reverts the offending commit with `git revert` and lands the revert; the author fixes forward in a new worktree. A landing must not add a failure.
- `.land/tool/` and `.land/land-direct` are a pinned copy of vbm-land: never edit them (`.land/tool/bin/land-check` fails the gate). Change the tool upstream, then `.land/tool/bin/land-update <tag>`.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

## Principles (the VBM + HVTBD family)
- Everything runs before the push, once, on the commit rebased onto main. Nothing runs after the push.
- Proofs, not tests. A test exists only for what the proofs do not cover (the boundary), never for the development tooling.
- A failure is a root-cause question, never a reason to add a check, gate, script or document. Nothing is added to the process without deleting something.
- The worker owns its change: when the lander refuses it, the worker fixes it and lands again until it converges.

# AGENTS.md

The standard is VBM (verified bare metal); the method this repo describes is agentic (software that agents write). Libraries that follow it are `vbm-<name>`. One repository, three parts, kept together so they cannot drift:
- `guidelines/`: the published best practices for agent-built, verified-by-construction software (small files, one idea each).
- `scorecard/`: the evaluator. It scores any submitted repo against the seven ideals, from one adapter file in that repo, and writes ONE JSON. `scorecard/SPEC.md` is the design, `scorecard/DECISIONS.md` the owner's decisions.
- `registry/`: the list of scored repos, one entry file per repo.
The repository name is set in `project.toml`; `scripts/lint-public` flags any retired name. Public (published from a fresh history; the earlier development history is archived privately): the lint below runs on the whole tree. `README.md` is the human front door (the no-README house rule is about agent indexes; this file stays the agent file). Its registry table is GENERATED from `registry/*.toml` and their cards by `scorecard/registry-table`: never edit it by hand (`--write README.md` regenerates it; Tier 1 fails on drift).
The score is computed by scripts from the tree, the build and the git history, never self-reported.

## The seven ideals (the dimensions of the card; floors from `scorecard/DECISIONS.md` 1, no averaging)
1. **Verified**: specified share, no unproved escapes, trusted native code and trust-ledger size, non-vacuity.
2. **Bare metal**: freestanding build, no libc symbols, size, allocations.
3. **Correct by construction (unit-test free)**: hand-written tests 0, mutation score, differential agreement, fuzz.
4. **Trusted code generation**: reproducible builds, generator lineage, a second compiler.
5. **Resource efficiency**: throughput against comparators, memory, latency, scaling.
6. **Velocity** (landedness): warm fast gate under 60 s, cold fast gate at most 600 s, 0 open PRs, commits per hour, p90 commit-to-main.
7. **Process honesty**: every gate has a negative self-test; an attack suite; the definitions themselves are protected.
A dimension below its floor fails its verdict: the card has TWO verdicts, **Correctness** (ideals 1, 3, 4, 7) first and **Landedness** (ideal 6) second, then a profile (ideals 2 and 5) in neither; no blended score. A metric is `pass`, `fail` or `not-measurable`; `not-measurable` fails its floor. Metrics the runner does not implement yet, and metrics that must execute subject code while no sandbox
is configured, are `not-measurable` with the reason named, so a verdict is `fail` until they are implemented and measurable.

## How to run
- `mise exec -- scorecard/scorecard run --repo <path> --commit <sha> [--adapter <file>] [--out <file>] [--sandbox <launcher>]`: clones the pinned commit to a scratch dir (the subject is only read), prints one JSON. The adapter defaults to
  `scorecard.toml` at the pinned commit; `scorecard/adapters/` holds adapters for subjects that have none yet. `--sandbox scorecard/sandbox-bwrap` runs the executing metrics inside bubblewrap (needs `bwrap`). Without `--sandbox` NOTHING of the subject executes (`scorecard/SPEC.md`, "Untrusted subject code").
- Gate before landing: `mise exec -- scripts/tier1.sh` (runs every `scripts/test_*.sh`; a test not declared with `par` fails it, and the public-readiness lint runs in it).
- Land: `.land/land-direct` (commit on a branch in a worktree, then run it: fetch, rebase, local Tier 1, fast-forward push to main). `--dry-run` pushes nothing.

## Rules
- Everything runs as `mise exec -- ...`. No secrets in the repo. No paid model calls from a test or a gate.
- **Public-ready, always.** No private name, no path of ours, no number of ours anywhere: `scripts/lint-public` fails Tier 1 on them (names are kept as hashes in `scripts/public-banned-hashes.txt`). Write generic ('the subject repo', 'a worker host'). This history starts at the public flip: never import an earlier private history.
- **The subject is untrusted code.** The runner executes nothing of it outside the sandbox contract; static metrics read only files the adapter declares, through one guard (no symlinks, no `..`, size-capped). Never weaken either to make a metric pass.
- **The rubric is toolchain-neutral.** A metric's definition names no language; language-specific commands and patterns live only in the adapter (`[proof]`, `[tier1]`, ...). The adapter `scorecard.toml` is the submission contract.
- **No pull requests, except one place:** a contribution to `registry/` is a PR (external contributors; `scorecard/SPEC.md`, "Registry and contribution flow"). Everything else lands with `.land/land-direct` only; never push to main by hand, never force-push. Main is green (Tier 1) at every commit. Conventional Commits `type(scope): summary`; about 150 production lines per landing.
- **Every metric has a negative self-test** in `scripts/test_scorecard.sh`: a fixture shown to fail it (a planted placeholder is counted, a missing adapter key is rejected, a fixture below its floor FAILS the card). A metric without one does not land.
- **Metric definitions, floors, the adapter schema and the gates are never changed to make a number pass.** Nothing waits for an approval: a change lands when Tier 1 passes.
- Same pinned commits, same bytes out: the JSON carries the subject SHA, the scorecard SHA, the adapter hash and the sandbox attestation, and no timestamp of the run.
- Never walk network mounts. The scheduled series runs on one pinned worker host with no other load, never on a maintainer workstation.

## Later
- **GitHub Pages: not now.** At about 20 registry entries, or when filtering is wanted, add a static page generated from the SAME files (`registry/*.toml` and their cards): a second render, never a second source.
- **License:** Apache-2.0 for code, tooling and the guidelines text (see `LICENSE`).

## Layout
`guidelines/` published practices · `scorecard/` the runner (Python, stdlib only), `SPEC.md`, `DECISIONS.md`, `adapters/` · `registry/` entries and scores (`scorecard/registry-validate` checks an entry or a contribution PR) · `scripts/` the process and the self-tests (`land-direct`, `tier1.sh`, `lint-public`, `sandbox-conformance.sh`, `test_*.sh`) · `project.toml` the name.
