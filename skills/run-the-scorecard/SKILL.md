---
name: run-the-scorecard
description: >-
  Run the scorecard on a repo and read the card (Level 1 Certified, Level 2 Measured). Use when asked how a repo scores or why a card fails.
---

# Run the scorecard

Two levels. **Level 1, Certified**: runs none of the subject's code; rechecks the proof export, reads claims, axioms, escapes, symbols, ledgers, history. **Level 2, Measured**: runs the artifact (throughput, mutation, reproducible builds, second compiler) and only inside a sandbox. Design: `scorecard/SPEC.md`.

## Steps (from this repository's root)
1. The subject needs `scorecard.toml` at the commit, or pass `--adapter <file>`.
2. Level 1, nothing executes:
   `mise exec -- scorecard/scorecard run --repo <path-or-url> --commit <full-sha> --out card.json`
3. Level 2, in bubblewrap (needs `bwrap`):
   `mise exec -- scorecard/scorecard run --repo <path> --commit <sha> --sandbox scorecard/sandbox-bwrap --out card.json`
4. Read the card: `verdicts.correctness` first, then `verdicts.landedness` (`pass`/`fail`; `pending` for a card scored before the warm/cold split), then the profile (`verdicts.profile`, in neither verdict); `level` (0, 1 or 2) and `badge`; `dimensions` per ideal (`pass`/`fail`); each metric is `pass`, `fail` or `not-measurable`, with a reason.

## Reading it
- One failed dimension fails its verdict (Correctness, Landedness); the profile (bare metal, efficiency) is in neither; no averaging and no single score. `not-measurable` fails its floor.
- The fast gate is timed twice: `velocity.tier1_seconds_warm` (a landing's cost: floor under 60 s; the adapter's `[tier1] warm_change_cmd` and `warm_command`) and `velocity.tier1_seconds_cold` (a fresh clone, no cache: ceiling at most 600 s). Both are printed.
- The card carries the subject SHA, scorecard SHA, adapter hash and sandbox attestation, and no run timestamp: same inputs, same bytes.

## Do not
- Run a subject's commands outside the sandbox, or add `--sandbox` to an untrusted repo without it being the shipped launcher.
- Hand-edit a card or report a score from a document; only the computed card counts.
- Pass a branch name as `--commit`; use the full SHA.
