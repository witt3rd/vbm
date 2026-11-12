---
name: new-vbm-library
description: >-
  Scaffold a new verified-bare-metal library `vbm-<name>`: spec first, Lean skeleton, scorecard adapter, trust ledger, gates, landing tool.
  Use when starting a new library or turning an idea into a VBM repo.
---

# New VBM library

A library is a pure Lean specification (types, grammar as a relation, reference implementation, fast implementation, theorems), compiled to C and WebAssembly, with a small boundary that only moves bytes. Read `guidelines/spec-first.md` and `guidelines/verified-by-construction.md` first.

## Steps
1. Create the repo `vbm-<name>`; work on a branch in a worktree, never in the primary clone.
2. Write `docs/spec.md` BEFORE any Lean: the inputs, outputs, every named limit, every typed refusal, and one sentence per property to prove. Bytes in, bytes out; time and randomness are inputs; no allocator across the ABI.
3. Lean skeleton: `lake init`, a `<Name>.lean` (spec + code) and a separate `<Name>Proofs.lean` (theorems). Pin the toolchain in `lean-toolchain`.
4. Obligation ledger `docs/obligations.md`: one row per claim, state `open` / `partial` / `proved` (or, once the claims are many, a Lean `Ledger.lean` checked by `land-lean ledger`, which generates `docs/proof-ledger.md`: see the `prove-and-gate` skill). Trust ledger `docs/trust-ledger.md`: one `### T<n>` entry per thing not proved (compiler, runtime, each binding, each vendored library), with an owner and a plan; the landing tool derives what must appear and checks it (`land-lean trust`, configured in `.land/lean.conf`; guideline `mark-what-is-trusted.md`).
5. Gates: the closure gate (specified share) in `scripts/`; the axiom gate comes with the landing tool (list your modules in `.land/lean.conf`; see the `prove-and-gate` skill). Write none of the test-running runtime yourself: the landing tool ships it (step 7).
6. Adapter `scorecard.toml` at the repo root (copy `scorecard/adapters/vbm-json.toml` from this repository and edit; every key is required). Languages appear only in `[proof]`, `[tier1]` and similar tables.
7. Landing: adopt the landing tool (trunk-based, one lander, no pull requests for a single owner: `guidelines/trunk-based-landing.md`) at a signed release of [vbm-land](https://github.com/witt3rd/vbm-land) (its README: `install --signers`). It vendors the tool in `.land/tool/`, including the test runtime, `land-pin` and `land-release`: use them, write none of them (`guidelines/where-things-live.md`).
7a. Dependencies: `.land/tool/bin/land-pin vendor NAME https://github.com/OWNER/NAME.git vX.Y.Z` for each; require them by path (`vendor/NAME`); run `land-pin verify` first in `scripts/tier1.sh` (`guidelines/vendor-and-pin.md`).
7b. Release: put the version in `VERSION`, land it, then `land-release --push` on the host that holds the release key; the first release is `v0.1.0`.
8. Protect main: create the ruleset from `skills/flip-checklist/ruleset-protect-main.json` (`gh api -X POST repos/<owner>/<repo>/rulesets --input <file>`): deletion and non-fast-forward only, no required pull request, no bypass list. The lander never force-pushes. Make the first real landing to prove it still lands.
9. First landing: the spec, an empty-but-building skeleton, the ledgers. Then climb the ladder: relation, reference recogniser, printer and round-trip, fast implementation and refinement, ABI.

## Verify
- `lake build` succeeds; the gates run and print their counts.
- `mise exec -- scorecard/scorecard run --repo <path> --commit <sha>` (from this repository) exits 0 and prints a card, even if it fails.

## Do not
- Write Lean before the spec, or tests by hand (vectors come from the reference).
- Add an axiom, `sorry`, `unsafe` or an `implemented_by` to make something pass; put it in the trust ledger or leave the claim `open`.
- Let the boundary make decisions.
