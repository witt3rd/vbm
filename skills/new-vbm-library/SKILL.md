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
4. Obligation ledger `docs/obligations.md`: one row per claim, state `open` / `partial` / `proved`. Trust ledger `docs/trust-ledger.md`: one `### T<n>` entry per thing not proved (compiler, runtime, each binding), with an owner and a plan.
5. Gates in `scripts/`: a closure gate (specified share), an axiom gate (see the `prove-and-gate` skill), and a `scripts/test_*.sh` negative self-test for each.
6. Adapter `scorecard.toml` at the repo root (copy `scorecard/adapters/vbm-json.toml` from this repository and edit; every key is required). Languages appear only in `[proof]`, `[tier1]` and similar tables.
7. Landing: adopt the landing tool (trunk-based, one lander, no pull requests for a single owner: `guidelines/trunk-based-landing.md`).
8. Protect main: create the ruleset from `skills/flip-checklist/ruleset-protect-main.json` (`gh api -X POST repos/<owner>/<repo>/rulesets --input <file>`): deletion and non-fast-forward only, no required pull request, no bypass list. The lander never force-pushes. Make the first real landing to prove it still lands.
9. First landing: the spec, an empty-but-building skeleton, the ledgers. Then climb the ladder: relation, reference recogniser, printer and round-trip, fast implementation and refinement, ABI.

## Verify
- `lake build` succeeds; the gates run and print their counts.
- `mise exec -- scorecard/scorecard run --repo <path> --commit <sha>` (from this repository) exits 0 and prints a card, even if it fails.

## Do not
- Write Lean before the spec, or tests by hand (vectors come from the reference).
- Add an axiom, `sorry`, `unsafe` or an `implemented_by` to make something pass; put it in the trust ledger or leave the claim `open`.
- Let the boundary make decisions.
