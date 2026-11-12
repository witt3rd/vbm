---
name: prove-and-gate
description: >-
  Add a theorem to a VBM library and the gate that guards it: axiom gate, closure gate, negative self-tests, the attack suite.
  Use when adding or changing a proof, a claim, or any gate script.
---

# Prove and gate

## Add a theorem
1. State it in `<Name>Proofs/…lean` about a declared definition of the specification, never about `True`, a reflexive equality, or a hypothesis that can be `False` (non-vacuity).
2. Prove it with no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp`. A hypothesis (a hash is collision resistant) is a theorem argument, never an axiom.
3. Add or update its row in `docs/obligations.md` (`open`, `partial`, `proved`) with the theorem name.
4. `lake build <Name> <Name>Proofs` must pass.

## The gates
- **Axiom gate**: walks every constant of the modules you list and fails on any axiom beyond the standard three (`propext`, `Classical.choice`, `Quot.sound`). The landing tool ships it: list the modules to import and the roots to audit in `.land/lean.conf` (its presence turns the Lean gates on), then run `.land/tool/bin/land-lean axiom [--selftest]` (vbm-land `docs/lean-gates.md`); it prints `axiom gate: N constants checked, M offending`, and M must be 0. A root that matches no constant fails: a gate that audited nothing proves nothing. Write no axiom gate of your own.
- **Proof replay**: `land-lean recheck --selftest` replays every proof of the modules in `LAND_LEAN_RECHECK_MODULES` (`.land/lean.conf`), and of everything they import, with Lean's own checker in a fresh process (`leanchecker --fresh`); `--selftest` first proves the checker rejects a planted false theorem. Say exactly what it is: the same kernel code, so it catches a declaration that bypassed the kernel and an `.olean` an honest build did not produce, not a bug in the kernel (that needs a second implementation, nanoda: not wired).
- **Obligation ledger** (`land-lean ledger`): the claims as Lean data, one `O "slug" (.proved [``Some.theorem])` per claim in a `Ledger.lean` that does `import LandLedger` (the tool ships the vocabulary and the gate; `require «land-ledger» from ".land/tool/lean"` in the lakefile (the tool's package: never declare a library of your own for it, or a repository that vendors yours and requires it too gets an ambiguous `import LandLedger`) and list the module in `.land/lean.conf`: vbm-land `docs/lean-gates.md`). The gate renders `docs/proof-ledger.md` and fails if a named theorem is missing or is not a theorem; a failing ledger renders nothing. Each option is a key: reach (a claim proved only about a model nothing runs is demoted to partial: "proved" means proved about code that runs), the ratchet (proved may only rise), clause tags and their coverage. A Lean ledger replaces the hand-kept `docs/obligations.md` table; a repository uses one or the other.
- **Closure gate**: `lake env lean --run scripts/ClosureGate.lean` prints `specified share P%`; for a library the floor is 100%.

## Negative self-tests (the gate must be seen to fail)
For every gate add `scripts/test_<gate>.sh`: copy a fixture, plant the fault (a `sorry`, an added axiom, a vacuous claim), run the gate, and fail the test if the gate did NOT fail. See `guidelines/gates-need-negative-self-tests.md` and the scripts in this repository's `scripts/test_*.sh`.

## Changing a gate
Nothing waits for an approval and no file is locked: a gate, floor or definition is edited like any other file. A gate change never lands to make a number pass.

## Do not
- Weaken a gate or a floor in the same change that needs it to pass.
- Count a gate as done without its failing fixture.
