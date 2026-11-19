# 0001: vbm-rng

Status: accepted (2026-11-18).

## Why
Deterministic, splittable pseudo-random generators with specified streams: the same seed always gives the same bytes, and exactly reproducible sampling primitives (uniform integers in a range, uniform fractions in exact arithmetic) for simulation and experiments.

## Slices
- S0: the skeleton and one proved claim (this commit).
- S1: docs/spec.md, then the specification, its proofs and the ledger.
