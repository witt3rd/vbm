# 0001: vbm-areas

Status: accepted (2026-11-21).

## Why
Which declared areas a change touches, where areas overlap, and when a landing's verdict can be reused: the pure selection logic of a landing, specified and proved.

## Decision
Specify the selection logic in Lean, as a pure library, instead of leaving it in the script that implements it. The tool that applies it is a script: it reads a file, asks the version-control system for the changed paths, runs commands. Its decision logic (which areas a change touches, which paths are unowned, what a moved trunk invalidates) is small, total and easy to get subtly wrong at the edges (a rename, a deleted path, a tie between areas, a root glob). A script cannot state that logic and prove its properties; a specification can. So:

- The contract is `docs/spec.md`, written before any Lean; the Lean states it exactly, and theorems prove its properties (a change never misses an owner; an unmapped path forces the full suite; reuse never reuses what moved).
- The library has no input or output and no parsing. The script keeps the boundary; the library keeps the decision.
- The script is checked against test vectors generated from the library, case by case, so the two cannot drift without a failing check.
- Nothing narrower than "every step of every touched area" is ever selected (no import graph, coverage, name or size). Anything uncertain fails toward running more.
- Landing throughput is a non-goal: it is a probability model, kept for a later, separate library.

## Consequences
- A change to the selection rules is a change to the specification and its proofs first, then to the script.
- The library is public-family: generic, no names of products, people or machines.

## Slices
- S0: the skeleton and one proved claim.
- S1: `docs/spec.md` and this decision (documentation only).
- S2: the glob language, its matcher and refusals.
- S3: the areas value, its refusals, `owns`, enclosure and closest.
- S4: `decide`.
- S5: the reuse decision, the report, and the vectors.
