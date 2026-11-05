# The VBM standard

VBM (verified bare metal) is a standard for building software that is specified and proved in a proof assistant, runs without an operating-system runtime, and is written by coding agents. This page states what it is, what it claims and what it does not.

## The four properties

1. **Verified.** The behaviour of a component is written as a specification in the Lean proof assistant, and the properties that matter are proved against it. The code that runs is the specification, or is generated from it.
2. **Bare metal.** A component builds freestanding: no libc symbols, or a short named list. It carries its own small runtime, so it can run in a browser, a kernel, a microcontroller or a hosted process.
3. **Correct by construction.** Hand-written tests of the component are not the evidence. Tests are generated from the specification, and the checks themselves are tested by mutation: a deliberately broken specification or implementation must be caught.
4. **Agent-built.** Coding agents write the specification, the proofs and the tooling. People are not expected to read every line, so nothing depends on anyone having done so.

## What is measured, in order

The first and most important measure is **correctness**: the verified, bare-metal and correct-by-construction properties and the trusted code generation behind them. The second is **landedness**: how fast and how cleanly changes land (a fast gate, small steps, no open pull requests). Correctness comes first; landedness comes second. They are reported separately: there is no single blended score and nothing is averaged.

## Claims it makes

- A proved property holds for every input the specification covers, as far as the proof assistant's kernel is correct.
- The code that runs was derived from the specification by a recorded, reproducible build, and a second compiler agrees with the first.
- Every number on a component's card was computed by a script from the pinned commit, never self-reported, and anyone can recompute it.
- Everything that is trusted without proof is listed.

## Claims it refuses to make

- It does not claim the specification is the right one. A proof shows the code matches the specification, not that the specification matches what you wanted. The specification is kept small so that a person can read it.
- It does not claim the Lean kernel, the compiler, the hardware or the operating system are free of defects.
- It does not claim a failed card means bad software, or that a passing card means safe software. A card reports what was measured against stated floors.
- It does not claim that a metric the scorecard cannot yet measure has passed. Such a metric counts as a fail.

## The trust budget

Everything that runs outside the proofs is the trusted base: native shims, the runtime, the generators, the toolchain. Each trusted line is named in a ledger, the ledger has a size, and the size is scored. The aim is a small ledger, not a clean conscience. A component that needs more trust must say so on its card.

## Why the checks, not the reviewers

Agent-written code is produced faster than anyone can review it, and review does not scale or repeat. A proof checker, a mutation run and a reproducible build do the same thing every time and can be rerun by anyone. So the process puts its trust in checks, and puts its effort into making the checks themselves honest: every gate has a self-test that has been watched to fail, and an attack suite tries to defeat the gates and the definitions that protect them.

## What a VBM component promises its users

- A specification you can read, and proofs that the code matches it.
- A listed trusted base, with its size.
- A card, with a commit, a sandbox description and the result of each metric, that you can regenerate.
- A build with no libc dependency, from sources and tools that are pinned.
- Changes that land only when the gate is green, in small steps, with a fast gate.

## How to join

The registry lists the repositories we have scored. Anyone may run the scorecard on their own repository and publish the card: Level 1 certifies from a proof export, and nothing of your repository runs. To be listed, open an issue here with the card. Listing without our review waits for the isolation that makes Level 2 (running subject code) safe. See [how to register](skills/register-in-the-registry/SKILL.md) and the [scorecard specification](scorecard/SPEC.md).

## License

License: Apache-2.0 (see [LICENSE](LICENSE)).
