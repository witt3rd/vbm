# VBM guidelines: building verified bare-metal software that agents write and nobody reviews line by line

One idea per file. The scorecard (`../scorecard/SPEC.md`) measures how well a repo follows them.

Verified by construction
- `verified-by-construction.md`: the code that runs is the specification, or derived from it.
- `trusted-base-is-a-budget.md`: count what runs outside your control and keep it small.
- `mark-what-is-trusted.md`: what cannot be proven is marked as trusted, and what must be marked is derived from the tree.
- `boundary-never-decides.md`: code at the edge moves bytes; it does not choose.
- `logic-lives-in-the-spec.md`: decisions are in the specification; scripts only bind ports.
- `no-decisions-from-text.md`: a decision comes from typed data or a model's typed answer, never from matching a string.
- `decision-kinds.md`: every decision point is decidable, judgmental or probabilistic, and the kind fixes the evidence it must meet.
- `spec-first.md`: the specification lands before the implementation.
- `gates-need-negative-self-tests.md`: a gate that cannot fail is a label.

Generating code
- `write-once-generate-many.md`: one verified core, artifacts in every other language.
- `generated-code-is-checked-independently.md`: reproducible builds, lineage, a second compiler.
- `tests-from-the-spec.md`: vectors are generated; hand-written tests are the exception to explain.
- `efficiency-is-a-budget.md`: measure it, ratchet it, second to correctness.

How we land
- `trunk-based-landing.md`: a small change reaches main in minutes and the push is best-effort; a declared release candidate runs the full suite and is fixed until green before a release.
- `choose-the-landing-mechanism.md`: three questions pick direct landing or a queue.
- `fast-gate-small-changes.md`: the gate's speed and the change's size are the throughput ceiling.
- `factor-for-disjointness.md`: factor the code and the validation so changes overlap little; factor, then schedule, then reuse, then batch, then buy.
- `single-lander.md`: one writer, the gate on the exact combination, a plain fast-forward push.
- `revert-first.md`: a red main is reverted, then debugged.
- `no-pull-requests-for-a-single-owner.md`: when the pull request is ceremony and when it is not.

Depending and releasing
- `vendor-and-pin.md`: one way to take a dependency (vendor a signed release, lock it, verify it) and to release.
- `where-things-live.md`: one layout convention, the habits other ecosystems use.
- `code-placement.md`: the language's core first, then the family's libraries, then the product; a general thing defined twice is a defect.
- `library-design.md`: a library is a concept with one purpose sentence; extend before you create; tiers, naming, the set, the incubator, and a placement battery that fails closed.
