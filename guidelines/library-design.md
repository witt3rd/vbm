# Library design: a cohesive family of few libraries

**A library is a concept with one purpose sentence; the family stays a few libraries that each own one concept, with dependencies pointing one way down the tiers.** `code-placement.md` says where a definition goes. This guideline says what a library is, when a new one may exist, and how the placement is decided. The evidence is the study of other ecosystems (`docs/ecosystems.md`): what lasts is cohesion by concept, a small closed foundation, a named place for the unstable, and a set released together; what fails is the grab-bag, the micro-package and the second foundation.

## Principles

- **A library is a CONCEPT.** It has ONE purpose sentence that does not contain "and" and does not say who uses it. If the sentence needs a conjunction, it is two libraries or one badly named.
- **Extend before you create.** A new module in an existing library is cheap; a new library costs a repository, a release, a pin and a gate in every consumer.
- **No grab-bag.** A thing that fits no purpose is either specific to a product or a new concept. It is never put in "core" because it is used a lot.
- **A closed-scope foundation.** The more a thing is imported, the smaller and more closed it is. Admission to it changes the purpose sentence or shows that the sentence already covers the thing, and its size has a recorded ceiling that only a stated change raises.
- **Dependencies point one way, down the tiers.** No cycle, and no library imports a product.

## The tiers

| Tier | Holds | Depends on |
|---|---|---|
| 0 | The language's core and standard library (not ours) | nothing |
| 1 | The foundation: the few concepts every library needs | tier 0 |
| 2 | Exact numerics and probability | tiers 0 and 1 |
| 3 | Codecs, protocols and algorithms | tiers 0 to 2 |
| 4 | The harness: machines and assemblies that use the libraries | any lower tier |

A product sits above all of them. The tool that lands changes sits beside the tiers and is a run-time dependency of none. The declared tier of each dependency is lower than or equal to the library's own: a gate can check it.

## Naming

Name a library by the concept it defines, never by the role it plays for others. Refused as the whole or main word of a library or a module: `util`, `common`, `base`, `core`, `misc`, `helpers`, `shared`, `lib`. A word on this list may be used only when the purpose sentence defines it as a closed concept. The test: write what the library IS in one sentence without "and" and without naming a user.

## The set and the incubator

- **The set.** A set is a versioned manifest of mutually compatible pins (tag, commit and tree hash of each member, and the toolchain version), vendored as one (`vendor-and-pin.md`). It is released only when every member builds and passes its gate together at exactly those pins, with one version of each library. A new release of a member enters the next set only if the set still holds.
- **The incubator.** A thing is born in its first consumer, marked in its docstring as a candidate library, and extracted at its first stable point. Where a second repository already uses it, it may be a library with `status = incubating`: a weaker promise about interface stability and review only, depended on by tier 2 and above, pinned exactly, and given a date by which it graduates, merges or retires. The truth contract is not weakened.

## Retirement

Pins keep old versions buildable, so retiring is cheap and is done early. A library is retired by a registry status with a replacement or a reason, a dated deprecation kept for a stated number of set releases, then removal from the set. Triggers a gate can see: no consumer in the set, no release in a stated period, a set build nobody fixed, the same purpose sentence as another library.

## The placement battery

Before a definition is written, a small battery of typed questions is answered, and the answers decide the placement. A DECIDABLE answer comes from code (`decision-kinds.md`). A JUDGMENTAL answer comes from a person or a decision model as a typed probability, never as prose. Weighted, the answers give a score per outcome; the outcome is one of `use-core`, `extend-LIBRARY`, `new-library`, `incubate`, `specific`, or `abstain`.

| Kind | Question | What it decides |
|---|---|---|
| **K** core | Does the language's core or standard library already cover it? A search (decidable) and then a judgment on whether the match is enough | Yes: `use-core`, and only the missing part is proved on top |
| **G** generality | Would another product use it unchanged? How free is it of product vocabulary (judgmental)? How many repositories need it now (count)? Does the public lint pass (decidable)? | A high score makes it family code; two consumers and a pass make a library possible |
| **C** consolidation | Which existing library's one-sentence purpose already includes it (judgmental)? Does it import only what that library imports (decidable)? Does adding it keep the sentence true (judgmental)? Does it change together with that library (history, decidable)? | A high score for one library: `extend-LIBRARY` |
| **D** dumping-ground guard | Is the name a concept and not a refused word? Is the purpose one sentence with no conjunction? Would it be an orphan module (imported by nothing in its library)? (all decidable) | A new library is created only if the guard passes |
| **S** stability | Will its interface still change weekly (judgmental, from the history and the author's answer)? | An unstable general thing is incubated, not extracted |

### The order in which the answers decide

1. K stops it: if the core covers it, `use-core`.
2. A high C score for one library: `extend-LIBRARY`.
3. A high G score, at least two consumers and a passing D guard: `new-library`, if S says stable.
4. A high G score with an unstable S, or fewer than two consumers: `incubate`.
5. Otherwise `specific`: it stays in the product.

**Fail closed.** A missing, malformed or middling answer, a judgment below its threshold, or two outcomes too close to separate gives `abstain`, and an abstention goes to a person. Nothing defaults to a placement.

### Whose data the numbers are

The weights and the thresholds are the owner's data, not this page's. They are calibrated on a labelled sample of past placement decisions and recorded with it; a threshold chosen for one decision model does not transfer to another. The judgmental answers start in SHADOW: the model answers beside a person, its answers are logged and compared with the person's, and it decides nothing until its measured agreement meets the owner's bar. The decidable answers are gates, each with a negative self-test (`gates-need-negative-self-tests.md`).

## Failure modes

- **A role name wearing a concept's coat.** `core` or `base` accepted because the word is common elsewhere. Only a closed purpose sentence makes it a concept.
- **A micro-library.** A few theorems with one consumer cost a release, a pin and a gate. Incubate them.
- **Granularity by flags.** Options that multiply the cases to prove. Use modules that can be imported alone.
- **A second foundation.** The foundation leaves a gap, a product fills it, and two copies of one concept exist. Name what to use instead where the foundation's scope stops.
- **A battery nobody checked.** Weights chosen by hand and never compared with real decisions are a guess with a number.

## What this does not claim

It does not say how many libraries is right; it says each needs a concept, a purpose sentence and, to be new, a second consumer. It does not give the weights or thresholds, and no battery answer is a verdict while it is in shadow. It does not say the decidable checks find every duplicate: a renamed or differently typed copy is invisible to them, and a conjunction in a purpose sentence can be innocent. The study behind it was written from memory, and its claims about other ecosystems are structural, not verified quotations.
