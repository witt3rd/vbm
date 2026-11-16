# Factor the code and the validation so that changes overlap as little as possible

Conflicts and wasted validation have one cause: two things that should be independent share a region. Faster machines and smarter schedulers treat the symptom. The cure is in the design, done before any tool: **factor the code, and factor the validation, so that a change touches little and what it touches is read by little.**

Three kinds of overlap, in the order they hurt:
1. **Write overlap.** Two changes edit the same region. They conflict, and the one that loses the race validates again after the base moves.
2. **Read overlap (a hub).** A region that many validations read, or that most tests execute. One edit to it invalidates all of them. In one measured codebase a quarter of all changes edited hub code that about 60% of its test files imported, and no coverage tool could shrink that: a test that really executes the changed function must run.
3. **Aggregate overlap.** A file that every change must edit: a registry, an import list, a manifest, a changelog, a generated index, a running log. It turns every pair of changes into a conflict, and every change into an invalidation of whatever reads the aggregate. In one repository such a file was touched by one commit in seven.

## What to do
- **No file that every change must edit.** Register by adding a file (one entry per file, found by name or generated at build), never by editing a shared list. A generated file that is committed is a conflict by construction: generate it at build or at release, or make its entries separate files.
- **Narrow, single-purpose modules.** Cut by responsibility so a change to one concern does not touch another. A module that most of the code depends on is a hub: measure it, and split it when a change to one of its concerns would not need to invalidate the others. Do not split to look tidy; factoring is by responsibility and the measurement says where.
- **Validation follows the factoring.** One stage per independent unit (a test per file, a suite per module, a proof check per module) with the inputs that unit really reads, never one command that reads the whole tree. The memo and the footprints (`vbm-land`'s validation memo) only reuse what the factoring made separable: a single stage that reads everything reuses nothing.
- **Prefer many tests that exercise little.** A wide test, one that boots or loads most of the system, is expensive forever and invalidated by almost any change. Keep wide tests few, name them as wide, and push the checking down to unit-level tests, specifications and proofs, whose reach is narrow by construction.
- **Measure the overlap and ratchet it.** For every change, the regions it wrote; for every stage, the regions it read. Report the hubs (regions read by more than a given share of stages), the wide stages, and the aggregates (files written by more than a given share of changes). Overlap may fall and may not rise. A repository's throughput ceiling is its overlap.

## The order of resort
Use the cheapest cure first; each later one works better after the earlier:
1. **Factor** (design: remove the overlap).
2. **Schedule** (keys: do not run work with overlapping regions at the same time).
3. **Reuse** (memoize validation whose inputs did not change).
4. **Batch** (validate ready changes together, bisect a failure).
5. **Buy** (bigger or more machines).

Reaching for a later cure while an earlier one is open is how a team ends up with a merge queue in front of a codebase whose every change touches the same three files.

## How to tell it is working
- Concurrent changes land with one attempt each, not several.
- A typical change reruns a small share of the validation, and the share does not grow with the codebase.
- No file appears in more than a small share of commits except by decision.
- Adding a feature adds files; it does not add lines to files that other features also edit.
