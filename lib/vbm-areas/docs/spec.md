# vbm-areas: specification

Status: the contract of the library (slice S1, written before any Lean). Slices S2 to S5 implement it. Where the Lean differs from this page, the page is amended in the same landing as the Lean.

## What it is
Which declared areas a change touches, where areas overlap, and when a landing's verdict can be reused: the pure selection logic of a landing, specified and proved. The library models a published contract (the glob language, the areas file, the selection rules); a tool that implements the contract is checked against test vectors produced from this library, case by case.

## Scope
Modelled (pure data and total functions over `Init`; no input or output, no clock, no randomness):

1. The **glob language** and its matcher (`*`, `?`, literal), the **refusal** of malformed patterns and working directories.
2. The **validated areas value** (ordered areas, each with a name, path globs, exclude globs and steps) and the typed **refusals** of an invalid one.
3. **`owns`**: when an area owns a path.
4. **The directory a glob starts in**, **`encloses`**, and the **closest enclosing** areas.
5. **`decide`**: from a configuration and a list of changes to a `Decision` record (touched, unmapped, full, run, steps, skipped).
6. The **reuse decision** between a validated landing and a moved trunk.
7. The **report**: overlaps, unmapped paths, stepless areas, and three counts.

Not modelled (each is a boundary or another library's work):

- JSON and any other wire form. The library takes the validated value; a wire layer is a separate sibling library. The refusal type has constructors for the wire-level faults (unknown key, missing `steps`, a step with no `run`) so one type names every refusal, but the library itself only produces the others.
- The version-control system: how changed paths are listed, how renames are detected, how tracked paths are listed. The library receives them as lists.
- Running steps, their exit codes, their output, their timeouts.
- Landing throughput and the concurrency arithmetic (see Non-goals).

## Conventions
- A path or a pattern is a `String`; the working form is its `toList : List Char` (`String` operations such as `splitOn` and `toNat?` do not reduce under `decide`). `abbrev Chars := List Char`.
- A path is relative, has no leading `./`, and is compared case-sensitively. A segment is a maximal run of non-`/` characters.
- Every function is total and structural (or has explicit fuel with a theorem that the fuel suffices). Lists that are reported are in a stated order: file order for areas, a stated total order (code point, lexicographic) for paths, duplicates removed.
- The pseudo-area `inert` is a name, reserved: no declared area may use it.

## The glob language

```lean
abbrev Chars := List Char
/-- `globMatch pat path`: `*` = any run of characters including `/` (and the empty run),
    `?` = exactly one character, everything else literal. The whole path must match. -/
def globMatch : Chars → Chars → Bool
```
`**` is two stars: the same as one. No brackets, braces, negation or escape exists. The matcher is a structural recursion over the pattern, with the star case recursing over the path (fuel: the path length plus one, proved sufficient).

```lean
inductive GlobRefusal where
  | empty | forbiddenChar (c : Char)   -- one of [ ] \ { }
  | leadingSlash | leadingDotSlash | trailingSlash | doubleSlash | dotDotSegment
  | wildcardInCwd                        -- cwd only: contains * or ?

def checkGlob : Chars → Option GlobRefusal   -- none = accepted
def checkCwd  : Chars → Option GlobRefusal   -- the same shape rules, and no `*` or `?`
```
A pattern is refused when it contains `[`, `]`, `\`, `{` or `}`; is empty; starts with `/` or `./`; ends with `/`; contains `//`; or has a `..` segment. A `cwd` is a literal directory: the same shape rules and no `*`, `?`.

## The areas value and its refusals

```lean
structure Step where   (run : String) (cwd : Option String)
structure Area where   (name : String) (paths exclude : List String) (steps : List Step)
abbrev Areas := List Area            -- ordered: the order steps run in

inductive AreasRefusal where
  | badVersion (v : Nat) | noAreas
  | badName (area : String) | reservedName | duplicateName (area : String)
  | emptyPaths (area : String)
  | badGlob (area : String) (g : String) (why : GlobRefusal)
  | badCwd (area : String) (cwd : String) (why : GlobRefusal)
  | emptyRun (area : String)
  | unknownKey (where_ : String) | missingSteps (area : String)   -- raised by the wire layer only

def validName : Chars → Bool          -- [a-z0-9][a-z0-9_-]*
def validate (version : Nat) (areas : List Area) : Except AreasRefusal Areas
```
`validate` accepts exactly: version `1`; `areas` non-empty; every name matches `[a-z0-9][a-z0-9_-]*`, is not `inert`, and is unique; every `paths` non-empty; every glob of `paths` and `exclude` accepted by `checkGlob`; every `cwd` accepted by `checkCwd`; every `run` non-empty. It refuses the first fault in file order, naming the area. `exclude` may be empty; `steps` may be empty (a stepless, "inert" area). Nothing is half read.

## `owns`, the directory of a glob, `encloses`

```lean
def Area.owns (a : Area) (p : Chars) : Bool :=
  a.paths.any (fun g => globMatch g.toList p) && !a.exclude.any (fun g => globMatch g.toList p)

def segments : Chars → List Chars                -- split on '/'
def globDir : Chars → List Chars
```
`globDir g` is the segments of `g` before the first segment containing `*` or `?`, the last segment (the file part) never counting: `src/lib/*` starts in `src/lib`; `core/*.py` in `core`; `docs/*/index.md` in `docs`; `README.md` and `*.md` in the root (the empty list).

```lean
def Area.encloses (a : Area) (p : Chars) : Bool    -- not excluded, and under some glob's directory
def Area.enclosingDepth (a : Area) (p : Chars) : Option Nat   -- the longest such directory, in segments
```
`a.encloses p` holds when no `exclude` glob matches `p` and, for some glob `g` of `a`, `globDir g` is a non-empty, proper, whole-segment prefix of `segments p`. A glob that starts in the root encloses nothing. Prefix is by whole segments: `core/io` does not enclose `core/iodata.json`.

```lean
def closest (areas : Areas) (p : Chars) : List Area
```
The areas that enclose `p` with the longest directory (by segment count); all areas that tie are returned, in file order; the empty list if none encloses `p`.

## `decide`

```lean
inductive Status where | added | modified | deleted
structure Change where (status : Status) (path : String) (renamedFrom : Option String)   -- a rename: `renamedFrom = some old`

structure Config where
  areas : Option Areas          -- none: no areas file, the implicit area `all`
  implicitSteps : List Step     -- the gates command, then the test command (used when `areas = none`)
  inert : List String           -- the older inert patterns (globs)
  protected : List String       -- the protected list (globs)

structure Decision where
  full : Bool
  touched : List String         -- area names in file order, `inert` last if declared and touched
  unmapped : List String        -- paths with no owner and no enclosing area, in input order
  gateDefining : List String    -- paths under `.land/` or matching a protected glob
  run : List String             -- area names in file order (`inert` last when declared)
  steps : List Step             -- of `run`, in file order, a repeated (cwd, run) once
  skipped : List String         -- every area not in `run`

def Change.split : Change → List Change   -- a rename ↦ [deleted old, added p]; the decision splits every change
def decide (cfg : Config) (changes : List Change) (releaseCandidate : Bool) : Decision
```
Meaning, exactly the reference algorithm. `changes := splitRenames changes`; `full := releaseCandidate`. For each `(status, p)`: if `p` is under `.land/` or matches a protected glob, `full := true` and `p` is gate-defining. `owners` := every area that owns `p`, plus `inert` if `p` matches an inert glob and `status ≠ D`. If `owners` is non-empty they are touched and the path is done. Else, if `p` is gate-defining, the path is done (it is never unmapped). Else the areas `closest cfg.areas p` are touched when non-empty; when empty `p` is unmapped and `full := true`. `run` is every area (and `inert`, if declared) when `full`, else `touched`. `steps` is the steps of the areas in `run` in file order, a step repeated by `(cwd, run)` kept at its first occurrence. `skipped` is every area not in `run`.

With no areas file there is one implicit area `all` that owns every path with `implicitSteps` as its steps; an inert pattern carves a non-deleted path out of `all` (that path is owned by `inert` only). A deleted path matching an inert pattern is still owned by `all`.

A landing whose `run` has no step runs nothing and says so: `Decision.stepless : Bool := steps = []` (never a bare green).

## The reuse decision

```lean
structure Reuse where
  reused : List String          -- areas of `mine` whose verdict on the old base stands
  rerun : List String           -- every other area of `mine` that has steps

def reuse (cfg : Config) (mine moved : Decision) (passed : List String) : Reuse
```
`mine` is the decision of the validated landing (made on base B1), `moved` the decision of the paths the trunk changed between B1 and B2, `passed` the names of the areas of `mine` that ran and passed. If `mine.full`, nothing is reused: every area with steps reruns. If `moved.full`, everything of `mine` reruns. Otherwise an area of `mine.run` with steps that is in `passed` and not in `moved.touched` is reused, and every other area of `mine.run` with steps reruns. An area with no steps is neither rerun nor reused. Reuse only ever fails toward running.

## The report

```lean
structure Overlap where (a b : String) (paths : List String)   -- a < b by name, paths sorted, distinct
structure Report where
  overlaps : List Overlap
  unmapped : List (String × List String)   -- (path, enclosing area names); [] = UNMAPPED
  stepless : List String
  areasInOverlap : Nat
  pathsInOverlap : Nat
  unmappedCount : Nat

def report (cfg : Config) (tracked : List String) : Report
```
(a) every pair of areas (`inert` counts, if declared) that both own some tracked path, in name order, with the sorted paths they both own; a path in three areas appears under each of the three pairs. (b) every tracked path no area owns, with the areas that enclose it; gate-defining paths are not listed. (c) the areas with no steps. Counts: `areasInOverlap` is the number of distinct areas in some overlap; `pathsInOverlap` is the number of distinct paths in some overlap; `unmappedCount` is the length of the unmapped list (every entry, including those with enclosing areas, is counted: they are paths no area owns).

## Theorems the library will prove
Each has a statement, and, when it has a hypothesis, a non-vacuity witness: a concrete `example` closed by `decide`, `decide +kernel` or `simp`, showing the hypothesis can hold. A theorem is re-read against this page: the last words of each line say what it rules out.

### Glob (S2)
1. **Total and decidable.** `globMatch` is a total function into `Bool`; `globMatch pat path = true` is decidable and the fuel version equals the structural one. Rules out a matcher that diverges or has no answer. Witness: `globMatch "a*c" "abc" = true` and `= false` for `"abd"`, by `decide`.
2. **Star matches the empty run and `/`.** `globMatch ('*' :: pat) p` holds whenever `pat` matches some suffix of `p`; in particular `globMatch "*" []` and `globMatch "*" "a/b"` hold; `**` matches what `*` matches. Rules out a star that needs a character or stops at a slash. Witness: `"src/*"` matches `"src/a/b.c"`.
3. **`?` matches exactly one character.** `globMatch ('?' :: pat) (c :: p) = globMatch pat p`, and `?` never matches the empty path. Rules out `?` as optional or as many. Witness: `"a?c"` on `"abc"`, not on `"ac"`.
4. **A literal pattern matches only itself.** If the pattern has no `*` and no `?`, `globMatch pat p = true ↔ p = pat`. Rules out a literal that matches a prefix, a case variant or a neighbour. Witness: `"README.md"` on itself, not on `"readme.md"`.
5. **Case-sensitive, whole path.** Corollary of 4 and the definition; no partial match. Witness: `"a"` does not match `"ab"`.
6. **Refusal predicate.** `checkGlob g = none ↔` `g` is non-empty, has none of `[ ] \ { }`, does not start with `/` or `./`, does not end with `/`, has no `//`, and has no `..` segment; `checkCwd c = none ↔ checkGlob c = none ∧` no `*`, no `?`. Rules out an accepted pattern that the contract refuses, and a refused one it accepts. Witnesses: `src/*.py` accepted; each of the seven shapes refused, one `example` each.
7. **A refusal is stable under the language.** An accepted pattern contains no character that `globMatch` treats other than as star, query or literal (no escape, no class). Witness: `"a.b"` is accepted and `.` is literal.

### Areas value and `owns` (S3)
8. **`validate` is exact.** `validate v as = ok as ↔` the version is 1, `as` is non-empty, names are valid, not `inert`, unique, `paths` non-empty, every glob and cwd accepted, every `run` non-empty; otherwise it returns the refusal of the first fault, naming the area. Rules out a half-read value and an unnamed refusal. Witness: a two-area value validates; one example per refusal constructor the library produces.
9. **`owns` is exactly the rule.** `a.owns p = true ↔ (∃ g ∈ a.paths, globMatch g p) ∧ ¬ ∃ x ∈ a.exclude, globMatch x p`. Rules out an exclude that does not win, and an owner by `exclude` alone. Witness: `src/*` with exclude `src/gen/*` owns `src/a.c`, not `src/gen/b.c`.
10. **Deleted paths match like any other.** `owns` does not mention status. Witness: a deleted `src/a.c` is owned like an added one.
11. **`globDir`.** The five examples above (`src/lib/*`, `core/*.py`, `docs/*/index.md`, `README.md`, `*.md`) evaluate as stated; `globDir` is a prefix of the segments of the glob and never includes the last segment.
12. **Enclosure is by whole segments.** `encloses` implies the glob directory is a segment prefix of the path's segments; `core/io` does not enclose `core/iodata.json` (witness: an area with glob `core/io/*`) and does enclose `core/io/x.json`.
13. **A root glob encloses nothing.** If every glob of `a` has `globDir = []`, then `a.encloses p = false` for every `p`. Witness: `*.md` and `README.md`.
14. **An excluded path is not enclosed.** `exclude` removes enclosure as it removes ownership. Witness: `core/*` excluding `core/gen/*` does not enclose `core/gen/a`.
15. **Closest picks only the longest directories, and ties all run.** Every member of `closest as p` encloses `p`; none has a longer enclosing directory than another member; every enclosing area with that depth is a member; `closest as p = []` iff no area encloses `p`. Rules out a shorter-directory area winning, and a tie broken to one. Witness: `core/*` and `core/io/*`: `core/io/x/y` has the second only; two areas with `core/io/*` both return.

### `decide` (S4)
16. **Owned implies touched.** If area `a` owns a changed path (end of a rename included), `a.name ∈ (decide …).touched`. Rules out a missed area. Witness: one area, one modified path.
17. **Touched is in `run`; `run` is touched when nothing is full.** `touched ⊆ run` and `full = false → run = touched`. Rules out a touched area that is skipped, and an untouched one that runs without a reason. Witness: a change that is owned, no gate path, no unmapped path, not a release candidate.
18. **Run when full.** `full = true → run =` every area (and `inert` if declared) in file order, and `skipped = []`. Witness: an unmapped path.
19. **Unmapped implies full.** `unmapped ≠ [] → full = true`. Rules out a silent skip. Witness: a root file no glob owns.
20. **Gate-defining implies full and is never unmapped.** A path under `.land/` or matching a protected glob makes `full = true`, is in `gateDefining`, and is not in `unmapped`, even if an area owns it. Rules out a narrowed run for a gate change. Witnesses: `.land/x`, a protected `Makefile`, and an owned protected path.
21. **The release candidate runs every area.** `releaseCandidate = true → run =` every area (and `inert`); no step skipped. Witness: an empty change list.
22. **A rename touches what its two ends touch.** `touched (R old p) = touched [D old, A p]`, and its `touched` is the union of the two single-path decisions' touched, as a set. Witness: a rename across two areas touches both.
23. **Monotonicity.** For `cs ⊆ cs'` (as sets), `(decide cfg cs rc).run ⊆ (decide cfg cs' rc).run` and the same for `touched`, `full` and `unmapped`. Adding a changed path never shrinks `run`. Witness: add a path of a second area.
24. **No narrower selection.** `steps` is exactly the steps of the areas in `run`: every step of every area in `run` appears (by `(cwd, run)`), and no other step does. Rules out selection by anything but area. Witness: an area with three steps, all in `steps`.
25. **A shared step runs once, in the file's order.** `steps` has no repeated `(cwd, run)`; it is a sublist of the file-order concatenation of the steps of `run`; for two kept steps the first occurrence in the file comes first. Witness: two touched areas that declare the same `(cwd, run)`.
26. **Overlap is the dependency; there is no edge.** A path owned by two areas touches both; the touched set is a function of the owners and enclosures of each path only, never of another area. Witness: one path in `a` and `b`.
27. **Stepless.** If every area in `run` has no steps, `steps = []` and `stepless = true`. Witness: only an inert area touched.
28. **Inert does not own a deleted path.** A deleted path matching only an inert glob is not owned by `inert` (it falls to enclosure or to unmapped); a non-deleted one is. With no areas file, the same carve-out applies to `all`. Witness: `D docs/x.md` versus `M docs/x.md`.
29. **`Change.split`.** Its output has no rename, its length is the number of changes plus the number of renames, and every path of the input appears. Witness: one rename.

### Reuse (S5)
30. **Never reuses an area `moved` touches.** `a ∈ (reuse …).reused → a ∉ moved.touched`. Witness: an area that passed, not moved.
31. **Nothing reused when either side is full.** `mine.full → reused = []`; `moved.full → reused = []`. Witness: a full `mine`.
32. **Never reuses a stepless area, and reuses only a passed one.** `a ∈ reused → a` has steps `∧ a ∈ passed ∧ a ∈ mine.run`; a stepless area is in neither `reused` nor `rerun`. Witness: one stepless area.
33. **Fails toward running.** Every area of `mine.run` with steps is in exactly one of `reused`, `rerun`; an area not passed is in `rerun`. Rules out a verdict reused without evidence. Witness: a failed area.

### Report (S5)
34. **Symmetric.** `a` and `b` overlap on `ps` iff `b` and `a` do; the report lists each pair once, in name order, with `a < b`; the paths are sorted and distinct. Witness: two overlapping areas.
35. **A path in three areas** appears under each of the three pairs. Witness: three areas, one path.
36. **Counts equal the lists.** `unmappedCount = unmapped.length`; `areasInOverlap` is the length of the distinct names in `overlaps`; `pathsInOverlap` the length of the distinct paths in `overlaps`; and `areasInOverlap = 0 ↔ overlaps = []`. Witness: a report with one overlap of two paths gives `(2, 2, 0)`.
37. **Unmapped is exact.** A tracked path is listed iff no area owns it and it is not gate-defining; its list is the enclosing areas (`[]` = unmapped, and then `decide` of that path alone is `full`). Witness: a root `notes.txt`.
38. **Stepless is exact.** `stepless` is exactly the areas whose `steps = []`, in file order.

## Slices
- **S2: the glob** (`VbmAreas/Glob.lean`): `Chars`, `globMatch`, `checkGlob`, `checkCwd`, `segments`, `globDir`. Proves 1 to 7 and 11.
- **S3: the areas value, `owns`, enclosure** (`VbmAreas/Areas.lean`): `Step`, `Area`, `AreasRefusal`, `validName`, `validate`, `owns`, `encloses`, `closest`. Proves 8 to 10 and 12 to 15.
- **S4: `decide`** (`VbmAreas/Decide.lean`): `Status`, `Change`, `Config`, `Decision`, `splitRenames`, `decide`. Proves 16 to 29.
- **S5: reuse and the report** (`VbmAreas/Reuse.lean`, `VbmAreas/Report.lean`): `reuse`, `report`, the path order and the distinct-list helper. Proves 30 to 38; also generates the test vectors the tool is checked against (`scripts/`, deterministic, no network).

Each slice keeps its diff near 150 production lines (split rather than grow), lands behind no flag (a pure library has no behaviour to switch), and regenerates `docs/proof-ledger.md` through the gate.

## Named limits
- Paths and patterns are bounded by nothing in the library; the caller bounds input size. `globMatch` is a structural recursion with fuel; its worst case on a pattern with many stars is polynomial only if the implementation memoises, so S2 either proves a polynomial bound or states the limit (a pattern's star count) with the harm it prevents.
- The number of areas and changes is bounded by the caller; every function is linear or quadratic in them.

## Typed refusals
Every refusal is an `AreasRefusal` or a `GlobRefusal`, never a default and never a partial value. `decide`, `reuse` and `report` take a validated value and cannot refuse.

## Non-goals
- **Landing throughput.** The library does not model how many landings per hour a repository can sustain, queueing, or the cost of rerunning steps. That is a probability model (arrival rates, run times, conflict odds); it is estimation, not selection, it needs a different kind of proof, and mixing it in would put a distribution into a library whose value is that every answer is exact. It belongs in a later, separate library that may import this one.
- Selection by import graph, coverage, test history, name or size, and any flag that skips a step (rule 3 forbids them; no function here has such a parameter).
- Parsing and printing the areas file.

## Doubts to settle before S2
- `pathsInOverlap` as a count of distinct paths (not of path-pair entries).
- "Under `.land/`": the prefix `.land/` with a following segment; the bare path `.land` is treated as not under it.
- A path equal to a glob's directory (`core` against `core/*`) is not enclosed (the enclosure is a proper prefix).
