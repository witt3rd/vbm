import VbmAreas.Report
/-! # Compose: composing the libraries' declared areas (specification)

Pure, deterministic composition of per-library area declarations (`lib/<name>/areas.json`)
and each library's declared `deps` into the repository's `.land/areas.json` (`AreasFile`).
Definitions only; proofs are the next item.

Design summary:
1. Each library `<name>` declares `version`, its `deps` (direct library dependencies), and
   `areas`, where each area has `name` (`<name>` for a single-area library, or `<name>:<part>`),
   `paths` (relative to `lib/<name>/`), `exclude` (optional, relative to `lib/<name>/`),
   `steps`, and `uses` (`[{lib, area}]` where `area` is the `<part>` or full area name).
2. Validity checks every rule of (1) and (2) as a decidable predicate returning a typed
   `ComposeRefusal` that names the offending library and area:
   - `version = 1`, `areas` non-empty, valid library name, unique library names;
   - every area name is valid, not `"inert"`, unique in the repository, and starts with
     the library's name (`n == lib` when single-area, or `(lib ++ ":").isPrefixOf n` / `n == lib`);
   - every `paths` non-empty, every glob in `paths`/`exclude` valid, every `cwd` valid, every `run` non-empty;
   - no path of the library is unmapped (for any library paths given, or the glob union covers `*`,
     checked via `unmappedPaths` against the library's relative paths, and also checking `paths`
     do not leave `lib/<name>/` — relative paths have no leading `/`, `./`, or `..` segments);
   - every `uses` target names a library in the library's `deps` (direct or transitive; direct
     `deps` check is explicit), and names an existing area of that library;
   - `deps` closure and `uses` expansion are acyclic (a cycle is refused with `cycle`).
3. `uses` expansion:
   - If an area declares non-empty `uses`, it transitively owns the prefixed `paths` (and
     carries the prefixed `exclude`) of each named `(lib, area)` in its `uses` closure.
   - If an area declares empty `uses`, it defaults to using EVERY area of EVERY library in
     its library's `deps` closure (sound default, matching the single-area-per-lib rule).
4. Prefixing and output:
   - Every relative path/exclude glob `g` in library `<name>` is prefixed `lib/<name>/<g>`.
   - Output areas are sorted deterministically by `strLt` on area name (stable total order),
     followed by the repository-level areas (`registry`, `docs`, `tooling`) and with the
     whole-repository lint step appended (deduplicated) to every area's steps.
5. `checkComposed`: compares a candidate `AreasFile` against `compose`, returning `.ok ()` or
   a typed `ComposeDiff` naming the difference.

Protected-set ruling (design note, question 4):
  Every `lib/*/areas.json` and the composed `.land/areas.json` should be in the protected set
  (changed only with the owner's word and the `Protected:` trailer), while a library's tests,
  proofs, and sources remain ordinary. Cost: adding a new library or area requires the owner's
  word once (rare). Alternative: keeping steps in unprotected per-library files that the lander
  merely invokes — weaker because an agent editing those files could silently weaken or disable
  the check that judges its own landing.
-/
namespace VbmAreas

/-- A cross-library area reference in `uses`: names a dependency library and the area part
    (or full area name) within that library. -/
structure UseRef where
  lib : String
  area : String
  deriving DecidableEq, Repr

/-- A declared area inside `lib/<name>/areas.json` (paths and exclude are relative to `lib/<name>/`). -/
structure LibAreaDecl where
  name : String
  paths : List String
  exclude : List String := []
  steps : List Step := []
  uses : List UseRef := []
  deriving DecidableEq, Repr

/-- A library's `areas.json` declaration together with its library name, declared direct `deps`,
    and the library's relative tracked paths (used to check full coverage within the library). -/
structure LibDecl where
  lib : String
  version : Nat := 1
  deps : List String := []
  areas : List LibAreaDecl
  trackedPaths : List String := []
  deriving DecidableEq, Repr

/-- Repository-level framing appended during composition: extra repo areas (`registry`, `docs`,
    `tooling`) and the whole-repository lint step added to every area. -/
structure RepoFrame where
  extraAreas : List Area := []
  repoLintStep : Option Step := none
  deriving DecidableEq, Repr

/-- Typed refusals for library declarations and composition; every area/library fault names
    the offending library and area. -/
inductive ComposeRefusal where
  | noLibraries
  | duplicateLibrary (lib : String)
  | badLibraryName (lib : String)
  | badVersion (lib : String) (version : Nat)
  | noAreas (lib : String)
  | badAreaName (lib area : String)
  | areaNamePrefix (lib area : String)
  | reservedAreaName (lib area : String)
  | duplicateAreaName (lib area : String)
  | emptyPaths (lib area : String)
  | badGlob (lib area glob : String) (why : Glob.Reason)
  | pathLeavesLibrary (lib area glob : String)
  | badCwd (lib area cwd : String) (why : Glob.Reason)
  | emptyRun (lib area : String)
  | unmappedLibPath (lib path : String)
  | unknownDep (lib area dep : String)
  | useNotInDeps (lib area targetLib : String)
  | unknownUseArea (lib area targetLib targetArea : String)
  | depCycle (lib : String)
  | useCycle (lib area : String)
  deriving DecidableEq, Repr

/-- Typed difference returned by `checkComposed` when a committed `AreasFile` disagrees with
    the composed result. -/
inductive ComposeDiff where
  | invalidInput (why : ComposeRefusal)
  | versionMismatch (expected actual : Nat)
  | missingArea (name : String)
  | extraArea (name : String)
  | areaMismatch (name : String) (expected actual : Area)
  | orderMismatch (expected actual : List String)
  deriving DecidableEq, Repr

/-- Valid area name for declarations: `[a-z0-9][a-z0-9_:-]*` (allows `:` for `<lib>:<part>`). -/
def validDeclNameRest (c : Char) : Bool :=
  validNameRest c || c == ':'

/-- A valid declared area name: starts with `[a-z0-9]` and continues with `[a-z0-9_:-]*`. -/
def validDeclName (n : String) : Bool :=
  match n.toList with
  | [] => false
  | c :: cs => (('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')) && cs.all validDeclNameRest

/-- Check whether `areaName` belongs to `lib`: either exact `lib` (single-area library) or
    prefixed `lib:` (multi-area `<lib>:<part>`). -/
def hasLibPrefix (lib areaName : String) : Bool :=
  areaName == lib || (lib.toList ++ [':']).isPrefixOf areaName.toList

/-- Resolve the canonical full area name for a `UseRef` `(targetLib, targetArea)`:
    if `targetArea` already equals `targetLib` or starts with `targetLib:`, keep it;
    otherwise form `targetLib ++ ":" ++ targetArea`. -/
def resolveUseAreaName (u : UseRef) : String :=
  if hasLibPrefix u.lib u.area then u.area else u.lib ++ ":" ++ u.area

/-- Prefix a relative glob or path with `lib/<name>/`. -/
def prefixLibPath (lib p : String) : String :=
  "lib/" ++ lib ++ "/" ++ p

/-- Check if a relative glob attempts to leave `lib/<name>/` (leading `/`, `./`, or any `..` segment). -/
def leavesLibrary (g : String) : Bool :=
  let cs := g.toList
  cs.head? == some '/' || ['.', '/'].isPrefixOf cs || (Glob.segments cs).any (· == ['.', '.'])

/-- Look up a `LibDecl` by library name. -/
def findLib (decls : List LibDecl) (lib : String) : Option LibDecl :=
  decls.find? (fun d => d.lib == lib)

/-- Look up an area in a `LibDecl` by its declared name. -/
def findLibArea (d : LibDecl) (areaName : String) : Option LibAreaDecl :=
  d.areas.find? (fun a => a.name == areaName)

/-- Check if a library's `deps` graph has a cycle reachable from `lib`, using `fuel` bounded by
    `decls.length` and `visiting` as the active recursion stack. -/
def hasDepCycleAux (decls : List LibDecl) (visiting : List String) : Nat → String → Bool
  | 0, _ => false
  | fuel + 1, lib =>
    if visiting.contains lib then true
    else match findLib decls lib with
      | none => false
      | some d => d.deps.any (hasDepCycleAux decls (lib :: visiting) fuel)

/-- Compute the transitive closure of `deps` for a library (sorted, deduplicated),
    with explicit fuel `decls.length`. -/
def depsClosureAux (decls : List LibDecl) : Nat → List String → List String → List String
  | 0, _, acc => sortU acc
  | _, [], acc => sortU acc
  | fuel + 1, q :: qs, acc =>
    if acc.contains q then depsClosureAux decls fuel qs acc
    else
      let next := match findLib decls q with
        | some d => d.deps
        | none => []
      depsClosureAux decls fuel (qs ++ next) (q :: acc)

/-- Transitive `deps` closure of library `lib` (excluding `lib` itself unless cyclic). -/
def depsClosure (decls : List LibDecl) (lib : String) : List String :=
  match findLib decls lib with
  | none => []
  | some d => depsClosureAux decls (decls.length * (decls.length + 1) + 1) d.deps []

/-- Validate a single `LibAreaDecl` within `lib`, given all `decls` and `libDecl`. -/
def validateLibArea (decls : List LibDecl) (libDecl : LibDecl) (a : LibAreaDecl) :
    Option ComposeRefusal :=
  if !validDeclName a.name then some (.badAreaName libDecl.lib a.name)
  else if a.name == "inert" then some (.reservedAreaName libDecl.lib a.name)
  else if !hasLibPrefix libDecl.lib a.name then some (.areaNamePrefix libDecl.lib a.name)
  else if a.paths.isEmpty then some (.emptyPaths libDecl.lib a.name)
  else
    let globCheck := (a.paths ++ a.exclude).findSome? (fun g =>
      if leavesLibrary g then some (.pathLeavesLibrary libDecl.lib a.name g)
      else (Glob.refusal g).map (.badGlob libDecl.lib a.name g))
    let stepCheck := a.steps.findSome? (fun s =>
      if s.run.isEmpty then some (.emptyRun libDecl.lib a.name)
      else match s.cwd with
        | none => none
        | some c => (Glob.cwdRefusal c).map (.badCwd libDecl.lib a.name c))
    let useCheck := a.uses.findSome? (fun u =>
      if !libDecl.deps.contains u.lib then some (.useNotInDeps libDecl.lib a.name u.lib)
      else match findLib decls u.lib with
        | none => some (.unknownDep libDecl.lib a.name u.lib)
        | some targetLib =>
          let fullTarget := resolveUseAreaName u
          match findLibArea targetLib fullTarget with
          | none => some (.unknownUseArea libDecl.lib a.name u.lib u.area)
          | some _ => none)
    globCheck.or (stepCheck.or useCheck)

/-- Validate that every tracked relative path of `d` is owned by at least one of its areas. -/
def validateLibCoverage (d : LibDecl) : Option ComposeRefusal :=
  d.trackedPaths.findSome? (fun p =>
    let owned := d.areas.any (fun a =>
      a.paths.any (fun g => Glob.matches g p) && !a.exclude.any (fun g => Glob.matches g p))
    if owned then none else some (.unmappedLibPath d.lib p))

/-- Validate a single `LibDecl` (version, library name, deps existence/cycles, areas, coverage). -/
def validateLibDecl (decls : List LibDecl) (d : LibDecl) : Option ComposeRefusal :=
  if !validName d.lib then some (.badLibraryName d.lib)
  else if d.version != 1 then some (.badVersion d.lib d.version)
  else if d.areas.isEmpty then some (.noAreas d.lib)
  else if hasDepCycleAux decls [] (decls.length + 1) d.lib then some (.depCycle d.lib)
  else
    let missingDep := d.deps.findSome? (fun dep =>
      match findLib decls dep with
      | none => some (.unknownDep d.lib d.lib dep)
      | some _ => none)
    let areaCheck := d.areas.findSome? (validateLibArea decls d)
    missingDep.or (areaCheck.or (validateLibCoverage d))

/-- Total number of areas across all library declarations (used as fuel for `uses` expansion). -/
def totalAreaCount (decls : List LibDecl) : Nat :=
  decls.foldl (fun acc d => acc + d.areas.length) 0

/-- Direct `uses` targets `(targetLib, targetFullAreaName)` for an area:
    if `a.uses` is non-empty, use the resolved explicit targets;
    if `a.uses` is empty, default to every area of every library in `depsClosure decls lib`. -/
def effectiveUses (decls : List LibDecl) (lib : String) (a : LibAreaDecl) :
    List (String × String) :=
  if !a.uses.isEmpty then
    a.uses.map (fun u => (u.lib, resolveUseAreaName u))
  else
    (depsClosure decls lib).flatMap (fun depLib =>
      match findLib decls depLib with
      | none => []
      | some dl => dl.areas.map (fun da => (depLib, da.name)))

/-- Check for cycles in the `uses` relation starting from `(lib, areaName)`. -/
def hasUseCycleAux (decls : List LibDecl) (visiting : List String) : Nat → String → String → Bool
  | 0, _, _ => false
  | fuel + 1, lib, areaName =>
    if visiting.contains areaName then true
    else match findLib decls lib with
      | none => false
      | some dl =>
        match findLibArea dl areaName with
        | none => false
        | some a =>
          (effectiveUses decls lib a).any (fun (tl, ta) =>
            hasUseCycleAux decls (areaName :: visiting) fuel tl ta)

/-- Validate all library declarations: non-empty, unique library names, unique global area names,
    per-library validity, and no `uses` cycles. -/
def validateDecls (decls : List LibDecl) : Option ComposeRefusal :=
  if decls.isEmpty then some .noLibraries
  else
    let rec checkLibs (seenLibs seenAreas : List String) : List LibDecl → Option ComposeRefusal
      | [] => none
      | d :: rest =>
        if seenLibs.contains d.lib then some (.duplicateLibrary d.lib)
        else match validateLibDecl decls d with
          | some r => some r
          | none =>
            let rec checkAreaNames (sa : List String) : List LibAreaDecl → Option (List String × ComposeRefusal)
              | [] => none
              | a :: as =>
                if sa.contains a.name then some (sa, .duplicateAreaName d.lib a.name)
                else checkAreaNames (a.name :: sa) as
            match checkAreaNames seenAreas d.areas with
            | some (_, r) => some r
            | none =>
              let newSeenAreas := d.areas.foldl (fun acc a => a.name :: acc) seenAreas
              let fuel := totalAreaCount decls + 1
              let cyc := d.areas.findSome? (fun a =>
                if hasUseCycleAux decls [] fuel d.lib a.name then some (.useCycle d.lib a.name) else none)
              match cyc with
              | some r => some r
              | none => checkLibs (d.lib :: seenLibs) newSeenAreas rest
    checkLibs [] [] decls

/-- Expand transitive `paths` and `exclude` (already prefixed with `lib/<name>/`) for `(lib, areaName)`. -/
def expandAreaPathsAux (decls : List LibDecl) :
    Nat → String → String → (List String × List String)
  | 0, _, _ => ([], [])
  | fuel + 1, lib, areaName =>
    match findLib decls lib with
    | none => ([], [])
    | some dl =>
      match findLibArea dl areaName with
      | none => ([], [])
      | some a =>
        let ownPaths := a.paths.map (prefixLibPath lib)
        let ownExcl := a.exclude.map (prefixLibPath lib)
        let inherited := (effectiveUses decls lib a).map (fun (tl, ta) =>
          expandAreaPathsAux decls fuel tl ta)
        let inhPaths := inherited.flatMap Prod.fst
        let inhExcl := inherited.flatMap Prod.snd
        (sortU (ownPaths ++ inhPaths), sortU (ownExcl ++ inhExcl))

/-- Append the repository lint step (if any) to an area's steps, deduplicating while preserving order. -/
def withRepoLint (lintStep : Option Step) (steps : List Step) : List Step :=
  match lintStep with
  | none => dedupFrom [] steps
  | some s => dedupFrom [] (steps ++ [s])

/-- Insert an `Area` into a list sorted strictly ascending by `strLt` on `Area.name`. -/
def insertAreaSorted (a : Area) : List Area → List Area
  | [] => [a]
  | b :: bs =>
    if strLt a.name b.name then a :: b :: bs
    else if a.name == b.name then b :: bs
    else b :: insertAreaSorted a bs

/-- Sort areas deterministically by `Area.name` using `strLt`. -/
def sortAreas (xs : List Area) : List Area :=
  xs.foldr insertAreaSorted []

/-- Compose validated library declarations and repository framing into a deterministic `AreasFile`. -/
def compose (decls : List LibDecl) (frame : RepoFrame := {}) :
    Except ComposeRefusal AreasFile :=
  match validateDecls decls with
  | some r => .error r
  | none =>
    let fuel := totalAreaCount decls + 1
    let libAreas : List Area := decls.flatMap (fun dl =>
      dl.areas.map (fun a =>
        let (ps, ex) := expandAreaPathsAux decls fuel dl.lib a.name
        { name := a.name
          paths := ps
          exclude := ex
          steps := withRepoLint frame.repoLintStep a.steps }))
    let extraAreas : List Area := frame.extraAreas.map (fun a =>
      { a with steps := withRepoLint frame.repoLintStep a.steps })
    .ok { version := 1, areas := sortAreas (libAreas ++ extraAreas) }

/-- Compare two `AreasFile` values and return `.ok ()` if identical or a typed `ComposeDiff`. -/
def diffAreasFile (expected actual : AreasFile) : Except ComposeDiff Unit :=
  if expected.version != actual.version then
    .error (.versionMismatch expected.version actual.version)
  else
    let rec checkMissing : List Area → Except ComposeDiff Unit
      | [] => .ok ()
      | e :: es =>
        match actual.areas.find? (fun a => a.name == e.name) with
        | none => .error (.missingArea e.name)
        | some act =>
          if e != act then .error (.areaMismatch e.name e act)
          else checkMissing es
    match checkMissing expected.areas with
    | .error d => .error d
    | .ok () =>
      match actual.areas.find? (fun a => !expected.areas.any (fun e => e.name == a.name)) with
      | some extra => .error (.extraArea extra.name)
      | none =>
        let expNames := expected.areas.map Area.name
        let actNames := actual.areas.map Area.name
        if expNames != actNames then .error (.orderMismatch expNames actNames)
        else .ok ()

/-- Check whether a committed `AreasFile` agrees with the composition of `decls` and `frame`. -/
def checkComposed (decls : List LibDecl) (committed : AreasFile) (frame : RepoFrame := {}) :
    Except ComposeDiff Unit :=
  match compose decls frame with
  | .error r => .error (.invalidInput r)
  | .ok expected => diffAreasFile expected committed

/-! ## Examples (`decide` / `simp` checks) -/

section Examples

private def leafLib : LibDecl :=
  { lib := "leaf"
    version := 1
    deps := []
    areas := [{ name := "leaf", paths := ["*"], steps := [{ run := "lake build Leaf" }] }]
    trackedPaths := ["Leaf.lean", "Leaf/Core.lean"] }

private def baseLib : LibDecl :=
  { lib := "base"
    version := 1
    deps := []
    areas :=
      [ { name := "base:spec", paths := ["Base/*.lean"], steps := [{ run := "lake build Base" }] }
      , { name := "base:c", paths := ["cbits/*"], steps := [{ run := "cc -c cbits/a.c" }] } ]
    trackedPaths := ["Base/Core.lean", "cbits/a.c"] }

private def appLib : LibDecl :=
  { lib := "app"
    version := 1
    deps := ["base"]
    areas :=
      [ { name := "app:spec", paths := ["App/*.lean"], steps := [{ run := "lake build App" }],
          uses := [{ lib := "base", area := "spec" }] }
      , { name := "app:proofs", paths := ["AppProofs/*"], steps := [{ run := "lake build AppProofs" }] } ]
    trackedPaths := ["App/Main.lean", "AppProofs/Thm.lean"] }

private def defaultClosureLib : LibDecl :=
  { lib := "consumer"
    version := 1
    deps := ["base"]
    areas := [{ name := "consumer", paths := ["*"], steps := [{ run := "lake build Consumer" }] }]
    trackedPaths := ["Consumer.lean"] }

-- 1. A one-area leaf library composes cleanly with prefixed paths.
example :
    compose [leafLib] =
      .ok { version := 1
            areas := [{ name := "leaf", paths := ["lib/leaf/*"], exclude := [],
                        steps := [{ run := "lake build Leaf" }] }] } := rfl

-- 2. A library with two areas and a cross-library `uses` (`app:spec` uses `base:spec`, not `base:c`;
--    `app:proofs` has empty `uses`, so it defaults to the whole `deps` closure of `app`).
example :
    (compose [baseLib, appLib]).isOk = true := by
  decide

example :
    (compose [baseLib, appLib]).map (fun f =>
      (f.areas.find? (fun a => a.name == "app:spec")).map Area.paths) =
      .ok (some ["lib/app/App/*.lean", "lib/base/Base/*.lean"]) := rfl

-- 3. Default closure: `consumer` has empty `uses`, so it inherits all areas of `base`.
example :
    (compose [baseLib, defaultClosureLib]).map (fun f =>
      (f.areas.find? (fun a => a.name == "consumer")).map Area.paths) =
      .ok (some ["lib/base/Base/*.lean", "lib/base/cbits/*", "lib/consumer/*"]) := rfl

-- 4. Refused dependency cycle.
private def cycA : LibDecl :=
  { lib := "a", version := 1, deps := ["b"],
    areas := [{ name := "a", paths := ["*"], steps := [{ run := "test a" }] }] }
private def cycB : LibDecl :=
  { lib := "b", version := 1, deps := ["a"],
    areas := [{ name := "b", paths := ["*"], steps := [{ run := "test b" }] }] }

example :
    compose [cycA, cycB] = .error (.depCycle "a") := rfl

-- 5. Refused unmapped path inside a library.
private def unmappedLib : LibDecl :=
  { lib := "broken", version := 1, deps := [],
    areas := [{ name := "broken", paths := ["src/*"], steps := [{ run := "test" }] }],
    trackedPaths := ["src/a.lean", "README.md"] }

example :
    compose [unmappedLib] = .error (.unmappedLibPath "broken" "README.md") := rfl

-- 6. `checkComposed` agrees when committed matches composed, and refuses a mismatch.
example :
    (match compose [leafLib] with
     | .ok f => match checkComposed [leafLib] f with | .ok () => true | .error _ => false
     | .error _ => false) = true := by
  decide

example :
    checkComposed [leafLib] { version := 2, areas := [] } =
      .error (.versionMismatch 1 2) := rfl

end Examples

end VbmAreas
