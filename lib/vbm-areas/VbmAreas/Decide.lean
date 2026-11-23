import VbmAreas.Area
/-! # The decision (S4)

`Config.decide`: from the validated areas, the inert and protected globs, the changes and the release-candidate flag to a `Decision`. A change touches every area that owns a changed path; an unowned path runs the closest enclosing areas, or the full suite when none encloses it; a gate-defining path runs the full suite; the steps of the areas that run are listed once each, in the file's order. Areas are named by their `name`; the reserved pseudo-area `inert` comes last, when inert globs are declared. -/
namespace VbmAreas

/-- How a path changed. A rename is not a status: see `Change.renamedFrom`. -/
inductive Status where
  | added | modified | deleted
  deriving DecidableEq, Repr

/-- A changed path. `renamedFrom = some old` marks a rename from `old` to `path` (its `status` is then ignored). -/
structure Change where
  status : Status
  path : String
  renamedFrom : Option String := none
  deriving DecidableEq, Repr

/-- A rename becomes a deletion of the old path plus an addition of the new; every other change is itself. -/
def Change.split (c : Change) : List Change :=
  match c.renamedFrom with
  | none => [c]
  | some old => [⟨.deleted, old, none⟩, ⟨.added, c.path, none⟩]

/-- The areas file of a repository with none: one area `all` owning every path, with the gates command then the test command as steps. -/
def implicitFile (steps : List Step) : AreasFile := ⟨1, [⟨"all", ["*"], [], steps⟩]⟩

/-- The inputs of a decision but the changes: the validated file (`none` = no areas file), the steps of the implicit area, the inert globs, the protected globs. -/
structure Config where
  areas : Option Areas
  implicitSteps : List Step := []
  inert : List String := []
  protectedGlobs : List String := []

/-- The areas the decision ranges over: the validated file, or the implicit one. -/
def Config.file (cfg : Config) : AreasFile :=
  match cfg.areas with
  | some a => a.file
  | none => implicitFile cfg.implicitSteps

/-- Every area name in file order, then `inert` when inert globs are declared. -/
def Config.names (cfg : Config) : List String :=
  cfg.file.areas.map Area.name ++ (if cfg.inert.isEmpty then [] else ["inert"])

/-- A gate-defining path: strictly under `.land/`, or matching a protected glob. -/
def Config.gate (cfg : Config) (p : String) : Bool :=
  Glob.under ".land" p || cfg.protectedGlobs.any (fun g => Glob.matches g p)

/-- `inert` owns the change: an inert glob matches and the path is not deleted. -/
def Config.inertOwns (cfg : Config) (c : Change) : Bool :=
  c.status != .deleted && cfg.inert.any (fun g => Glob.matches g c.path)

/-- The area owns the change; with no areas file the inert globs carve a non-deleted path out of `all`. -/
def Config.areaOwns (cfg : Config) (a : Area) (c : Change) : Bool :=
  a.owns c.path && !(cfg.areas.isNone && cfg.inertOwns c)

/-- The names of the owners of a change: the areas that own it, in file order, then `inert`. -/
def Config.owners (cfg : Config) (c : Change) : List String :=
  (cfg.file.areas.filter (fun a => cfg.areaOwns a c)).map Area.name ++ (if cfg.inertOwns c then ["inert"] else [])

/-- How deeply the area encloses the path (0 when it does not). -/
def Area.depth (a : Area) (p : String) : Nat := (a.enclosureLength p).getD 0

/-- The closest enclosing areas: those that enclose the path with the longest directory; every tie is kept, in file order. -/
def closest (f : AreasFile) (p : String) : List Area :=
  let es := f.areas.filter (fun a => a.encloses p)
  let m := (es.map (fun a => a.depth p)).max?.getD 0
  es.filter (fun a => a.depth p == m)

/-- The names a change touches: its owners; else, unless gate-defining, the closest enclosing areas. -/
def Config.hit (cfg : Config) (c : Change) : List String :=
  if (cfg.owners c).isEmpty then (if cfg.gate c.path then [] else (closest cfg.file c.path).map Area.name) else cfg.owners c

/-- Unmapped: no owner, not gate-defining, and no area encloses it. -/
def Config.unmappedAt (cfg : Config) (c : Change) : Bool :=
  (cfg.owners c).isEmpty && !cfg.gate c.path && (closest cfg.file c.path).isEmpty

/-- The list without repeats, first occurrences kept in order; `seen` are the elements already kept. -/
def dedupFrom (seen : List Step) : List Step → List Step
  | [] => []
  | s :: r => if seen.contains s then dedupFrom seen r else s :: dedupFrom (s :: seen) r

/-- The decision. `inert` means that `run` has no steps (a landing that runs nothing says so). -/
structure Decision where
  touched : List String
  unmapped : List String
  gateDefining : List String
  full : Bool
  run : List String
  steps : List Step
  skipped : List String
  inert : Bool
  deriving DecidableEq, Repr

/-- The decision for a list of changes: split every rename, mark gate-defining paths, collect owners, then closest enclosure, then unmapped. -/
def Config.decide (cfg : Config) (changes : List Change) (rc : Bool) : Decision :=
  let cs := changes.flatMap Change.split
  let full := rc || cs.any (fun c => cfg.gate c.path || cfg.unmappedAt c)
  let hits := cs.flatMap cfg.hit
  let touched := cfg.names.filter (fun n => hits.contains n)
  let run := if full then cfg.names else touched
  let steps := dedupFrom [] ((cfg.file.areas.filter (fun a => run.contains a.name)).flatMap Area.steps)
  { touched, full, run, steps, inert := steps.isEmpty
    unmapped := (cs.filter cfg.unmappedAt).map Change.path
    gateDefining := (cs.filter (fun c => cfg.gate c.path)).map Change.path
    skipped := cfg.names.filter (fun n => !run.contains n) }

end VbmAreas
