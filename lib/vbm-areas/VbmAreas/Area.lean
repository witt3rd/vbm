import VbmAreas.Glob
/-! # The areas value (S3)

The areas file as data: ordered areas, each with a name, path globs, exclude globs and steps; the strict rules that make it valid, with a typed `Refusal` that names the area and the reason; the validated value; `owns`, the directories an area's globs start in, `encloses`. The version is part of the raw value. JSON parsing is a boundary and is not here: the two wire-level refusals exist so one type names every refusal, and `validate` never produces them. -/
namespace VbmAreas

/-- A step: a command line and an optional working directory. -/
structure Step where
  run : String
  cwd : Option String := none
  deriving DecidableEq, Repr

/-- An area: a name, the globs it owns, the globs it excludes, and its steps (possibly none). -/
structure Area where
  name : String
  paths : List String
  exclude : List String := []
  steps : List Step := []
  deriving DecidableEq, Repr

/-- The raw areas file: the version and the ordered areas (the order is the order steps run in). -/
structure AreasFile where
  version : Nat
  areas : List Area
  deriving DecidableEq, Repr

/-- Why an areas file is refused (closed); every constructor but the last two names the area. `unknownKey` and `missingSteps` are raised by a wire layer only. -/
inductive Refusal where
  | badVersion (v : Nat) | noAreas
  | badName (area : String) | reservedName (area : String) | duplicateName (area : String)
  | emptyPaths (area : String)
  | badGlob (area glob : String) (why : Glob.Reason)
  | badCwd (area cwd : String) (why : Glob.Reason)
  | emptyRun (area : String)
  | unknownKey (key : String) | missingSteps (area : String)
  deriving DecidableEq, Repr

/-- A name character after the first: `[a-z0-9_-]`. -/
def validNameRest (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-'

/-- A valid area name: `[a-z0-9][a-z0-9_-]*`. -/
def validName (n : String) : Bool :=
  match n.toList with
  | [] => false
  | c :: cs => (('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')) && cs.all validNameRest

/-- The first refusal of a step of area `a`: an empty `run`, then a bad `cwd`. -/
def Step.refusal (a : String) (s : Step) : Option Refusal :=
  if s.run.isEmpty then some (.emptyRun a)
  else match s.cwd with
    | none => none
    | some c => (Glob.cwdRefusal c).map (.badCwd a c)

/-- The first bad glob of the area, `paths` then `exclude`. -/
def Area.globRefusal (a : Area) : Option Refusal :=
  (a.paths ++ a.exclude).findSome? (fun g => (Glob.refusal g).map (Refusal.badGlob a.name g))

/-- The first refusal of one area: name, reserved name, empty paths, a bad glob, then its steps in order. -/
def Area.refusal (a : Area) : Option Refusal :=
  if !validName a.name then some (.badName a.name)
  else if a.name = "inert" then some (.reservedName a.name)
  else if a.paths.isEmpty then some (.emptyPaths a.name)
  else a.globRefusal.or (a.steps.findSome? (Step.refusal a.name))

/-- The first refusal over the areas in file order; `seen` holds the names already accepted (a repeat is a duplicate). -/
def Areas.refusalFrom (seen : List String) : List Area → Option Refusal
  | [] => none
  | a :: rest =>
    match a.refusal with
    | some r => some r
    | none => if seen.contains a.name then some (.duplicateName a.name) else Areas.refusalFrom (a.name :: seen) rest

/-- The validation: `none` = accepted, otherwise the first refusal (version, no areas, then file order). -/
def Areas.validate (f : AreasFile) : Option Refusal :=
  if f.version ≠ 1 then some (.badVersion f.version)
  else if f.areas.isEmpty then some .noAreas
  else Areas.refusalFrom [] f.areas

/-- The validated value: a file with its proof that `validate` accepts it. -/
structure Areas where
  file : AreasFile
  ok : Areas.validate file = none

/-- Validate a file into the validated value, or its refusal. -/
def Areas.check (f : AreasFile) : Except Refusal Areas :=
  match h : Areas.validate f with
  | none => .ok ⟨f, h⟩
  | some r => .error r

/-- The area owns the path: one of `paths` matches and no `exclude` does. -/
def Area.owns (a : Area) (p : String) : Bool :=
  a.paths.any (fun g => Glob.matches g p) && !a.exclude.any (fun g => Glob.matches g p)

/-- Some `exclude` glob matches the path. -/
def Area.excluded (a : Area) (p : String) : Bool := a.exclude.any (fun g => Glob.matches g p)

/-- The directories the area's globs start in (`""` is the root). -/
def Area.dirs (a : Area) : List String := a.paths.map Glob.startDir

/-- The directories of the area, not the root, that the path lies strictly under by whole segments. -/
def Area.enclosingDirs (a : Area) (p : String) : List String := a.dirs.filter (fun d => !d.isEmpty && Glob.under d p)

/-- The area encloses the path: not excluded, and under the (non-root) directory of some glob. -/
def Area.encloses (a : Area) (p : String) : Bool := !a.excluded p && !(a.enclosingDirs p).isEmpty

/-- How closely the area encloses the path: the most segments of an enclosing directory; `none` when it does not enclose it. -/
def Area.enclosureLength (a : Area) (p : String) : Option Nat :=
  if a.excluded p then none else ((a.enclosingDirs p).map (fun d => (Glob.segments d.toList).length)).max?

/-- The areas of the file that own the path, in file order. -/
def Areas.owners (f : AreasFile) (p : String) : List Area := f.areas.filter (fun a => a.owns p)

end VbmAreas
