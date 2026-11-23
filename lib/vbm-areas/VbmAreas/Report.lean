import VbmAreas.Decide
/-! # The report (S5)

What a repository's areas look like: where areas overlap (`inert`, when declared, counts as an area), which tracked paths no area owns and which areas enclose them, which areas have no steps, and three counts. Paths are listed in code-point order of their characters, without repeats; a pair of areas is listed once, in name order. -/
namespace VbmAreas

/-- Lexicographic order on characters by code point (`[]` is least). -/
def lexLt : Chars → Chars → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a.toNat < b.toNat) || (a == b && lexLt as bs)

/-- The order on paths and names. -/
def strLt (a b : String) : Bool := lexLt a.toList b.toList

/-- Insert into a strictly ascending list, keeping it strictly ascending (an element already there is not repeated). -/
def insertU (p : String) : List String → List String
  | [] => [p]
  | q :: qs => if strLt p q then p :: q :: qs else if p = q then q :: qs else q :: insertU p qs

/-- Sorted and without repeats. -/
def sortU (l : List String) : List String := l.foldr insertU []

/-- A path in a report. A tracked path is not deleted: it is looked at as a modified one. -/
def Report.owners (cfg : Config) (p : String) : List String := cfg.owners ⟨.modified, p, none⟩

/-- The tracked paths (sorted, distinct) that both `a` and `b` own. -/
def Report.pathsOf (cfg : Config) (tr : List String) (a b : String) : List String :=
  tr.filter (fun p => (Report.owners cfg p).contains a && (Report.owners cfg p).contains b)

/-- One overlap: two areas, `a` before `b` by name, and the paths both own (sorted, never empty). -/
structure Overlap where
  a : String
  b : String
  paths : List String
  deriving DecidableEq, Repr

/-- Every pair `(a, b)` of the names with `a` before `b`, by `a` then `b`. -/
def Report.pairs (ns : List String) : List (String × String) :=
  ns.flatMap (fun a => (ns.filter (strLt a)).map (fun b => (a, b)))

/-- (a) Every pair of areas (`inert` included) that both own a tracked path, with those paths; a path owned by three areas is under each of the three pairs. -/
def Report.overlap (cfg : Config) (tracked : List String) : List Overlap :=
  (Report.pairs (sortU cfg.names)).filterMap (fun ab =>
    let ps := Report.pathsOf cfg (sortU tracked) ab.1 ab.2
    if ps.isEmpty then none else some ⟨ab.1, ab.2, ps⟩)

/-- (b) Every tracked path (sorted, distinct) that no area owns and that is not gate-defining, with the declared areas that enclose it (`[]` = UNMAPPED). -/
def Report.unowned (cfg : Config) (tracked : List String) : List (String × List String) :=
  (sortU tracked).filterMap (fun p =>
    if (Report.owners cfg p).isEmpty && !cfg.gate p then some (p, (cfg.file.areas.filter (fun a => a.encloses p)).map Area.name) else none)

/-- (c) The areas with no steps, in file order, then `inert` when declared. -/
def Report.noSteps (cfg : Config) : List String :=
  (cfg.file.areas.filter (fun a => a.steps.isEmpty)).map Area.name ++ (if cfg.inert.isEmpty then [] else ["inert"])

/-- The distinct names in some overlap. -/
def Report.overlapNames (cfg : Config) (tracked : List String) : List String :=
  sortU ((Report.overlap cfg tracked).flatMap (fun o => [o.a, o.b]))

/-- The distinct paths in some overlap. -/
def Report.overlapPaths (cfg : Config) (tracked : List String) : List String :=
  sortU ((Report.overlap cfg tracked).flatMap Overlap.paths)

/-- The report: the three lists and the three counts (areas in overlap, paths in overlap, unmapped paths: every listed path, enclosed or not). -/
structure Summary where
  overlaps : List Overlap
  unowned : List (String × List String)
  noSteps : List String
  areasInOverlap : Nat
  pathsInOverlap : Nat
  unmapped : Nat
  deriving DecidableEq, Repr

/-- The whole report of a configuration and its tracked paths. -/
def Report.summary (cfg : Config) (tracked : List String) : Summary :=
  { overlaps := Report.overlap cfg tracked, unowned := Report.unowned cfg tracked, noSteps := Report.noSteps cfg
    areasInOverlap := (Report.overlapNames cfg tracked).length, pathsInOverlap := (Report.overlapPaths cfg tracked).length
    unmapped := (Report.unowned cfg tracked).length }

end VbmAreas
