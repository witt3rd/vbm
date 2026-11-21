import VbmAreas.Decide
/-! # The reuse decision (S5)

A landing validated on base B1 finds the trunk at B2. `mine` is the decision of the landing, `moved` the decision of the paths the trunk changed in between, `passed` the names of the areas of `mine` that ran and passed on B1. An area of `mine` that ran, has steps, passed, and is not touched by `moved` is REUSED; every other area of `mine` with steps RUNS AGAIN; an area with no steps is neither. A full `mine` or a full `moved` reuses nothing: reuse only ever fails toward running. -/
namespace VbmAreas

/-- The areas of the decision's configuration that have steps, by name (`inert` and every declared stepless area have none). -/
def Config.hasSteps (cfg : Config) (n : String) : Bool := cfg.file.areas.any (fun a => a.name == n && !a.steps.isEmpty)

/-- The outcome: the areas whose verdict on the old base stands, and the areas that run again. -/
structure Reuse where
  reused : List String
  rerun : List String
  deriving DecidableEq, Repr

/-- The verdict on the old base stands for `n`: neither side is full, `n` passed, and `moved` does not touch it. -/
def Reuse.stands (mine moved : Decision) (passed : List String) (n : String) : Bool :=
  !mine.full && !moved.full && passed.contains n && !moved.touched.contains n

/-- The reuse decision: of the areas of `mine` that ran and have steps, the ones whose verdict stands are reused, the others run again. -/
def Reuse.decide (cfg : Config) (mine moved : Decision) (passed : List String) : Reuse :=
  let cand := mine.run.filter cfg.hasSteps
  { reused := cand.filter (Reuse.stands mine moved passed), rerun := cand.filter (fun n => !Reuse.stands mine moved passed n) }

end VbmAreas
