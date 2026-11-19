import VbmDecision.Types
/-! # The types (S2): the tag maps, with witnesses

The spec's property section names no property of this slice (types only). The one-line tag maps are checked here, one witness per constructor. -/
namespace VbmDecision

/-- An answer and a question of the same constructor have the same kind tag. -/
theorem kindOf_noul (i : String) (c : Option (String × String)) (p : Prob) :
    (Question.noul i c).kindOf = (Answer.noul p).kindOf := rfl

example : (Question.choice "t" [("a", none), ("b", some "d")]).kindOf = Kind.choice := rfl
example : (Question.score "t" ["lo", "hi"]).kindOf = Kind.score := rfl
example : (Question.box "t").kindOf = Kind.box := rfl
example : (Answer.noul ⟨500000, by decide⟩).kindOf = Kind.noul := rfl
example : (Answer.choice "a" [("a", ⟨1000000, by decide⟩)] ⟨1000000, by decide⟩).kindOf = Kind.choice := rfl
example : (Answer.score 1500000 ⟨700000, by decide⟩ [] []).kindOf = Kind.score := rfl
example : (Thresholds.noul ⟨300000, by decide⟩ ⟨800000, by decide⟩).kindOf = Kind.noul := rfl
example : (Thresholds.box ⟨500000, by decide⟩).kindOf = Kind.box := rfl
/-- The kind tags are four distinct values. -/
example : Kind.noul ≠ Kind.box := by decide
/-- An outcome of each constructor, over a placeholder refusal type. -/
example : (Outcome.refused (ρ := Nat) 0) ≠ .abstain .lowMargin := by decide
example : (Outcome.decided (ρ := Nat) .yes) ≠ .decided .no := by decide

end VbmDecision
