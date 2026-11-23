import VbmMemory

/-! # Proofs about the types: a note and an instance

A theorem with a hypothesis carries a witness beside it that its hypothesis can hold: a theorem whose hypothesis cannot be met says nothing. -/
namespace VbmMemory

/-! ## The three kinds of scope -/

/-- The three kinds of scope are distinct, even under one name. -/
theorem scope_kinds_distinct (n : String) :
    Scope.cls n ≠ Scope.domain n ∧ Scope.domain n ≠ Scope.identity n ∧ Scope.cls n ≠ Scope.identity n := by
  simp

/-- Witness: the hypothesis of `scope_kinds_distinct` (a name) can be met. -/
example : Scope.cls "x" ≠ Scope.domain "x" ∧ Scope.domain "x" ≠ Scope.identity "x" ∧
    Scope.cls "x" ≠ Scope.identity "x" := scope_kinds_distinct "x"

/-! ## A note and an instance -/

/-- Witness: a note that derives from nothing and a note that derives from another both exist, so the list of sources can be empty and not empty. -/
example : ∃ (n m : Note), n.cites = [] ∧ m.cites = [n.id] :=
  ⟨⟨0, .cls "x", "s", []⟩, ⟨1, .domain "d", "t", [0]⟩, rfl, rfl⟩

/-- Witness: an instance without an identity and one that bears an identity both exist, so neither branch of the attachment type is empty. -/
example : ∃ (w k : Attach), w.identity = none ∧ k.identity = some "i" ∧ k.domains = ["d"] ∧ w.profile = "x" :=
  ⟨⟨"x", none, []⟩, ⟨"x", some "i", ["d"]⟩, rfl, rfl, rfl, rfl⟩

end VbmMemory
