import VbmMemory.Scope
namespace VbmMemory

/-- The three kinds of scope are distinct, even under one name. -/
theorem scope_kinds_distinct (n : String) :
    Scope.cls n ≠ Scope.domain n ∧ Scope.domain n ≠ Scope.identity n ∧ Scope.cls n ≠ Scope.identity n := by
  simp

end VbmMemory
