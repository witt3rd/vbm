import VbmProb.Refusal
/-! # The typed refusal: decidable equality, with witnesses -/
namespace VbmProb

/-- Refusals are compared by value: equal exactly when the same constructor carries equal fields. -/
theorem Refusal.eq_iff_decide (a b : Refusal) : a = b ↔ decide (a = b) = true := by
  simp

-- Non-vacuity witnesses: equal values are equal, different fields and different constructors are not.
example : Refusal.tooManyAtoms 4 3 = Refusal.tooManyAtoms 4 3 := by decide
example : Refusal.tooManyAtoms 4 3 ≠ Refusal.tooManyAtoms 5 3 := by decide
example : Refusal.zeroEvidence ≠ Refusal.zeroMarginal := by decide
example : Refusal.belowZero (-1/2) ≠ Refusal.aboveOne (-1/2) := by decide +kernel
example : Refusal.numberTooLarge 0 600 512 = Refusal.numberTooLarge 0 600 512 := by decide

/-- A constructor with fields is injective in each field (the refusal carries its evidence faithfully). -/
theorem Refusal.tooManyAtoms_inj {n m a b : Nat} (h : Refusal.tooManyAtoms n m = Refusal.tooManyAtoms a b) :
    n = a ∧ m = b := by
  cases h; exact ⟨rfl, rfl⟩

-- Non-vacuity witness: the hypothesis holds for equal refusals.
example : (4 = 4 ∧ 3 = 3) := Refusal.tooManyAtoms_inj (n := 4) (m := 3) (a := 4) (b := 3) rfl

end VbmProb
