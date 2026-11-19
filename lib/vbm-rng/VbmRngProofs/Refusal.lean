import VbmRng.Refusal
/-! # The refusals are distinct (S3) -/
namespace VbmRng

/-- The six refusals are pairwise distinct. -/
theorem refusal_pairwise_distinct :
    [Refusal.boundZero, .boundTooLarge, .fractionBitsOutOfRange,
     .probabilityDenominatorZero, .probabilityOutOfRange, .fuelExhausted].Pairwise
      (· ≠ ·) := by decide

/-- A refusal is never a success: the two constructors of `DrawWith` differ. -/
theorem refusal_ne_ok {σ α : Type} (r : Refusal) (v : α × σ) :
    (Except.error r : DrawWith σ α) ≠ Except.ok v := by
  intro h; cases h

-- Non-vacuity witnesses: a refusal and a success are both inhabited, and fractions compare by value.
example : (Except.error Refusal.boundZero : DrawWith Nat Nat) ≠ Except.ok (1, 2) := refusal_ne_ok _ _
example : Refusal.boundZero ≠ Refusal.fuelExhausted := by decide
example : ({ num := 21, bits := 8 } : Fraction) ≠ { num := 21, bits := 9 } := by decide

end VbmRng
