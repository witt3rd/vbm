import VbmProb.Refusal
/-! # Probability

A probability is an exact `Rat` in [0, 1], valid by construction (`docs/spec.md`, "Probability"). Core's `Rat` is the value; this file adds only the refinement and its operations. -/
namespace VbmProb

/-- A probability: an exact rational in the closed interval from 0 to 1. -/
structure Prob where
  /-- The exact value. -/
  val : Rat
  /-- The value is not below 0. -/
  nonneg : 0 ≤ val
  /-- The value is not above 1. -/
  le_one : val ≤ 1

namespace Prob

/-- Two probabilities with the same value are equal (the two bounds are proofs). -/
theorem ext {p q : Prob} (h : p.val = q.val) : p = q := by
  cases p; cases q; cases h; rfl

/-- The probability of the impossible event. -/
def zero : Prob := ⟨0, Rat.le_refl, by decide +kernel⟩

/-- The probability of the certain event. -/
def one : Prob := ⟨1, by decide +kernel, Rat.le_refl⟩

/-- The order of probabilities is the order of their values. -/
instance : LE Prob := ⟨fun p q => p.val ≤ q.val⟩

/-- Strictly below: the order of the values. -/
instance : LT Prob := ⟨fun p q => p.val < q.val⟩

instance (p q : Prob) : Decidable (p ≤ q) := inferInstanceAs (Decidable (p.val ≤ q.val))

/-- A rational as a probability, or the refusal that says which bound it breaks. -/
def make (q : Rat) : Except Refusal Prob :=
  if h0 : q < 0 then .error (.belowZero q)
  else if h1 : 1 < q then .error (.aboveOne q)
  else .ok ⟨q, Rat.not_lt.mp h0, Rat.not_lt.mp h1⟩

/-- The fraction `num / den` as a probability: a zero denominator is refused. -/
def ofFrac (num : Int) (den : Nat) : Except Refusal Prob :=
  if den = 0 then .error .denominatorZero else make (Rat.divInt num (den : Int))

/-- Subtracting twice from 1 returns the number (shared by `complement` and its involution). -/
theorem one_sub_one_sub (a : Rat) : 1 - (1 - a) = a := by
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, ← Rat.add_assoc,
    Rat.add_neg_cancel, Rat.zero_add]

/-- The probability that an event does not happen. -/
def complement (p : Prob) : Prob :=
  ⟨1 - p.val, (Rat.le_iff_sub_nonneg _ _).mp p.le_one,
   (Rat.le_iff_sub_nonneg _ _).mpr (by rw [one_sub_one_sub]; exact p.nonneg)⟩

/-- The probability that two independent events both happen. -/
def mul (p q : Prob) : Prob :=
  ⟨p.val * q.val, Rat.mul_nonneg p.nonneg q.nonneg,
   Rat.le_trans (by have := Rat.mul_le_mul_of_nonneg_left q.le_one p.nonneg; rwa [Rat.mul_one] at this) p.le_one⟩

/-- The probability that one of two disjoint events happens, or the refusal when the sum exceeds 1. -/
def add (p q : Prob) : Except Refusal Prob :=
  if h : p.val + q.val ≤ 1 then
    .ok ⟨p.val + q.val, Rat.add_nonneg p.nonneg q.nonneg, h⟩
  else .error (.sumExceedsOne (p.val + q.val))

end Prob
end VbmProb
