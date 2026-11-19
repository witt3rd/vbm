import VbmProb.Prob
/-! # Probability: the properties PR1 to PR5 and PR10, each with its witness -/
namespace VbmProb
namespace Prob

/-! ## PR1: `make` -/

/-- PR1: `make q` succeeds exactly when `q` is in `[0, 1]`, and then the value is `q`. -/
theorem make_ok_iff (q : Rat) : (∃ p, make q = .ok p) ↔ 0 ≤ q ∧ q ≤ 1 := by
  unfold make
  by_cases h0 : q < 0
  · simp [h0, Rat.not_le.mpr h0]
  · by_cases h1 : 1 < q
    · simp [h0, h1, Rat.not_le.mpr h1]
    · simp [h0, h1, Rat.not_lt.mp h0, Rat.not_lt.mp h1]

/-- PR1: an accepted value is the input. -/
theorem make_val {q : Rat} {p : Prob} (h : make q = .ok p) : p.val = q := by
  unfold make at h
  by_cases h0 : q < 0
  · simp [h0] at h
  · by_cases h1 : 1 < q
    · simp [h0, h1] at h
    · simp only [h0, h1, dite_false] at h
      cases h; rfl

/-- PR1: a value below 0 is refused as `belowZero`. -/
theorem make_belowZero {q : Rat} (h : q < 0) : make q = .error (.belowZero q) := by
  simp [make, h]

/-- PR1: a value above 1 is refused as `aboveOne`. -/
theorem make_aboveOne {q : Rat} (h : 1 < q) : make q = .error (.aboveOne q) := by
  have h0 : ¬ q < 0 := Rat.not_lt.mpr (Rat.le_trans (by decide +kernel) (Rat.le_of_lt h))
  simp [make, h0, h]

-- Non-vacuity witnesses for PR1: the middle and both edges are accepted; both sides refuse.
example : ∃ p, make (1/2) = .ok p ∧ p.val = 1/2 :=
  let h := (make_ok_iff (1/2)).mpr (by decide +kernel)
  h.elim fun p hp => ⟨p, hp, make_val hp⟩
example : ∃ p, make 0 = .ok p := (make_ok_iff 0).mpr (by decide +kernel)
example : ∃ p, make 1 = .ok p := (make_ok_iff 1).mpr (by decide +kernel)
example : make (-1/2) = .error (.belowZero (-1/2)) := make_belowZero (by decide +kernel)
example : make (3/2) = .error (.aboveOne (3/2)) := make_aboveOne (by decide +kernel)

/-! ## PR2: `ofFrac` -/

/-- `make` never refuses with `denominatorZero`. -/
theorem make_ne_denominatorZero (q : Rat) : make q ≠ .error .denominatorZero := by
  unfold make
  by_cases h0 : q < 0
  · simp [h0]
  · by_cases h1 : 1 < q <;> simp [h0, h1]

/-- PR2: `ofFrac` refuses `denominatorZero` exactly when the denominator is 0. -/
theorem ofFrac_denominatorZero_iff (n : Int) (d : Nat) :
    ofFrac n d = .error .denominatorZero ↔ d = 0 := by
  unfold ofFrac
  by_cases h : d = 0
  · simp [h]
  · simp only [h, ite_false, iff_false]
    exact make_ne_denominatorZero _

/-- PR2: for a non-zero denominator `ofFrac` is `make` of the quotient. -/
theorem ofFrac_eq_make {n : Int} {d : Nat} (h : d ≠ 0) :
    ofFrac n d = make (Rat.divInt n (d : Int)) := by
  simp [ofFrac, h]

-- Non-vacuity witnesses for PR2.
example : ∃ p, ofFrac 1 4 = .ok p ∧ p.val = 1/4 := by
  have e : Rat.divInt 1 ((4 : Nat) : Int) = 1/4 := by decide +kernel
  have := ((make_ok_iff (1/4)).mpr (by decide +kernel))
  obtain ⟨p, hp⟩ := this
  refine ⟨p, ?_, make_val hp⟩
  rw [ofFrac_eq_make (by decide), e]; exact hp
example : ofFrac 1 0 = .error .denominatorZero := by simp [ofFrac]
example : ofFrac 5 4 = .error (.aboveOne (5/4)) := by
  have : Rat.divInt 5 ((4 : Nat) : Int) = 5/4 := by decide +kernel
  rw [ofFrac_eq_make (by decide), this]
  exact make_aboveOne (by decide +kernel)

/-! ## PR3: `complement` -/

/-- PR3: the value of the complement. -/
theorem complement_val (p : Prob) : (complement p).val = 1 - p.val := rfl

/-- PR3: the complement is an involution. -/
theorem complement_complement (p : Prob) : complement (complement p) = p :=
  ext (by simp only [complement_val]; exact one_sub_one_sub _)

/-- PR3: the complement of `zero` is `one`. -/
theorem complement_zero : complement zero = one :=
  ext (by decide +kernel)

/-- PR3: a probability and its complement sum to 1. -/
theorem val_add_complement (p : Prob) : p.val + (complement p).val = 1 := by
  simp only [complement_val]
  rw [Rat.sub_eq_add_neg, ← Rat.add_assoc, Rat.add_comm p.val 1, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

-- Non-vacuity witness for PR3.
example : (complement ⟨1/4, by decide +kernel, by decide +kernel⟩).val = 3/4 := by decide +kernel

/-! ## PR4: `mul` -/

/-- PR4: the value of a product. -/
theorem mul_val (p q : Prob) : (mul p q).val = p.val * q.val := rfl

/-- PR4: commutative. -/
theorem mul_comm (p q : Prob) : mul p q = mul q p := ext (Rat.mul_comm _ _)

/-- PR4: associative. -/
theorem mul_assoc (p q r : Prob) : mul (mul p q) r = mul p (mul q r) := ext (Rat.mul_assoc _ _ _)

/-- PR4: `one` is a left unit. -/
theorem one_mul (p : Prob) : mul one p = p := ext (Rat.one_mul _)

/-- PR4: `one` is a right unit. -/
theorem mul_one (p : Prob) : mul p one = p := ext (Rat.mul_one _)

/-- PR4: `zero` absorbs on the left. -/
theorem zero_mul (p : Prob) : mul zero p = zero := ext (Rat.zero_mul _)

/-- PR4: `zero` absorbs on the right. -/
theorem mul_zero (p : Prob) : mul p zero = zero := ext (Rat.mul_zero _)

/-- PR4: a product is at most its left factor. -/
theorem mul_le_left (p q : Prob) : (mul p q).val ≤ p.val := by
  have := Rat.mul_le_mul_of_nonneg_left q.le_one p.nonneg
  rwa [Rat.mul_one] at this

/-- PR4: a product is at most its right factor. -/
theorem mul_le_right (p q : Prob) : (mul p q).val ≤ q.val := by
  rw [mul_comm]; exact mul_le_left q p

-- Non-vacuity witness for PR4.
example : (mul ⟨1/2, by decide +kernel, by decide +kernel⟩ ⟨1/3, by decide +kernel, by decide +kernel⟩).val = 1/6 := by
  decide +kernel

/-! ## PR5: `add` -/

/-- PR5: `add` succeeds exactly when the sum is at most 1, and then the value is the sum. -/
theorem add_ok_iff (p q : Prob) :
    (∃ r, add p q = .ok r ∧ r.val = p.val + q.val) ↔ p.val + q.val ≤ 1 := by
  unfold add
  by_cases h : p.val + q.val ≤ 1 <;> simp [h]

/-- PR5: an accepted sum is the sum of the values. -/
theorem add_val {p q r : Prob} (h : add p q = .ok r) : r.val = p.val + q.val := by
  unfold add at h
  by_cases hs : p.val + q.val ≤ 1
  · simp only [hs, dite_true] at h; cases h; rfl
  · simp [hs] at h

/-- PR5: a sum above 1 is refused, carrying the sum. -/
theorem add_refuses {p q : Prob} (h : ¬ p.val + q.val ≤ 1) :
    add p q = .error (.sumExceedsOne (p.val + q.val)) := by
  simp [add, h]

/-- PR5: commutative (as a result, refusal included). -/
theorem add_comm (p q : Prob) : add p q = add q p := by
  have e := Rat.add_comm p.val q.val
  by_cases h : p.val + q.val ≤ 1
  · have h' : q.val + p.val ≤ 1 := e ▸ h
    simp only [add, h, h', dite_true]; exact congrArg Except.ok (ext e)
  · have h' : ¬ q.val + p.val ≤ 1 := e ▸ h
    simp [add, h', e]

/-- PR5: a probability and its complement make `one`. -/
theorem add_complement (p : Prob) : add p (complement p) = .ok one := by
  have h : p.val + (complement p).val ≤ 1 := by rw [val_add_complement]; exact Rat.le_refl
  unfold add
  simp only [h, dite_true]
  exact congrArg Except.ok (ext (val_add_complement p))

-- Non-vacuity witnesses for PR5: 1/2 + 1/2 is accepted, 2/3 + 2/3 is refused.
example : add ⟨1/2, by decide +kernel, by decide +kernel⟩ ⟨1/2, by decide +kernel, by decide +kernel⟩ = .ok one := by
  have h : (1/2 : Rat) + 1/2 ≤ 1 := by decide +kernel
  simp only [add, h, dite_true]
  exact congrArg Except.ok (ext (by change (1/2 : Rat) + 1/2 = 1; decide +kernel))
example : add ⟨2/3, by decide +kernel, by decide +kernel⟩ ⟨2/3, by decide +kernel, by decide +kernel⟩
    = .error (.sumExceedsOne (4/3)) := by
  have h : ¬ ((2/3 : Rat) + 2/3 ≤ 1) := by decide +kernel
  have := add_refuses (p := ⟨2/3, by decide +kernel, by decide +kernel⟩) (q := ⟨2/3, by decide +kernel, by decide +kernel⟩) h
  rw [this]
  have e : ((2/3 : Rat) + 2/3) = 4/3 := by decide +kernel
  simp only [e]

/-! ## PR10: the order -/

/-- PR10: reflexive. -/
theorem le_refl (p : Prob) : p ≤ p := Rat.le_refl

/-- PR10: transitive. -/
theorem le_trans {p q r : Prob} (h : p ≤ q) (h' : q ≤ r) : p ≤ r := Rat.le_trans h h'

/-- PR10: antisymmetric, by `ext`. -/
theorem le_antisymm {p q : Prob} (h : p ≤ q) (h' : q ≤ p) : p = q := ext (Rat.le_antisymm h h')

/-- PR10: total. -/
theorem le_total (p q : Prob) : p ≤ q ∨ q ≤ p := Rat.le_total

-- Non-vacuity witness for PR10: `1/3 ≤ 1/2` and not `1/2 ≤ 1/3`.
example : (⟨1/3, by decide +kernel, by decide +kernel⟩ : Prob) ≤ ⟨1/2, by decide +kernel, by decide +kernel⟩ := by
  decide +kernel
example : ¬ ((⟨1/2, by decide +kernel, by decide +kernel⟩ : Prob) ≤ ⟨1/3, by decide +kernel, by decide +kernel⟩) := by
  decide +kernel

end Prob
end VbmProb
