import VbmProb.Limits
/-! # The named limits, the size of a number and the key carrier: proofs and witnesses -/
namespace VbmProb

/-! ## The defaults -/

/-- The default limits are the specified ones: 1024 atoms, 512 bits, scale 10^18. -/
theorem Limits.default_values :
    Limits.default.maxAtoms = 1024 ∧ Limits.default.maxBits = 512 ∧ Limits.default.maxScale = 10 ^ 18 := by
  refine ⟨rfl, rfl, ?_⟩
  decide +kernel

-- Non-vacuity witness: the defaults differ from other limits, so the fields are not forced.
example : Limits.default ≠ { maxAtoms := 3, maxBits := 512, maxScale := 10 ^ 18 } := by decide +kernel

/-! ## `bitLength` -/

/-- `bitLength 0 = 0`. -/
theorem bitLength_zero : bitLength 0 = 0 := by simp [bitLength]

/-- For `n ≠ 0`, `bitLength n = log2 n + 1`. -/
theorem bitLength_of_ne_zero {n : Nat} (h : n ≠ 0) : bitLength n = Nat.log2 n + 1 := by
  simp [bitLength, h]

/-- `bitLength n = 0` exactly for `n = 0`. -/
theorem bitLength_eq_zero_iff {n : Nat} : bitLength n = 0 ↔ n = 0 := by
  by_cases h : n = 0
  · simp [bitLength, h]
  · simp [bitLength, h]

/-- `n < 2 ^ bitLength n`: the bit length is an upper bound of the exponent. -/
theorem lt_two_pow_bitLength (n : Nat) : n < 2 ^ bitLength n := by
  by_cases h : n = 0
  · simp [bitLength, h]
  · rw [bitLength_of_ne_zero h]; exact Nat.lt_log2_self

/-- `2 ^ (bitLength n - 1) ≤ n` for `n ≠ 0`: the bit length is the least such exponent. -/
theorem two_pow_bitLength_pred_le {n : Nat} (h : n ≠ 0) : 2 ^ (bitLength n - 1) ≤ n := by
  rw [bitLength_of_ne_zero h]; simpa using Nat.log2_self_le h

/-- `bitLength` is monotone. -/
theorem bitLength_mono {m n : Nat} (h : m ≤ n) : bitLength m ≤ bitLength n := by
  by_cases hm : m = 0
  · simp [bitLength, hm]
  · have hn : n ≠ 0 := by omega
    rw [bitLength_of_ne_zero hm, bitLength_of_ne_zero hn]
    have : m.log2 < n.log2 + 1 := (Nat.log2_lt hm).mpr (Nat.lt_of_le_of_lt h Nat.lt_log2_self)
    omega

-- Non-vacuity witnesses: the known values.
example : bitLength 0 = 0 := by decide
example : bitLength 1 = 1 := by decide
example : bitLength 255 = 8 := by decide
example : bitLength 256 = 9 := by decide
example : bitLength (2 ^ 511) = 512 := by decide +kernel
example : 255 < 2 ^ bitLength 255 := lt_two_pow_bitLength 255
example : 2 ^ (bitLength 256 - 1) ≤ 256 := two_pow_bitLength_pred_le (by decide)

/-! ## `Rat.bits` -/

/-- Every rational has at least one bit (its denominator is positive). -/
theorem Rat.bits_pos (q : Rat) : 0 < q.bits := by
  have h : q.den ≠ 0 := q.den_nz
  have : bitLength q.den ≠ 0 := fun h0 => h (bitLength_eq_zero_iff.mp h0)
  unfold Rat.bits; omega

/-- A whole number `n` has the bits of `|n|` plus one. -/
theorem Rat.bits_ofInt (n : Int) : (Rat.ofInt n).bits = bitLength n.natAbs + 1 := by
  simp [Rat.bits, bitLength]

-- Non-vacuity witnesses (`Rat` values by `decide +kernel`).
example : (0 : Rat).bits = 1 := by decide +kernel
example : (1 : Rat).bits = 2 := by decide +kernel
example : (1 / 2 : Rat).bits = 3 := by decide +kernel
example : (-1 / 2 : Rat).bits = 3 := by decide +kernel
example : (255 / 256 : Rat).bits = 8 + 9 := by decide +kernel
/-- The limit is attained: a rational of exactly 512 bits is within `Limits.default.maxBits`, one of 513 is not. -/
example : (Rat.ofInt (2 ^ 510)).bits ≤ Limits.default.maxBits := by decide +kernel
example : ¬ (Rat.ofInt (2 ^ 511)).bits ≤ Limits.default.maxBits := by decide +kernel

/-! ## `Key` -/

/-- `a ≤ b` on keys is `a < b ∨ a = b`. -/
theorem Key.le_iff {α : Type} [Key α] {a b : α} : Key.le a b ↔ a < b ∨ a = b := by
  unfold Key.le
  constructor
  · intro h
    cases Key.lt_trichotomy a b with
    | inl h' => exact .inl h'
    | inr h' => cases h' with
      | inl h' => exact .inr h'
      | inr h' => exact absurd h' h
  · intro h h'
    cases h with
    | inl h => exact Key.lt_irrefl a (Key.lt_trans h h')
    | inr h => subst h; exact Key.lt_irrefl _ h'

/-- Keys: `≤` is reflexive. -/
theorem Key.le_refl {α : Type} [Key α] (a : α) : Key.le a a := Key.lt_irrefl a

/-- Keys: `≤` is transitive. -/
theorem Key.le_trans {α : Type} [Key α] {a b c : α} (h1 : Key.le a b) (h2 : Key.le b c) : Key.le a c := by
  rcases Key.le_iff.mp h1 with h1 | h1 <;> rcases Key.le_iff.mp h2 with h2 | h2
  · exact Key.le_iff.mpr (.inl (Key.lt_trans h1 h2))
  · subst h2; exact Key.le_iff.mpr (.inl h1)
  · subst h1; exact Key.le_iff.mpr (.inl h2)
  · subst h1; subst h2; exact Key.le_refl _

/-- Keys: `≤` is total. -/
theorem Key.le_total {α : Type} [Key α] (a b : α) : Key.le a b ∨ Key.le b a := by
  cases Key.lt_trichotomy a b with
  | inl h => exact .inl (fun h' => Key.lt_irrefl a (Key.lt_trans h h'))
  | inr h => cases h with
    | inl h => subst h; exact .inl (Key.le_refl _)
    | inr h => exact .inr (fun h' => Key.lt_irrefl a (Key.lt_trans h' h))

/-- Keys: `≤` is antisymmetric. -/
theorem Key.le_antisymm {α : Type} [Key α] {a b : α} (h1 : Key.le a b) (h2 : Key.le b a) : a = b := by
  rcases Key.le_iff.mp h1 with h | h
  · exact absurd h h2
  · exact h

/-- Keys: `<` is asymmetric. -/
theorem Key.lt_asymm {α : Type} [Key α] {a b : α} (h : a < b) : ¬ b < a :=
  fun h' => Key.lt_irrefl a (Key.lt_trans h h')

/-- Keys: `Key.le` is decidable (it is the negation of a decidable `<`). -/
instance Key.instDecidableLe {α : Type} [Key α] (a b : α) : Decidable (Key.le a b) :=
  inferInstanceAs (Decidable (¬ b < a))

-- Non-vacuity witnesses: the instances compute, and the laws hold on literals.
example : Key.le (3 : Nat) 5 := by decide
example : ¬ Key.le (5 : Nat) 3 := by decide
example : Key.le (-2 : Int) 7 := by decide
example : Key.le (1 / 3 : Rat) (1 / 2) := by decide +kernel
example : ¬ Key.le (1 / 2 : Rat) (1 / 3) := by decide +kernel
example : (2 : Nat) < 3 ∨ (2 : Nat) = 3 ∨ (3 : Nat) < 2 := Key.lt_trichotomy 2 3
example : (-1 / 2 : Rat) < 1 / 3 := by decide +kernel
example : Key.le (4 : Int) 4 := Key.le_refl 4
example : (4 : Int) = 4 := Key.le_antisymm (Key.le_refl 4) (Key.le_refl 4)

end VbmProb
