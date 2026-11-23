import VbmDecision.Prob
/-! # Probabilities and exact decimals: P1 to P4 (S1a) -/
namespace VbmDecision

open Decimal Prob

theorem nat_a (m a : Nat) : m * 10 ^ (a + 6) = m * 10 ^ a * 10 ^ 6 := by
  rw [Nat.pow_add, Nat.mul_assoc]

theorem nat_b (m a b : Nat) (h : a + b = 6) : m * 10 ^ a * 10 ^ b = m * 10 ^ 6 := by
  rw [Nat.mul_assoc, ← Nat.pow_add, h]

theorem nat_c (q k : Nat) : q * 10 ^ (k + 6) = 10 ^ k * q * 10 ^ 6 := by
  rw [Nat.pow_add]; ac_rfl

theorem numer_scale (d : Decimal) (h : d.neg = false ∨ d.mantissa = 0) :
    d.numer * (scale : Int) = ((d.mantissa * 10 ^ d.exp.toNat * 10 ^ 6 : Nat) : Int) := by
  unfold Decimal.numer scale
  rcases h with h | h
  · simp [h]
  · simp [h]

/-- The exact scaling, in naturals: an accepted decimal has `v × denom = mantissa × 10^exp⁺ × 10^6`. -/
theorem toScaled_spec (d : Decimal) (v : Nat) (h : d.toScaled = .ok v) :
    v * d.denom = d.mantissa * 10 ^ d.exp.toNat * 10 ^ 6 := by
  unfold Decimal.toScaled at h
  by_cases h0 : d.mantissa = 0
  · simp [h0] at h
    subst h
    simp [h0]
  · simp only [h0, ite_false] at h
    by_cases hn : d.neg = true
    · simp [hn] at h
    · simp only [hn] at h
      by_cases hb : maxExponent < d.exp.natAbs
      · simp [hb] at h
      · simp only [hb, ite_false] at h
        unfold Decimal.denom
        by_cases h1 : 0 ≤ d.exp + 6
        · simp only [h1, ite_true] at h
          cases h
          by_cases he : 0 ≤ d.exp
          · have e2 : (-d.exp).toNat = 0 := by omega
            have e1 : (d.exp + 6).toNat = d.exp.toNat + 6 := by omega
            rw [e2, e1, nat_a]; simp
          · have e1 : d.exp.toNat = 0 := by omega
            have e2 : (d.exp + 6).toNat + (-d.exp).toNat = 6 := by omega
            rw [e1, Nat.pow_zero, Nat.mul_one, nat_b _ _ _ e2]
        · simp only [h1, ite_false] at h
          by_cases h2 : d.mantissa % 10 ^ (-(d.exp + 6)).toNat = 0
          · simp only [h2, ite_true] at h
            cases h
            have e1 : d.exp.toNat = 0 := by omega
            have e2 : (-d.exp).toNat = (-(d.exp + 6)).toNat + 6 := by omega
            obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h2
            have hpos : 0 < 10 ^ (-(d.exp + 6)).toNat := Nat.pow_pos (by decide)
            rw [hq, Nat.mul_div_cancel_left _ hpos, e1, e2, Nat.pow_zero, Nat.mul_one, nat_c]
          · simp [h2] at h

/-- P1 `prob-ofdecimal-exact`: an accepted decimal is exactly `val` millionths, as an equation of integers. -/
theorem ofDecimal_exact (d : Decimal) (p : Prob) (h : Prob.ofDecimal d = .ok p) :
    (p.val : Int) * (d.denom : Int) = d.numer * (scale : Int) := by
  unfold Prob.ofDecimal at h
  cases hs : d.toScaled with
  | error e => simp [hs] at h
  | ok v =>
    simp only [hs] at h
    by_cases hv : v ≤ scale
    · simp only [hv, dite_true] at h
      have hpv : p.val = v := by cases h; rfl
      have hz : d.neg = false ∨ d.mantissa = 0 := by
        unfold Decimal.toScaled at hs
        by_cases h0 : d.mantissa = 0
        · exact Or.inr h0
        · by_cases hn : d.neg = true
          · simp [h0, hn] at hs
          · exact Or.inl (by simpa using hn)
      rw [numer_scale d hz, hpv, ← Int.natCast_mul]
      exact congrArg (Nat.cast) (toScaled_spec d v hs)
    · simp [hv] at h

-- Non-vacuity of P1: `0.1234560` and `1.2345600e-1` are `123456` millionths.
example : Prob.ofDecimal ⟨false, 1234560, -7⟩ = .ok ⟨123456, by decide⟩ := rfl
example : Prob.ofDecimal ⟨false, 12345600, -8⟩ = .ok ⟨123456, by decide⟩ := rfl

theorem denom_pos (d : Decimal) : 0 < d.denom := Nat.pow_pos (by decide)

/-- P2 `prob-toscaled-refuses-imprecise`: a non-negative decimal within the exponent limit whose value is not a whole number of millionths is refused as `tooPrecise`. -/
theorem toScaled_tooPrecise (d : Decimal) (hn : d.neg = false) (hb : d.exp.natAbs ≤ maxExponent)
    (hnd : ¬ ((d.denom : Int) ∣ d.numer * (scale : Int))) :
    d.toScaled = .error .tooPrecise := by
  have h0 : d.mantissa ≠ 0 := by
    intro h0; apply hnd; rw [numer_scale d (Or.inl hn), h0]; simp
  have hb' : ¬ maxExponent < d.exp.natAbs := by omega
  have key : ∀ v, d.toScaled = .ok v → False := by
    intro v hv
    apply hnd
    rw [numer_scale d (Or.inl hn), ← toScaled_spec d v hv]
    exact Int.natCast_dvd_natCast.mpr ⟨v, Nat.mul_comm _ _⟩
  unfold Decimal.toScaled
  simp only [h0, hn, hb', ite_false, Bool.false_eq_true]
  by_cases h1 : 0 ≤ d.exp + 6
  · exfalso; apply key (d.mantissa * 10 ^ (d.exp + 6).toNat)
    unfold Decimal.toScaled
    simp [h0, hn, hb', h1]
  · simp only [h1, ite_false]
    by_cases h2 : d.mantissa % 10 ^ (-(d.exp + 6)).toNat = 0
    · exfalso; apply key (d.mantissa / 10 ^ (-(d.exp + 6)).toNat)
      unfold Decimal.toScaled
      simp [h0, hn, hb', h1, h2]
    · simp [h2]

-- Non-vacuity of P2: `0.1234567` is refused as `tooPrecise`, and the hypotheses hold for it.
example : Decimal.toScaled ⟨false, 1234567, -7⟩ = .error .tooPrecise := rfl
example : ¬ (((Decimal.denom ⟨false, 1234567, -7⟩ : Nat) : Int) ∣ Decimal.numer ⟨false, 1234567, -7⟩ * (scale : Int)) := by
  decide +kernel
example : Prob.ofDecimal ⟨false, 1234567, -7⟩ = .error .tooPrecise := rfl

theorem stripZeros_spec : ∀ (f m k m' k' : Nat), stripZeros f m k = (m', k') →
    ∃ j, m = m' * 10 ^ j ∧ k' = k + j ∧ j ≤ f := by
  intro f
  induction f with
  | zero =>
    intro m k m' k' h
    unfold stripZeros at h
    cases h
    exact ⟨0, by simp⟩
  | succ f ih =>
    intro m k m' k' h
    unfold stripZeros at h
    split at h
    · rename_i hc
      obtain ⟨j, hj1, hj2, hj3⟩ := ih _ _ _ _ h
      refine ⟨j + 1, ?_, by omega, by omega⟩
      calc m = 10 * (m / 10) := by omega
        _ = m' * 10 ^ (j + 1) := by rw [hj1, Nat.pow_succ]; ac_rfl
    · cases h
      exact ⟨0, by simp⟩

/-- P3 helper: `toDecimal` of a nonzero value is the stripped mantissa with the matching exponent. -/
theorem toDecimal_ne (p : Prob) (h0 : p.val ≠ 0) :
    p.toDecimal = ⟨false, (stripZeros 6 p.val 0).1, ((stripZeros 6 p.val 0).2 : Int) - 6⟩ := by
  unfold Prob.toDecimal; simp [h0]

/-- P3 `prob-roundtrip`: reading back the decimal of a probability gives the probability. -/
theorem ofDecimal_toDecimal (p : Prob) : Prob.ofDecimal p.toDecimal = .ok p := by
  by_cases h0 : p.val = 0
  · have hd : p.toDecimal = ⟨false, 0, 0⟩ := by unfold Prob.toDecimal; simp [h0]
    rw [hd]
    have : p = ⟨0, Nat.zero_le _⟩ := by cases p; simp at h0; simp [h0]
    rw [this]; rfl
  · rw [toDecimal_ne p h0]
    cases hr : stripZeros 6 p.val 0 with
    | mk m' k' =>
    obtain ⟨j, hj1, hj2, hj3⟩ := stripZeros_spec 6 p.val 0 m' k' hr
    have hm : m' ≠ 0 := by intro h; apply h0; rw [hj1, h]; simp
    have hle := p.le
    have hts : Decimal.toScaled ⟨false, m', (k' : Int) - 6⟩ = .ok (m' * 10 ^ j) := by
      unfold Decimal.toScaled
      have e1 : ((k' : Int) - 6 + 6).toNat = j := by omega
      have e3 : 0 ≤ (k' : Int) - 6 + 6 := by omega
      have e2 : ¬ maxExponent < ((k' : Int) - 6).natAbs := by unfold maxExponent; omega
      simp [hm, e2]
      have : k' = j := by omega
      subst this; rfl
    unfold Prob.ofDecimal
    rw [hts]
    have hv : m' * 10 ^ j ≤ scale := by rw [← hj1]; exact hle
    simp only [hv, dite_true]
    congr
    cases p; simp at hj1 ⊢; exact hj1.symm

-- Non-vacuity of P3: `0`, `1` and `0.9731` round-trip.
example : Prob.ofDecimal (Prob.toDecimal ⟨0, by decide⟩) = .ok ⟨0, by decide⟩ := rfl
example : Prob.ofDecimal (Prob.toDecimal ⟨1000000, by decide⟩) = .ok ⟨1000000, by decide⟩ := rfl
example : Prob.ofDecimal (Prob.toDecimal ⟨973100, by decide⟩) = .ok ⟨973100, by decide⟩ := rfl
example : Prob.toDecimal ⟨973100, by decide⟩ = ⟨false, 9731, -4⟩ := rfl

/-- P4 `prob-range` (accepted values): an accepted decimal is in `[0, 1]`, as a value and as a fraction. -/
theorem ofDecimal_range (d : Decimal) (p : Prob) (h : Prob.ofDecimal d = .ok p) :
    p.val ≤ scale ∧ 0 ≤ d.numer ∧ d.numer ≤ (d.denom : Int) := by
  refine ⟨p.le, ?_⟩
  have e := ofDecimal_exact d p h
  have hd : (0 : Int) < d.denom := by exact_mod_cast denom_pos d
  have hs : (0 : Int) < scale := by unfold scale; omega
  have hp0 : (0 : Int) ≤ p.val := by omega
  have hple : (p.val : Int) ≤ scale := by exact_mod_cast p.le
  constructor
  · apply Int.not_lt.mp; intro hc
    have h1 : d.numer * scale < 0 := Int.mul_neg_of_neg_of_pos (by omega) hs
    have h2 : 0 ≤ (p.val : Int) * d.denom := Int.mul_nonneg hp0 (Int.le_of_lt hd)
    omega
  · apply Int.not_lt.mp; intro hc
    have h1 : (d.denom : Int) * scale < d.numer * scale := Int.mul_lt_mul_of_pos_right (by omega) hs
    have h2 : (p.val : Int) * d.denom ≤ scale * d.denom := Int.mul_le_mul_of_nonneg_right hple (Int.le_of_lt hd)
    have h3 : (d.denom : Int) * scale = scale * d.denom := Int.mul_comm _ _
    omega

/-- P4 (negative): a nonzero negative decimal is refused as `negative`. -/
theorem ofDecimal_negative (d : Decimal) (hn : d.neg = true) (h0 : d.mantissa ≠ 0) :
    Prob.ofDecimal d = .error .negative := by
  simp [Prob.ofDecimal, Decimal.toScaled, hn, h0]

/-- P4 (above one): an exactly scaled value above `scale` is refused as `outOfRange`. -/
theorem ofDecimal_outOfRange (d : Decimal) (v : Nat) (hs : d.toScaled = .ok v) (hv : scale < v) :
    Prob.ofDecimal d = .error .outOfRange := by
  unfold Prob.ofDecimal
  rw [hs]
  simp [Nat.not_le.mpr hv]

-- Non-vacuity of P4: `1.000001` is refused, `1` is accepted, `-0.5` is refused, `-0` is zero.
example : Prob.ofDecimal ⟨false, 1000001, -6⟩ = .error .outOfRange := rfl
example : Prob.ofDecimal ⟨false, 1, 0⟩ = .ok ⟨1000000, by decide⟩ := rfl
example : Prob.ofDecimal ⟨true, 5, -1⟩ = .error .negative := rfl
example : Prob.ofDecimal ⟨true, 0, 0⟩ = .ok ⟨0, by decide⟩ := rfl
example : Decimal.toScaled ⟨false, 1000001, -6⟩ = .ok 1000001 := rfl

-- Non-vacuity of the sum rule's definition: 0.6 + 0.4 within the tolerance, 0.7 + 0.1 not.
example : SumOk 2 [⟨600000, by decide⟩, ⟨400000, by decide⟩] := by decide
example : ¬ SumOk 2 [⟨700000, by decide⟩, ⟨100000, by decide⟩] := by decide

end VbmDecision
