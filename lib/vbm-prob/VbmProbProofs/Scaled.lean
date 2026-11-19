import VbmProb.Scaled
/-! # Fixed point: the properties FX1 to FX7, each with its witness -/
namespace VbmProb

/-- A literal probability for the witnesses (the bounds are decided by the kernel). -/
private def lit (q : Rat) (h0 : 0 ≤ q := by decide +kernel) (h1 : q ≤ 1 := by decide +kernel) : Prob := ⟨q, h0, h1⟩

/-- A literal scale for the witnesses. -/
private def sc (n : Nat) (h : 0 < n := by decide) : Scale := ⟨n, h⟩

/-! ## FX1: `Scale.make` -/

/-- FX1: a scale of 0 is refused as `zeroScale`. -/
theorem Scale.make_zero (lim : Limits) : Scale.make 0 lim = .error .zeroScale := by
  simp [Scale.make]

/-- FX1: a scale above the limit is refused, carrying the scale and the limit. -/
theorem Scale.make_tooLarge {n : Nat} {lim : Limits} (h : lim.maxScale < n) :
    Scale.make n lim = .error (.scaleTooLarge n lim.maxScale) := by
  have h0 : n ≠ 0 := by omega
  simp [Scale.make, h0, h]

/-- FX1: otherwise the scale has that number of units. -/
theorem Scale.make_ok {n : Nat} {lim : Limits} (h0 : n ≠ 0) (h : n ≤ lim.maxScale) :
    ∃ s, Scale.make n lim = .ok s ∧ s.n = n := by
  have h' : ¬ lim.maxScale < n := by omega
  exact ⟨⟨n, Nat.pos_of_ne_zero h0⟩, by simp [Scale.make, h0, h'], rfl⟩

/-- FX1: an accepted scale is the number asked for. -/
theorem Scale.make_n {n : Nat} {lim : Limits} {s : Scale} (h : Scale.make n lim = .ok s) : s.n = n := by
  unfold Scale.make at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · by_cases h1 : lim.maxScale < n
    · simp [h0, h1] at h
    · simp only [h0, h1, dite_false, ite_false, Except.ok.injEq] at h
      cases h; rfl

-- Non-vacuity witnesses for FX1.
example : ∃ s, Scale.make 1000000 Limits.default = .ok s ∧ s.n = 1000000 :=
  Scale.make_ok (by decide) (by decide +kernel)
example : Scale.make 0 Limits.default = .error .zeroScale := Scale.make_zero _
example : Scale.make (10 ^ 18 + 1) Limits.default = .error (.scaleTooLarge (10 ^ 18 + 1) 1000000000000000000) :=
  Scale.make_tooLarge (by decide +kernel)

/-! ## The integer arithmetic of `toScaled` -/

/-- The numerator of a probability is a natural number. -/
theorem num_cast (p : Prob) : ((p.val.num.toNat : Nat) : Int) = p.val.num :=
  Int.toNat_of_nonneg (Rat.num_nonneg.mpr p.nonneg)

/-- A probability is at most 1: its numerator is at most its denominator. -/
theorem num_le_den (p : Prob) : p.val.num.toNat ≤ p.val.den := by
  have h := (Rat.le_iff _ _).mp p.le_one
  have := num_cast p
  simp at h
  omega

/-- The two bounds that define the integer quotient. -/
theorem toScaled_bounds (s : Scale) (p : Prob) :
    toScaled s p * (2 * p.val.den) ≤ 2 * p.val.num.toNat * s.n + p.val.den ∧
    2 * p.val.num.toNat * s.n + p.val.den < (toScaled s p + 1) * (2 * p.val.den) := by
  have hd : 0 < 2 * p.val.den := Nat.mul_pos (by decide) (Nat.pos_of_ne_zero p.val.den_nz)
  unfold toScaled
  refine ⟨Nat.div_mul_le_self _ _, ?_⟩
  have h1 := Nat.div_add_mod (2 * p.val.num.toNat * s.n + p.val.den) (2 * p.val.den)
  have h2 := Nat.mod_lt (2 * p.val.num.toNat * s.n + p.val.den) hd
  rw [Nat.add_mul, Nat.one_mul]
  rw [Nat.mul_comm] at h1
  omega

/-! ## FX2: the range -/

/-- FX2: `toScaled` is at most the scale. -/
theorem toScaled_le (s : Scale) (p : Prob) : toScaled s p ≤ s.n := by
  have h := num_le_den p
  have hd : 0 < 2 * p.val.den := Nat.mul_pos (by decide) (Nat.pos_of_ne_zero p.val.den_nz)
  have : toScaled s p < s.n + 1 := by
    unfold toScaled
    rw [Nat.div_lt_iff_lt_mul hd]
    have h2 : p.val.num.toNat * s.n ≤ p.val.den * s.n := Nat.mul_le_mul_right _ h
    have h3 : (s.n + 1) * (2 * p.val.den) = 2 * (p.val.den * s.n) + 2 * p.val.den := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm s.n, Nat.mul_assoc]
    have h4 : 2 * p.val.num.toNat * s.n = 2 * (p.val.num.toNat * s.n) := Nat.mul_assoc _ _ _
    have := Nat.pos_of_ne_zero p.val.den_nz
    omega
  omega

/-- FX2: the impossible event is 0 units. -/
theorem toScaled_zero (s : Scale) : toScaled s Prob.zero = 0 := by
  show (2 * (0 : Rat).num.toNat * s.n + (0 : Rat).den) / (2 * (0 : Rat).den) = 0
  simp

/-- FX2: the certain event is the whole scale. -/
theorem toScaled_one (s : Scale) : toScaled s Prob.one = s.n := by
  show (2 * (1 : Rat).num.toNat * s.n + (1 : Rat).den) / (2 * (1 : Rat).den) = s.n
  simp
  omega

-- Non-vacuity witness for FX2: scale 10, `1/3` is 3 units.
example : toScaled (sc 10) (lit (1/3)) = 3 := by decide +kernel
example : toScaled (sc 10) Prob.zero = 0 ∧ toScaled (sc 10) Prob.one = 10 := ⟨toScaled_zero _, toScaled_one _⟩

/-! ## FX3: the error bound -/

/-- FX3: twice the distance between `toScaled·den` and `num·n` is at most `den`: the rounding error is at most half a unit. -/
theorem toScaled_error (s : Scale) (p : Prob) :
    2 * ((toScaled s p : Int) * p.val.den - p.val.num * s.n).natAbs ≤ p.val.den := by
  obtain ⟨h1, h2⟩ := toScaled_bounds s p
  rw [← num_cast p]
  generalize toScaled s p = t at *
  generalize p.val.den = d at *
  generalize p.val.num.toNat = a at *
  have e1 : t * (2 * d) = 2 * (t * d) := Nat.mul_left_comm _ _ _
  have e2 : (t + 1) * (2 * d) = 2 * (t * d) + 2 * d := by rw [Nat.add_mul, e1, Nat.one_mul]
  have e3 : 2 * a * s.n = 2 * (a * s.n) := Nat.mul_assoc _ _ _
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h1 h2
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  generalize t * d = x at *
  generalize a * s.n = y at *
  omega

-- Non-vacuity witnesses for FX3: 1/3 at scale 10^6 is 333333 (error a third of a unit); 1/2000000 is a tie
-- (rounds up to 1) and the bound is attained exactly: `2 · 1000000 = den`, so it cannot be tightened.
example : toScaled (sc 1000000) (lit (1/3)) = 333333 := by decide +kernel
example : 2 * (((333333 : Nat) : Int) * 3 - 1 * 1000000).natAbs ≤ 3 := by decide +kernel
example : toScaled (sc 1000000) (lit (1/2000000)) = 1 := by decide +kernel
example : 2 * (((1 : Nat) : Int) * 2000000 - 1 * 1000000).natAbs = 2000000 := by decide +kernel

/-! ## FX4: monotone -/

/-- The numerator and denominator are ordered like the values (in the naturals). -/
theorem num_den_le {p q : Prob} (h : p ≤ q) :
    p.val.num.toNat * q.val.den ≤ q.val.num.toNat * p.val.den := by
  have := (Rat.le_iff _ _).mp h
  rw [← num_cast p, ← num_cast q] at this
  omega

/-- The cross-multiplied step of FX4, in the naturals. -/
theorem div_round_mono {a a' d d' n : Nat} (hd : 0 < d) (hd' : 0 < d') (hn : a * d' ≤ a' * d) :
    (2 * a * n + d) / (2 * d) ≤ (2 * a' * n + d') / (2 * d') := by
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) hd')]
  refine Nat.le_of_mul_le_mul_right (c := d) ?_ hd
  have h1 : (2 * a * n + d) / (2 * d) * (2 * d) ≤ 2 * a * n + d := Nat.div_mul_le_self _ _
  have e2 := Nat.mul_le_mul_right d' h1
  have e1 : a * d' * n ≤ a' * d * n := Nat.mul_le_mul_right _ hn
  have q1 : (2 * a * n + d) / (2 * d) * (2 * d') * d = (2 * a * n + d) / (2 * d) * (2 * d) * d' := by
    simp only [Nat.mul_assoc, Nat.mul_comm d' d]
  have q2 : (2 * a * n + d) * d' = 2 * (a * d' * n) + d * d' := by
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm n d']
  have q3 : (2 * a' * n + d') * d = 2 * (a' * d * n) + d' * d := by
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm n d]
  rw [q1]
  rw [q2] at e2
  rw [q3, Nat.mul_comm d' d]
  omega

/-- FX4: `toScaled` is monotone. -/
theorem toScaled_mono (s : Scale) {p q : Prob} (h : p ≤ q) : toScaled s p ≤ toScaled s q :=
  div_round_mono (Nat.pos_of_ne_zero p.val.den_nz) (Nat.pos_of_ne_zero q.val.den_nz) (num_den_le h)

-- Non-vacuity witness for FX4: scale 10, `1/3 ≤ 1/2` and 3 ≤ 5.
example : toScaled (sc 10) (lit (1/3)) ≤ toScaled (sc 10) (lit (1/2)) :=
  toScaled_mono _ (by decide +kernel)
example : toScaled (sc 10) (lit (1/3)) = 3 ∧ toScaled (sc 10) (lit (1/2)) = 5 := by decide +kernel

/-! ## FX5: `ofScaled` -/

/-- FX5: `ofScaled` succeeds exactly when `k` is at most the scale. -/
theorem ofScaled_ok_iff (s : Scale) (k : Nat) : (∃ p, ofScaled s k = .ok p) ↔ k ≤ s.n := by
  unfold ofScaled
  by_cases h : k ≤ s.n <;> simp [h]

/-- FX5: an accepted value is exactly `k / n`. -/
theorem ofScaled_val {s : Scale} {k : Nat} {p : Prob} (h : ofScaled s k = .ok p) :
    p.val = (k : Rat) / (s.n : Rat) := by
  unfold ofScaled at h
  by_cases hk : k ≤ s.n
  · simp only [hk, dite_true, Except.ok.injEq] at h
    cases h; rfl
  · simp [hk] at h

/-- FX5: above the scale it is refused, carrying `k` and the scale. -/
theorem ofScaled_above {s : Scale} {k : Nat} (h : s.n < k) :
    ofScaled s k = .error (.scaledAboveScale k s.n) := by
  have : ¬ k ≤ s.n := by omega
  simp [ofScaled, this]

-- Non-vacuity witnesses for FX5: scale 10^6, 250000 gives 1/4; 1000001 refuses.
example : ∃ p, ofScaled Scale.million 250000 = .ok p ∧ p.val = 1/4 := by
  obtain ⟨p, hp⟩ := (ofScaled_ok_iff Scale.million 250000).mpr (by decide)
  exact ⟨p, hp, by rw [ofScaled_val hp]; decide +kernel⟩
example : ofScaled Scale.million 1000001 = .error (.scaledAboveScale 1000001 1000000) :=
  ofScaled_above (by decide)

/-! ## FX6: `toScaled` after `ofScaled` -/

/-- The value `k / n` cross-multiplied: numerator times `n` is `k` times the denominator. -/
theorem num_mul_scale {s : Scale} {k : Nat} {p : Prob} (h : ofScaled s k = .ok p) :
    p.val.num * (s.n : Int) = (k : Int) * (p.val.den : Int) := by
  have hv := ofScaled_val h
  have hn : (s.n : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.pos_iff_ne_zero.mp s.pos)
  have hd : (p.val.den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr p.val.den_nz
  have e1 : Rat.divInt p.val.num p.val.den = Rat.divInt (k : Int) (s.n : Int) := by
    rw [Rat.num_divInt_den, hv, Rat.divInt_eq_div]; rfl
  exact (Rat.divInt_eq_divInt_iff hd hn).mp e1

/-- FX6: rounding what `ofScaled` built gives back the units. -/
theorem toScaled_ofScaled {s : Scale} {k : Nat} {p : Prob} (h : ofScaled s k = .ok p) :
    toScaled s p = k := by
  have e := num_mul_scale h
  have hc := num_cast p
  have hd := Nat.pos_of_ne_zero p.val.den_nz
  unfold toScaled
  rw [← hc] at e
  have e' : p.val.num.toNat * s.n = k * p.val.den := by omega
  have e'' : 2 * p.val.num.toNat * s.n = 2 * (k * p.val.den) := by rw [Nat.mul_assoc, e']
  rw [e'']
  have e3 : k * (2 * p.val.den) = 2 * (k * p.val.den) := Nat.mul_left_comm _ _ _
  have e4 : (k + 1) * (2 * p.val.den) = 2 * (k * p.val.den) + 2 * p.val.den := by
    rw [Nat.add_mul, Nat.one_mul, e3]
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

-- Non-vacuity witness for FX6: scale 10^6, 250000.
example : ∃ p, ofScaled Scale.million 250000 = .ok p ∧ toScaled Scale.million p = 250000 := by
  obtain ⟨p, hp⟩ := (ofScaled_ok_iff Scale.million 250000).mpr (by decide)
  exact ⟨p, hp, toScaled_ofScaled hp⟩

/-! ## FX7: `ofScaledInt` -/

/-- FX7: a negative integer is refused as `belowZero`, carrying `k / n`. -/
theorem ofScaledInt_neg {s : Scale} {k : Int} (h : k < 0) :
    ofScaledInt s k = .error (.belowZero ((k : Rat) / (s.n : Rat))) := by
  simp [ofScaledInt, h]

/-- FX7: an integer above the scale is refused as `aboveOne`, carrying `k / n`. -/
theorem ofScaledInt_above {s : Scale} {k : Int} (h : (s.n : Int) < k) :
    ofScaledInt s k = .error (.aboveOne ((k : Rat) / (s.n : Rat))) := by
  have : ¬ k < 0 := by omega
  simp [ofScaledInt, this, h]

/-- FX7: an integer in `0..n` agrees with `ofScaled`. -/
theorem ofScaledInt_in_range {s : Scale} {k : Int} (h0 : 0 ≤ k) (h1 : k ≤ (s.n : Int)) :
    ofScaledInt s k = ofScaled s k.toNat := by
  have : ¬ k < 0 := by omega
  have h2 : ¬ (s.n : Int) < k := by omega
  simp [ofScaledInt, this, h2]

/-- FX7: a natural number at most the scale agrees with `ofScaled` itself. -/
theorem ofScaledInt_natCast {s : Scale} {k : Nat} (h : k ≤ s.n) :
    ofScaledInt s (k : Int) = ofScaled s k := by
  rw [ofScaledInt_in_range (Int.natCast_nonneg k) (by omega)]; rfl

-- Non-vacuity witnesses for FX7: scale 10: -1, 0, 10, 11.
example : ofScaledInt (sc 10) (-1) = .error (.belowZero (-1/10)) := by
  rw [ofScaledInt_neg (by decide)]
  exact congrArg (fun q => Except.error (Refusal.belowZero q)) (by decide +kernel)
example : ∃ p, ofScaledInt (sc 10) 0 = .ok p ∧ p.val = 0 := by
  rw [ofScaledInt_in_range (by decide) (by decide)]
  obtain ⟨p, hp⟩ := (ofScaled_ok_iff (sc 10) 0).mpr (by decide)
  exact ⟨p, hp, by rw [ofScaled_val hp]; decide +kernel⟩
example : ∃ p, ofScaledInt (sc 10) 10 = .ok p ∧ p.val = 1 := by
  rw [ofScaledInt_in_range (by decide) (by decide)]
  obtain ⟨p, hp⟩ := (ofScaled_ok_iff (sc 10) 10).mpr (by decide)
  exact ⟨p, hp, by rw [ofScaled_val hp]; decide +kernel⟩
example : ofScaledInt (sc 10) 11 = .error (.aboveOne (11/10)) := by
  rw [ofScaledInt_above (by decide)]
  exact congrArg (fun q => Except.error (Refusal.aboveOne q)) (by decide +kernel)

end VbmProb
