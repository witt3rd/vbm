import VbmRng.Mix
/-! # The mixer's proofs (S1): M1-M4 and the mixer vectors

M1 is proved on `Nat` (a telescoping sum of shifts, then connected to `UInt64`); M2 chains M1 with the odd-multiplier inverses; M3 and M4 are corollaries. -/
namespace VbmRng

/-- The same sum on `Nat`, with no cutoff: `y >> t ⊕ y >> (t + s) ⊕ ...`, `fuel` terms. -/
def xsum (s y : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, t => (y >>> t) ^^^ xsum s y fuel (t + s)

theorem xsum_ge (s y : Nat) (hy : y < 2 ^ 64) :
    ∀ fuel t, 64 ≤ t → xsum s y fuel t = 0
  | 0, _, _ => rfl
  | fuel + 1, t, h => by
    have h0 : y >>> t = 0 := Nat.shiftRight_eq_zero _ _
      (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) h))
    simp only [xsum, h0, xsum_ge s y hy fuel (t + s) (by omega)]
    rfl

theorem toNat_shr (y : UInt64) (t : Nat) (h : t < 64) : (y >>> t.toUInt64).toNat = y.toNat >>> t := by
  have h1 : t.toUInt64.toNat = t := by
    simp [Nat.toUInt64, Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega)]
  rw [UInt64.toNat_shiftRight, h1, Nat.mod_eq_of_lt h]

theorem go_toNat (s : Nat) (y : UInt64) :
    ∀ fuel t, (invXorShiftGo s y fuel t).toNat = xsum s y.toNat fuel t
  | 0, _ => rfl
  | fuel + 1, t => by
    by_cases h : t < 64
    · simp only [invXorShiftGo, xsum, h, ite_true, UInt64.toNat_xor, toNat_shr y t h, go_toNat s y fuel (t + s)]
    · simp only [invXorShiftGo, h, ite_false]
      rw [xsum_ge s y.toNat y.toNat_lt _ _ (by omega)]; rfl

theorem xsum_shift (s y : Nat) : ∀ fuel t, xsum s y fuel t >>> s = xsum s y fuel (t + s)
  | 0, _ => by simp [xsum]
  | fuel + 1, t => by
    simp only [xsum, Nat.shiftRight_xor_distrib, xsum_shift s y fuel (t + s)]
    rw [Nat.shiftRight_add]

theorem xsum_snoc (s y : Nat) : ∀ fuel t, xsum s y (fuel + 1) t = xsum s y fuel t ^^^ (y >>> (t + fuel * s))
  | 0, t => by simp [xsum]
  | fuel + 1, t => by
    have ih := xsum_snoc s y fuel (t + s)
    have e : t + s + fuel * s = t + (fuel + 1) * s := by rw [Nat.succ_mul]; omega
    rw [e] at ih
    simp only [xsum] at ih ⊢
    rw [ih, Nat.xor_assoc]

/-- The forward step after the inverse, on `Nat`. -/
theorem xsum_fwd (s y : Nat) (hy : y < 2 ^ 64) (hs : 1 ≤ s) :
    xsum s y 64 0 ^^^ (xsum s y 64 0 >>> s) = y := by
  rw [xsum_shift]
  have h1 := xsum_snoc s y 63 s
  have h0 : xsum s y 64 0 = y ^^^ xsum s y 63 s := by simp [xsum]
  have h2 : xsum s y 64 s = xsum s y 63 s ^^^ (y >>> (s + 63 * s)) := h1
  have : y >>> (s + 63 * s) = 0 := Nat.shiftRight_eq_zero _ _
    (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [Nat.zero_add, h0, h2, this, Nat.xor_zero, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- The telescoping sum: the inverse applied to `x ⊕ (x >> s)`. -/
theorem xsum_tele (s x : Nat) : ∀ fuel t,
    xsum s (x ^^^ (x >>> s)) fuel t = (x >>> t) ^^^ (x >>> (t + fuel * s))
  | 0, t => by simp [xsum]
  | fuel + 1, t => by
    have ih := xsum_tele s x fuel (t + s)
    have e : t + s + fuel * s = t + (fuel + 1) * s := by rw [Nat.succ_mul]; omega
    rw [e] at ih
    simp only [xsum] at ih ⊢
    have hc : x >>> s >>> t = x >>> t >>> s := by
      rw [← Nat.shiftRight_add, ← Nat.shiftRight_add, Nat.add_comm]
    have hd : x >>> (t + s) = x >>> t >>> s := by rw [Nat.shiftRight_add]
    rw [ih, Nat.shiftRight_xor_distrib, hc, hd, Nat.xor_assoc, ← Nat.xor_assoc (x >>> t >>> s),
      Nat.xor_self, Nat.zero_xor]

/-- **M1 (xor-shift is invertible).** -/
theorem invXorShift_xorshift (s : Nat) (h1 : 1 ≤ s) (h2 : s ≤ 63) (x : UInt64) :
    invXorShift s (x ^^^ (x >>> s.toUInt64)) = x := by
  apply UInt64.toNat_inj.mp
  unfold invXorShift
  rw [go_toNat, UInt64.toNat_xor, toNat_shr x s (by omega), xsum_tele]
  have : x.toNat >>> (0 + 64 * s) = 0 := Nat.shiftRight_eq_zero _ _
    (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [this]; simp

theorem inv31 (x : UInt64) : invXorShift 31 (x ^^^ (x >>> 31)) = x := invXorShift_xorshift 31 (by decide) (by decide) x
theorem inv27 (x : UInt64) : invXorShift 27 (x ^^^ (x >>> 27)) = x := invXorShift_xorshift 27 (by decide) (by decide) x
theorem inv30 (x : UInt64) : invXorShift 30 (x ^^^ (x >>> 30)) = x := invXorShift_xorshift 30 (by decide) (by decide) x

/-- The forward xor-shift undoes `invXorShift`. -/
theorem xorshift_invXorShift (s : Nat) (h1 : 1 ≤ s) (h2 : s ≤ 63) (y : UInt64) :
    invXorShift s y ^^^ (invXorShift s y >>> s.toUInt64) = y := by
  apply UInt64.toNat_inj.mp
  unfold invXorShift
  rw [UInt64.toNat_xor, toNat_shr _ s (by omega), go_toNat]
  exact xsum_fwd s y.toNat y.toNat_lt h1

theorem fwd31 (y : UInt64) : invXorShift 31 y ^^^ (invXorShift 31 y >>> 31) = y := xorshift_invXorShift 31 (by decide) (by decide) y
theorem fwd27 (y : UInt64) : invXorShift 27 y ^^^ (invXorShift 27 y >>> 27) = y := xorshift_invXorShift 27 (by decide) (by decide) y
theorem fwd30 (y : UInt64) : invXorShift 30 y ^^^ (invXorShift 30 y >>> 30) = y := xorshift_invXorShift 30 (by decide) (by decide) y

theorem mulA_mulAInv : mulA * mulAInv = 1 := by decide +kernel
theorem mulB_mulBInv : mulB * mulBInv = 1 := by decide +kernel
theorem gamma_gammaInv : gamma * gammaInv = 1 := by decide +kernel

theorem mul_inv_cancel (a c ci : UInt64) (h : c * ci = 1) : a * c * ci = a := by
  rw [UInt64.mul_assoc, h, UInt64.mul_one]

theorem mul_inv_cancel' (a c ci : UInt64) (h : c * ci = 1) : a * ci * c = a := by
  rw [UInt64.mul_assoc, UInt64.mul_comm ci c, h, UInt64.mul_one]

/-- **M2 (left).** `unmix` undoes `mix`. -/
theorem unmix_mix (x : UInt64) : unmix (mix x) = x := by
  unfold mix unmix
  simp only []
  rw [inv31, mul_inv_cancel _ _ _ mulB_mulBInv, inv27, mul_inv_cancel _ _ _ mulA_mulAInv, inv30]

/-- **M2 (right).** `mix` undoes `unmix`. -/
theorem mix_unmix (y : UInt64) : mix (unmix y) = y := by
  unfold mix unmix
  simp only []
  rw [fwd30, mul_inv_cancel' _ _ _ mulA_mulAInv, fwd27, mul_inv_cancel' _ _ _ mulB_mulBInv, fwd31]

/-- **M3 (mix is injective).** -/
theorem mix_injective {x y : UInt64} (h : mix x = mix y) : x = y := by
  rw [← unmix_mix x, ← unmix_mix y, h]

/-- **M4 (multiplication by `gamma` is injective).** -/
theorem mul_gamma_injective {x y : UInt64} (h : x * gamma = y * gamma) : x = y := by
  rw [← mul_inv_cancel x gamma gammaInv gamma_gammaInv, ← mul_inv_cancel y gamma gammaInv gamma_gammaInv, h]

-- The multipliers and the stream increment are odd.
example : mulA % 2 = 1 ∧ mulB % 2 = 1 ∧ gamma % 2 = 1 := by decide +kernel

-- Non-vacuity witnesses and the mixer vectors (kernel-checked).
example : invXorShift 30 ((0x0123456789ABCDEF : UInt64) ^^^ ((0x0123456789ABCDEF : UInt64) >>> 30))
    = 0x0123456789ABCDEF := by decide +kernel
example : mix 0 = 0 := by decide +kernel
example : mix 1 = 0x5692161D100B05E5 := by decide +kernel
example : mix 2 = 0xDBD238973A2B148A := by decide +kernel
example : mix 0xFFFFFFFFFFFFFFFF = 0xB4D055FCF2CBBD7B := by decide +kernel
example : mix 0x0123456789ABCDEF = 0xB2C058E4EBB5112C := by decide +kernel
example : unmix (mix 1) = 1 := by decide +kernel
example : mix (unmix 0x5692161D100B05E5) = 0x5692161D100B05E5 := by decide +kernel
example : mix 1 ≠ mix 2 := by decide +kernel
example : (7 : UInt64) * gamma = 7 * gamma ∧ gamma * gammaInv = 1 := ⟨rfl, gamma_gammaInv⟩

end VbmRng
