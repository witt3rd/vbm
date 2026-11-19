import VbmRng.Fraction
import VbmRngProofs.Stream
import VbmRngProofs.Refusal
/-! # The fraction's proofs (S6): F1-F4 and the fraction vectors

F2 is a pure `Nat` counting lemma (`count_div`): among the first `c * d` numbers exactly `d` have quotient `m` by `d`, for every `m < c`. The shift of the specification is that quotient (`shift_toNat`), which connects the count to the words. -/
namespace VbmRng

theorem uniformFraction_eq {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 64) (st : Stream) :
    uniformFraction k st =
      .ok ({ num := (st.next.1 >>> (64 - k).toUInt64).toNat, bits := k }, st.next.2) := by
  have : ¬ (k = 0 ∨ 64 < k) := by omega
  simp [uniformFraction, this]

/-- The shift of the specification is division by `2^(64-k)`. -/
theorem shift_toNat {k : Nat} (h1 : 1 ≤ k) (w : UInt64) :
    (w >>> (64 - k).toUInt64).toNat = w.toNat / 2 ^ (64 - k) := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have : (64 - k).toUInt64.toNat % 64 = 64 - k := by
    simp only [Nat.toUInt64_eq]
    have e : (UInt64.ofNat (64 - k)).toNat = 64 - k := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    rw [e]
    exact Nat.mod_eq_of_lt (by omega)
  rw [this]

theorem uniformFraction_valid {k : Nat} {st : Stream} {r : Fraction × Stream}
    (h : uniformFraction k st = .ok r) : 1 ≤ k ∧ k ≤ 64 := by
  unfold uniformFraction at h
  by_cases hk : k = 0 ∨ 64 < k
  · simp [hk] at h
  · omega

/-- **F1 (in range):** on success `num < 2^bits` and `bits = k`, with `1 ≤ k ≤ 64`. -/
theorem uniformFraction_lt {k : Nat} {st st' : Stream} {f : Fraction}
    (h : uniformFraction k st = .ok (f, st')) : f.num < 2 ^ f.bits ∧ f.bits = k ∧ 1 ≤ k ∧ k ≤ 64 := by
  have hv := uniformFraction_valid h
  rw [uniformFraction_eq hv.1 hv.2] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  refine ⟨?_, rfl, hv⟩
  show (st.next.1 >>> (64 - k).toUInt64).toNat < 2 ^ k
  rw [shift_toNat hv.1]
  have hw : st.next.1.toNat < 2 ^ 64 := st.next.1.toNat_lt
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  rwa [show k + (64 - k) = 64 by omega]

/-- **F3 (refusals), zero bits.** -/
theorem uniformFraction_zero (st : Stream) : uniformFraction 0 st = .error .fractionBitsOutOfRange := by
  simp [uniformFraction]

/-- **F3 (refusals), more than 64 bits.** -/
theorem uniformFraction_tooMany {k : Nat} (h : 64 < k) (st : Stream) :
    uniformFraction k st = .error .fractionBitsOutOfRange := by
  simp [uniformFraction, h]

/-- **F4 (consumption):** on success the advanced stream is `st.advance 1`. -/
theorem uniformFraction_advance {k : Nat} {st st' : Stream} {f : Fraction}
    (h : uniformFraction k st = .ok (f, st')) : st' = st.advance 1 := by
  have hv := uniformFraction_valid h
  rw [uniformFraction_eq hv.1 hv.2] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

/-- The result is a function of `(k, st)`. -/
theorem uniformFraction_det {k k' : Nat} {st st' : Stream} (hk : k = k') (hs : st = st') :
    uniformFraction k st = uniformFraction k' st' := by subst hk; subst hs; rfl

/-! ### F2: exactness, a pure counting lemma on `Nat` -/

/-- A window of `d` numbers starting at `c * d` all have quotient `c` by `d`. -/
theorem count_div_block {d : Nat} (hd : 0 < d) (c m : Nat) :
    (List.range' (c * d) d).countP (fun w => decide (w / d = m)) = if m = c then d else 0 := by
  have hall : ∀ w ∈ List.range' (c * d) d, w / d = c := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hw
    rw [Nat.one_mul]
    rw [Nat.mul_comm, Nat.mul_add_div hd, Nat.div_eq_of_lt hi, Nat.add_zero]
  by_cases h : m = c
  · subst h
    rw [List.countP_eq_length.mpr (fun w hw => by simpa using hall w hw), List.length_range']
    simp
  · simp only [h, ite_false]
    rw [List.countP_eq_zero]
    intro w hw
    have := hall w hw
    simp only [decide_eq_true_eq]
    omega

/-- Among the first `c * d` numbers exactly `d` have quotient `m` by `d` when `m < c`, and none otherwise. -/
theorem count_div {d : Nat} (hd : 0 < d) (m : Nat) :
    ∀ c, (List.range (c * d)).countP (fun w => decide (w / d = m)) = if m < c then d else 0
  | 0 => by simp
  | c + 1 => by
    have hs : List.range ((c + 1) * d) = List.range (c * d) ++ List.range' (c * d) d := by
      have h := List.range'_append (s := 0) (m := c * d) (n := d) (step := 1)
      rw [Nat.one_mul, Nat.zero_add] at h
      rw [List.range_eq_range', List.range_eq_range', h, Nat.succ_mul]
    rw [hs, List.countP_append, count_div hd m c, count_div_block hd c m]
    by_cases h1 : m < c
    · have : m ≠ c := by omega
      simp [h1, this]; omega
    · by_cases h2 : m = c
      · subst h2; simp
      · have : ¬ m < c + 1 := by omega
        simp [h1, h2, this]

/-- **F2 (exactness):** for `1 ≤ k ≤ 64` and `m < 2^k`, exactly `2^(64-k)` of the `2^64` words have top `k` bits `m` (`w / 2^(64-k) = m`, which is `w >> (64 - k)` by `shift_toNat`). -/
theorem uniformFraction_exact {k : Nat} (h2 : k ≤ 64) (m : Nat) (hm : m < 2 ^ k) :
    (List.range (2 ^ 64)).countP (fun w => decide (w / 2 ^ (64 - k) = m)) = 2 ^ (64 - k) := by
  have h64 : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h64, count_div (Nat.two_pow_pos _)]
  simp [hm]

/-- **F2, connected to the specification:** the same count with the shift of `uniformFraction` applied to the word. -/
theorem uniformFraction_exact_shift {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 64) (m : Nat) (hm : m < 2 ^ k) :
    (List.range (2 ^ 64)).countP (fun w => decide ((w.toUInt64 >>> (64 - k).toUInt64).toNat = m)) = 2 ^ (64 - k) := by
  rw [← uniformFraction_exact h2 m hm]
  apply List.countP_congr
  intro w hw
  have hw' := List.mem_range.mp hw
  have : w.toUInt64.toNat = w := by
    simp only [Nat.toUInt64_eq]; rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hw'
  simp only [shift_toNat h1, this]

-- Non-vacuity witnesses for F2: the scaled-down analogue (8-bit words, 3 bits: 32 each) and the full width (1 each).
example : (List.range 256).countP (fun w => decide (w / 2 ^ (8 - 3) = 5)) = 2 ^ (8 - 3) := by decide +kernel
example : (List.range (2 ^ 64)).countP (fun w => decide (w / 2 ^ (64 - 3) = 5)) = 2 ^ (64 - 3) :=
  uniformFraction_exact (by decide) 5 (by decide)
example : (List.range (2 ^ 64)).countP (fun w => decide (w / 2 ^ (64 - 64) = 12345)) = 1 :=
  uniformFraction_exact (by decide) 12345 (by decide)

example : (List.range (2 ^ 64)).countP (fun w => decide ((w.toUInt64 >>> (64 - 8).toUInt64).toNat = 21)) = 2 ^ (64 - 8) :=
  uniformFraction_exact_shift (by decide) (by decide) 21 (by decide)

-- Non-vacuity witnesses for F1, F4 (a concrete success) and F3 (the two refusals).
/-- The numerator, bit count and position of a successful draw (for the vectors). -/
def fracVals (r : DrawWith Stream Fraction) : Option (Nat × Nat × UInt64) :=
  match r with
  | .ok (f, st) => some (f.num, f.bits, st.pos)
  | .error _ => none

/-- The refusal of a refused fraction draw (for the vectors). -/
def fracErr (r : DrawWith Stream Fraction) : Option Refusal :=
  match r with
  | .ok _ => none
  | .error e => some e

theorem fraction_eight : uniformFraction 8 (Stream.ofSeed 1) =
    .ok ({ num := 21, bits := 8 }, (Stream.ofSeed 1).advance 1) := by rfl
example : 21 < 2 ^ 8 ∧ 8 = 8 ∧ 1 ≤ 8 ∧ 8 ≤ 64 := uniformFraction_lt fraction_eight
example : (Stream.ofSeed 1).advance 1 = (Stream.ofSeed 1).advance 1 := uniformFraction_advance fraction_eight
example (st : Stream) : uniformFraction 0 st = .error .fractionBitsOutOfRange := uniformFraction_zero st
example (st : Stream) : uniformFraction 65 st = .error .fractionBitsOutOfRange :=
  uniformFraction_tooMany (by decide) st
example : fracErr (uniformFraction 0 (Stream.ofSeed 1)) = some .fractionBitsOutOfRange := by decide +kernel
example : fracErr (uniformFraction 65 (Stream.ofSeed 1)) = some .fractionBitsOutOfRange := by decide +kernel

-- The uniformFraction vectors (`num` for k = 1, 8, 53, 64; position 1).
example : fracVals (uniformFraction 1 (Stream.ofSeed 0)) = some (1, 1, 1) := by decide +kernel
example : fracVals (uniformFraction 8 (Stream.ofSeed 0)) = some (250, 8, 1) := by decide +kernel
example : fracVals (uniformFraction 53 (Stream.ofSeed 0)) = some (8818418357062403, 53, 1) := by decide +kernel
example : fracVals (uniformFraction 64 (Stream.ofSeed 0)) = some (18060120795263802588, 64, 1) := by decide +kernel
example : fracVals (uniformFraction 1 (Stream.ofSeed 1)) = some (0, 1, 1) := by decide +kernel
example : fracVals (uniformFraction 8 (Stream.ofSeed 1)) = some (21, 8, 1) := by decide +kernel
example : fracVals (uniformFraction 53 (Stream.ofSeed 1)) = some (767758383961102, 53, 1) := by decide +kernel
example : fracVals (uniformFraction 64 (Stream.ofSeed 1)) = some (1572369170352337190, 64, 1) := by decide +kernel

end VbmRng
