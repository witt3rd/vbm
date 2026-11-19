import VbmRng.Below
import VbmRngProofs.Stream
import VbmRngProofs.Refusal
/-! # The bounded integer's proofs (S5): U1-U7 and the uniformBelow vectors

U2 is a pure `Nat` counting lemma (`count_accepted`): in `[0, N)` the words at least `N % n` with residue `v` number `(N - N % n) / n`, for every residue. U3 characterises the rejection loop by the first accepted index of the stream; U1, U5, U6 and U7 follow from it. U4 is arithmetic. The expectation and the tail of rejection (Q3) are consequences of Q1 and are trusted, see `docs/trust-ledger.md`. -/
namespace VbmRng

/-- Word number `i` of a stream as a natural number. -/
def word (st : Stream) (i : Nat) : Nat := (st.«at» i.toUInt64).toNat

theorem toUInt64_succ (j : Nat) : (j + 1).toUInt64 = j.toUInt64 + 1 := by
  simp only [Nat.toUInt64_eq, UInt64.ofNat_add]; rfl

theorem word_advance (st : Stream) (j : Nat) : word (st.advance 1) j = word st (j + 1) := by
  unfold word
  rw [toUInt64_succ, Stream.at_add]

theorem advance_advance_succ (st : Stream) (i : Nat) :
    (st.advance 1).advance (i + 1).toUInt64 = st.advance (i + 1 + 1).toUInt64 := by
  rw [Stream.advance_advance, toUInt64_succ (i + 1), UInt64.add_comm]

theorem word_zero (st : Stream) : word st 0 = (st.«at» 0).toNat := rfl

/-- **U3 (the specification matches the counting), the accepting case:** the loop returns `v` exactly when `v` is the first accepted word modulo `n`. -/
theorem drawGo_ok (n th : Nat) : ∀ (fuel : Nat) (st : Stream) (v : Nat) (st' : Stream),
    drawGo n th fuel st = .ok (v, st') ↔
      ∃ i, i < fuel ∧ (∀ j, j < i → word st j < th) ∧ th ≤ word st i ∧
        v = word st i % n ∧ st' = st.advance (i + 1).toUInt64
  | 0, st, v, st' => by simp [drawGo]
  | fuel + 1, st, v, st' => by
    by_cases h : th ≤ word st 0
    · have h' : th ≤ (st.«at» 0).toNat := h
      simp only [drawGo, h', ite_true, Except.ok.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨0, by omega, fun j hj => by omega, h, rfl, rfl⟩
      · rintro ⟨i, _, hj, hi, rfl, rfl⟩
        have : i = 0 := by
          by_cases hi0 : i = 0
          · exact hi0
          · exact absurd (hj 0 (by omega)) (by omega)
        subst this
        exact ⟨rfl, rfl⟩
    · have h' : ¬ th ≤ (st.«at» 0).toNat := h
      simp only [drawGo, h', ite_false]
      rw [drawGo_ok n th fuel (st.advance 1) v st']
      constructor
      · rintro ⟨i, hi, hj, hth, hv, hst⟩
        refine ⟨i + 1, by omega, ?_, ?_, ?_, ?_⟩
        · intro j hjl
          cases j with
          | zero => omega
          | succ j => have := hj j (by omega); rw [word_advance] at this; exact this
        · rw [word_advance] at hth; exact hth
        · rw [word_advance] at hv; exact hv
        · rw [hst, advance_advance_succ]
      · rintro ⟨i, hi, hj, hth, hv, hst⟩
        cases i with
        | zero => omega
        | succ i =>
          refine ⟨i, by omega, ?_, ?_, ?_, ?_⟩
          · intro j hjl; have := hj (j + 1) (by omega); rw [← word_advance] at this; exact this
          · rw [word_advance]; exact hth
          · rw [word_advance]; exact hv
          · rw [hst, advance_advance_succ]

/-- The refusing case: the loop refuses exactly when all of its fuel is rejected. -/
theorem drawGo_error (n th : Nat) : ∀ (fuel : Nat) (st : Stream) (e : Refusal),
    drawGo n th fuel st = .error e ↔ e = .fuelExhausted ∧ ∀ i, i < fuel → word st i < th
  | 0, st, e => by simp [drawGo, eq_comm]
  | fuel + 1, st, e => by
    by_cases h : th ≤ word st 0
    · have h' : th ≤ (st.«at» 0).toNat := h
      simp only [drawGo, h', ite_true]
      constructor
      · intro hh; cases hh
      · rintro ⟨_, hall⟩; have := hall 0 (by omega); omega
    · have h' : ¬ th ≤ (st.«at» 0).toNat := h
      simp only [drawGo, h', ite_false]
      rw [drawGo_error n th fuel (st.advance 1) e]
      constructor
      · rintro ⟨he, hall⟩
        refine ⟨he, fun i hi => ?_⟩
        cases i with
        | zero => omega
        | succ i => have := hall i (by omega); rw [word_advance] at this; exact this
      · rintro ⟨he, hall⟩
        exact ⟨he, fun i hi => by rw [word_advance]; exact hall (i + 1) (by omega)⟩

theorem drawGo_lt (n th : Nat) (hn : 0 < n) : ∀ (fuel : Nat) (st : Stream) (v : Nat) (st' : Stream),
    drawGo n th fuel st = .ok (v, st') → v < n := by
  intro fuel st v st' h
  obtain ⟨i, _, _, _, hv, _⟩ := (drawGo_ok n th fuel st v st').mp h
  rw [hv]; exact Nat.mod_lt _ hn

theorem uniformBelowWith_eq {fuel n : Nat} (hn : 0 < n) (hle : n ≤ 2 ^ 64) (st : Stream) :
    uniformBelowWith fuel n st = drawGo n (threshold n) fuel st := by
  have h0 : n ≠ 0 := by omega
  have h1 : ¬ 2 ^ 64 < n := by omega
  simp [uniformBelowWith, maxBound, h0, h1]

theorem uniformBelowWith_valid {fuel n : Nat} {st : Stream} {r : Nat × Stream}
    (h : uniformBelowWith fuel n st = .ok r) : 0 < n ∧ n ≤ 2 ^ 64 := by
  unfold uniformBelowWith maxBound at h
  by_cases h0 : n = 0
  · simp [h0] at h
  · by_cases h1 : 2 ^ 64 < n
    · simp [h0, h1] at h
    · omega

/-- **U1 (the result is in range).** -/
theorem uniformBelowWith_lt {fuel n : Nat} {st st' : Stream} {v : Nat}
    (h : uniformBelowWith fuel n st = .ok (v, st')) : v < n ∧ 0 < n ∧ n ≤ 2 ^ 64 := by
  have hv := uniformBelowWith_valid h
  refine ⟨?_, hv⟩
  rw [uniformBelowWith_eq hv.1 hv.2] at h
  exact drawGo_lt n _ hv.1 _ _ _ _ h

theorem uniformBelow_lt {n : Nat} {st st' : Stream} {v : Nat}
    (h : uniformBelow n st = .ok (v, st')) : v < n ∧ 0 < n ∧ n ≤ 2 ^ 64 :=
  uniformBelowWith_lt h

/-- **U3 (the specification matches the counting):** for a valid bound the result is the first word at least `threshold n`, modulo `n`, and the stream advanced past it. -/
theorem uniformBelowWith_ok_iff {fuel n : Nat} (hn : 0 < n) (hle : n ≤ 2 ^ 64) (st : Stream) (v : Nat) (st' : Stream) :
    uniformBelowWith fuel n st = .ok (v, st') ↔
      ∃ i, i < fuel ∧ (∀ j, j < i → word st j < threshold n) ∧ threshold n ≤ word st i ∧
        v = word st i % n ∧ st' = st.advance (i + 1).toUInt64 := by
  rw [uniformBelowWith_eq hn hle]
  exact drawGo_ok n _ fuel st v st'

theorem uniformBelowWith_error_iff {fuel n : Nat} (hn : 0 < n) (hle : n ≤ 2 ^ 64) (st : Stream) (e : Refusal) :
    uniformBelowWith fuel n st = .error e ↔ e = .fuelExhausted ∧ ∀ i, i < fuel → word st i < threshold n := by
  rw [uniformBelowWith_eq hn hle]
  exact drawGo_error n _ fuel st e

/-- **U7 (determinism and advance).** The result is a function of `(fuel, n, st)`. -/
theorem uniformBelowWith_det {f f' n n' : Nat} {st st' : Stream} (hf : f = f') (hn : n = n') (hs : st = st') :
    uniformBelowWith f n st = uniformBelowWith f' n' st' := by subst hf; subst hn; subst hs; rfl

/-- **U7 (advance).** On success the stream advanced by `k` words, `1 ≤ k ≤ fuel`. -/
theorem uniformBelowWith_advance {fuel n : Nat} {st st' : Stream} {v : Nat}
    (h : uniformBelowWith fuel n st = .ok (v, st')) :
    ∃ k, 1 ≤ k ∧ k ≤ fuel ∧ st' = st.advance k.toUInt64 := by
  have hv := uniformBelowWith_valid h
  obtain ⟨i, hi, _, _, _, hst⟩ := (uniformBelowWith_ok_iff hv.1 hv.2 st v st').mp h
  exact ⟨i + 1, by omega, by omega, hst⟩

/-- **U6 (refusals), zero bound.** -/
theorem uniformBelowWith_boundZero (fuel : Nat) (st : Stream) : uniformBelowWith fuel 0 st = .error .boundZero := by
  simp [uniformBelowWith]

/-- **U6 (refusals), a bound above the word size.** -/
theorem uniformBelowWith_boundTooLarge (fuel : Nat) {n : Nat} (h : 2 ^ 64 < n) (st : Stream) :
    uniformBelowWith fuel n st = .error .boundTooLarge := by
  have h0 : n ≠ 0 := by omega
  simp [uniformBelowWith, maxBound, h0, h]

/-- **U6 (refusals), no fuel.** -/
theorem uniformBelowWith_zero_fuel {n : Nat} (hn : 0 < n) (hle : n ≤ 2 ^ 64) (st : Stream) :
    uniformBelowWith 0 n st = .error .fuelExhausted := by
  rw [uniformBelowWith_eq hn hle]; rfl

theorem accepted_aux (n q r : Nat) (h2 : n * q + r = 2 ^ 64) (h1 : r < n) (hle : n ≤ 2 ^ 64) :
    2 ^ 63 < 2 ^ 64 - r := by
  by_cases hs : n ≤ 2 ^ 63
  · omega
  · rcases q with _ | _ | q
    · simp at h2; omega
    · simp at h2; omega
    · simp only [Nat.mul_add, Nat.mul_one] at h2
      omega

/-- **U4 (accepted fraction):** more than half of all words are accepted. -/
theorem accepted_gt_half {n : Nat} (hn : 0 < n) (hle : n ≤ 2 ^ 64) : 2 ^ 63 < 2 ^ 64 - threshold n :=
  accepted_aux n (2 ^ 64 / n) (2 ^ 64 % n) (Nat.div_add_mod (2 ^ 64) n) (Nat.mod_lt _ hn) hle

/-- **U5 (the fuel is enough when the threshold is small).** -/
theorem uniformBelowWith_ne_fuelExhausted {fuel n : Nat} (h : threshold n < fuel) (st : Stream) :
    uniformBelowWith fuel n st ≠ .error .fuelExhausted := by
  intro he
  by_cases h0 : n = 0
  · subst h0; rw [uniformBelowWith_boundZero] at he; cases he
  by_cases h1 : 2 ^ 64 < n
  · rw [uniformBelowWith_boundTooLarge fuel h1] at he; cases he
  have hn : 0 < n := by omega
  have hle : n ≤ 2 ^ 64 := by omega
  have hall := ((uniformBelowWith_error_iff (fuel := fuel) hn hle st _).mp he).2
  have hth : threshold n < n := Nat.mod_lt _ hn
  have hinj : ∀ i j, i < threshold n + 1 → j < threshold n + 1 → word st i = word st j → i = j := by
    intro i j hi hj e
    have e1 : (st.«at» i.toUInt64) = st.«at» j.toUInt64 := UInt64.toNat_inj.mp e
    have e2 := Stream.at_injective st e1
    have e3 : i % 2 ^ 64 = j % 2 ^ 64 := by
      have := congrArg UInt64.toNat e2
      simpa [Nat.toUInt64_eq] using this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e3
  have hnd : ((List.range (threshold n + 1)).map (word st)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact (List.nodup_range (n := threshold n + 1)).imp_of_mem (fun {a b} ha hb hne e =>
      hne (hinj a b (List.mem_range.mp ha) (List.mem_range.mp hb) e))
  have hsub : (List.range (threshold n + 1)).map (word st) ⊆ List.range (threshold n) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (hall i (by have := List.mem_range.mp hi; omega))
  have := hnd.length_le_of_subset hsub
  rw [List.length_map, List.length_range, List.length_range] at this
  omega

/-! ### U2: exactness, a pure counting lemma on `Nat` -/

theorem count_range_eq (v : Nat) : ∀ m, (List.range m).countP (fun w => decide (w = v)) = if v < m then 1 else 0
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.countP_append, count_range_eq v m]
    by_cases h : v < m
    · have : m ≠ v := by omega
      simp [h, this]; omega
    · by_cases h2 : m = v
      · subst h2; simp
      · simp [h, h2]; omega

/-- A window of `n` consecutive numbers holds exactly one number of each residue. -/
theorem count_block {n : Nat} (hn : 0 < n) (v : Nat) (hv : v < n) :
    ∀ s, (List.range' s n).countP (fun w => decide (w % n = v)) = 1
  | 0 => by
    rw [← List.range_eq_range']
    have : (List.range n).countP (fun w => decide (w % n = v)) = (List.range n).countP (fun w => decide (w = v)) :=
      List.countP_congr (fun x hx => by
        have := List.mem_range.mp hx
        simp [Nat.mod_eq_of_lt this])
    rw [this, count_range_eq]; simp [hv]
  | s + 1 => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have ih := count_block hn v hv s
    rw [List.range'_succ, List.countP_cons] at ih
    rw [List.range'_concat, List.countP_append]
    have e3 : (s + 1 + n') % (n' + 1) = s % (n' + 1) := by
      rw [show s + 1 + n' = s + (n' + 1) by omega, Nat.add_mod_right]
    simp only [Nat.one_mul, List.countP_cons, List.countP_nil] at ih ⊢
    rw [e3]
    omega

/-- `q` whole windows from `s` hold `q` numbers of each residue. -/
theorem count_blocks {n : Nat} (hn : 0 < n) (v : Nat) (hv : v < n) :
    ∀ q s, (List.range' s (n * q)).countP (fun w => decide (w % n = v)) = q
  | 0, s => by simp
  | q + 1, s => by
    have : n * (q + 1) = n + n * q := by rw [Nat.mul_succ]; omega
    rw [this, ← List.range'_append, List.countP_append, count_block hn v hv s]
    have h2 : (List.range' (s + 1 * n) (n * q)).countP (fun w => decide (w % n = v)) = q := by
      rw [Nat.one_mul, Nat.add_comm s n]; exact count_blocks hn v hv q (n + s)
    rw [h2]; omega

/-- The count of a window starting at `th` of length `n * q` is `q` for each residue. -/
theorem count_range_ge {N n : Nat} (hn : 0 < n) (v : Nat) (hv : v < n) :
    (List.range N).countP (fun w => decide (N % n ≤ w ∧ w % n = v)) = (N - N % n) / n := by
  have hq : N - N % n = n * (N / n) := by
    have := Nat.div_add_mod N n
    omega
  have hle : N % n ≤ N := Nat.mod_le N n
  have hsplit : List.range N = List.range' 0 (N % n) ++ List.range' (N % n) (n * (N / n)) := by
    have h := List.range'_append (s := 0) (m := N % n) (n := n * (N / n)) (step := 1)
    rw [Nat.one_mul, Nat.zero_add] at h
    rw [List.range_eq_range', h]
    congr 1
    have := Nat.div_add_mod N n
    omega
  rw [hsplit, List.countP_append]
  have h0 : (List.range' 0 (N % n)).countP (fun w => decide (N % n ≤ w ∧ w % n = v)) = 0 := by
    rw [List.countP_eq_zero]
    intro w hw
    have := (List.mem_range'.mp hw)
    simp only [decide_eq_true_eq, not_and]
    intro h; omega
  have h1 : (List.range' (N % n) (n * (N / n))).countP (fun w => decide (N % n ≤ w ∧ w % n = v)) =
      (List.range' (N % n) (n * (N / n))).countP (fun w => decide (w % n = v)) := by
    apply List.countP_congr
    intro w hw
    have := (List.mem_range'.mp hw)
    obtain ⟨i, _, rfl⟩ := this
    simp only [decide_eq_true_eq]
    omega
  rw [h0, h1, count_blocks hn v hv, hq, Nat.mul_div_cancel_left _ hn]
  omega

/-- **U2 (exactness):** among the `2^64` words, those at least `threshold n` with residue `v` number `(2^64 - threshold n) / n`, the same for every `v < n`. -/
theorem uniformBelow_exact {n : Nat} (hn : 0 < n) (v : Nat) (hv : v < n) :
    (List.range (2 ^ 64)).countP (fun w => decide (threshold n ≤ w ∧ w % n = v)) = (2 ^ 64 - threshold n) / n :=
  count_range_ge hn v hv

-- Non-vacuity witnesses for U2: the scaled-down analogue (8-bit words, `n = 10`: threshold 6, 25 each) and the full width.
example : (List.range 256).countP (fun w => decide (256 % 10 ≤ w ∧ w % 10 = 7)) = 25 := by decide +kernel
example : (256 % 10 = 6) ∧ (256 - 256 % 10) / 10 = 25 := by decide
example : threshold 10 = 6 ∧ (2 ^ 64 - threshold 10) / 10 = 1844674407370955161 := by decide +kernel
example : threshold (2 ^ 64) = 0 ∧ (2 ^ 64 - threshold (2 ^ 64)) / 2 ^ 64 = 1 := by decide +kernel
example : (List.range (2 ^ 64)).countP (fun w => decide (threshold 10 ≤ w ∧ w % 10 = 3)) = 1844674407370955161 :=
  uniformBelow_exact (by decide) 3 (by decide)

-- Non-vacuity witnesses for U1, U4, U5, U6.
/-- The value and the position of a successful draw (for the vectors). -/
def okVals (r : DrawWith Stream Nat) : Option (Nat × UInt64) :=
  match r with
  | .ok (v, st) => some (v, st.pos)
  | .error _ => none

/-- The refusal of a refused draw (for the vectors). -/
def errOf (r : DrawWith Stream Nat) : Option Refusal :=
  match r with
  | .ok _ => none
  | .error e => some e

/-- `k` draws in a row below `n`: the values and the final position. -/
def draws : Nat → Nat → Stream → Option (List Nat × UInt64)
  | 0, _, st => some ([], st.pos)
  | k + 1, n, st =>
    match uniformBelow n st with
    | .ok (v, st') => (draws k n st').map fun r => (v :: r.1, r.2)
    | .error _ => none

example : okVals (uniformBelow 10 (Stream.ofSeed 1)) = some (0, 1) := by decide +kernel
example : 2 ^ 63 < 2 ^ 64 - threshold 10 := accepted_gt_half (by decide) (by decide)
example : uniformBelowWith 64 1 (Stream.ofSeed 1) ≠ .error .fuelExhausted :=
  uniformBelowWith_ne_fuelExhausted (by decide) _
example : uniformBelowWith 64 3 (Stream.ofSeed 1) ≠ .error .fuelExhausted :=
  uniformBelowWith_ne_fuelExhausted (by decide) _
example : uniformBelowWith 64 (2 ^ 64) (Stream.ofSeed 1) ≠ .error .fuelExhausted :=
  uniformBelowWith_ne_fuelExhausted (by decide) _
example : threshold 1 = 0 ∧ threshold 3 = 1 ∧ threshold (2 ^ 64) = 0 := by decide +kernel
example (st : Stream) : uniformBelow 0 st = .error .boundZero := uniformBelowWith_boundZero _ _
example (st : Stream) : uniformBelow (2 ^ 64 + 1) st = .error .boundTooLarge :=
  uniformBelowWith_boundTooLarge _ (by omega) _
example (st : Stream) : uniformBelowWith 0 7 st = .error .fuelExhausted :=
  uniformBelowWith_zero_fuel (by decide) (by decide) _
example : errOf (uniformBelowWith 1 (2 ^ 63 + 1) (Stream.ofSeed 1)) = some .fuelExhausted := by decide +kernel

-- The uniformBelow vectors (three draws in a row, then the position).
example : draws 3 10 (Stream.ofSeed 1) = some ([0, 3, 2], 3) := by decide +kernel
example : draws 3 10 (Stream.ofSeed 0) = some ([8, 8, 1], 3) := by decide +kernel
example : draws 3 7 (Stream.ofSeed 0) = some ([4, 6, 4], 3) := by decide +kernel
example : draws 3 1 (Stream.ofSeed 1) = some ([0, 0, 0], 3) := by decide +kernel
example : draws 3 (2 ^ 64) (Stream.ofSeed 1) =
    some ([1572369170352337190, 15161360428669594083, 17081804703922980912], 3) := by decide +kernel
example : draws 3 (2 ^ 63 + 1) (Stream.ofSeed 3) =
    some ([4658251182101344059, 2841104050483902510, 8369637337981164616], 5) := by decide +kernel
example : draws 1 (2 ^ 63 + 1) (Stream.ofSeed 1) = some ([5937988391814818274], 2) := by decide +kernel
-- U3: the first word is below the threshold `2^63 - 1` and is rejected; the second is accepted.
example : threshold (2 ^ 63 + 1) = 2 ^ 63 - 1 ∧ word (Stream.ofSeed 1) 0 = 0x15D22D6DFEA07126 ∧
    word (Stream.ofSeed 1) 0 < threshold (2 ^ 63 + 1) ∧ threshold (2 ^ 63 + 1) ≤ word (Stream.ofSeed 1) 1 := by
  decide +kernel

-- Non-vacuity of the conditional theorems: a concrete successful draw (U1, U3, U7) and a concrete refusal (U3).
theorem draw_ten : uniformBelow 10 (Stream.ofSeed 1) = .ok (0, (Stream.ofSeed 1).advance 1) := by
  rfl
example : 0 < 10 ∧ 0 < 10 ∧ 10 ≤ 2 ^ 64 := by
  have h := uniformBelow_lt draw_ten
  exact ⟨h.1, h.2⟩
example : ∃ k, 1 ≤ k ∧ k ≤ rejectionFuel ∧ (Stream.ofSeed 1).advance 1 = (Stream.ofSeed 1).advance k.toUInt64 :=
  uniformBelowWith_advance draw_ten
example : ∃ i, i < rejectionFuel ∧ (∀ j, j < i → word (Stream.ofSeed 1) j < threshold 10) ∧
    threshold 10 ≤ word (Stream.ofSeed 1) i ∧ 0 = word (Stream.ofSeed 1) i % 10 ∧
    (Stream.ofSeed 1).advance 1 = (Stream.ofSeed 1).advance (i + 1).toUInt64 :=
  (uniformBelowWith_ok_iff (by decide) (by decide) _ _ _).mp draw_ten

end VbmRng
