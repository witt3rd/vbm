import VbmRng.Bernoulli
import VbmRngProofs.Below
/-! # The Bernoulli proofs (S8): B1-B4 and the bernoulli vectors

B1 is a pure `Nat` counting argument on top of U2 (`uniformBelow_exact`): among the accepted words, those with residue below `k` number `k * q` where `q = (2^64 - threshold den) / den`, and all accepted words number `den * q`, so `true` has the exact share `num / den`. B2-B4 follow from the equation of the definition. -/
namespace VbmRng

theorem bernoulli_eq {num : Int} {den : Nat} (h0 : 0 < den) (h1 : 0 ≤ num) (h2 : num ≤ den) (h3 : den ≤ 2 ^ 64)
    (st : Stream) :
    bernoulli num den st =
      match uniformBelow den st with
      | .error e => .error e
      | .ok (u, st') => .ok (decide ((u : Int) < num), st') := by
  have e0 : den ≠ 0 := by omega
  have e1 : ¬ (num < 0 ∨ (den : Int) < num) := by omega
  have e2 : ¬ maxBound < den := by unfold maxBound; omega
  simp only [bernoulli, e0, e1, e2, ite_false]
  rfl

theorem bernoulli_valid {num : Int} {den : Nat} {st : Stream} {r : Bool × Stream}
    (h : bernoulli num den st = .ok r) : 0 < den ∧ 0 ≤ num ∧ num ≤ den ∧ den ≤ 2 ^ 64 := by
  unfold bernoulli maxBound at h
  by_cases h0 : den = 0
  · simp [h0] at h
  · by_cases h1 : num < 0 ∨ (den : Int) < num
    · simp [h0, h1] at h
    · by_cases h2 : 2 ^ 64 < den
      · simp [h0, h1, h2] at h
      · omega

/-- The success equation: the Boolean is `u < num` for the drawn `u`. -/
theorem bernoulli_ok_iff {num : Int} {den : Nat} (h0 : 0 < den) (h1 : 0 ≤ num) (h2 : num ≤ den)
    (h3 : den ≤ 2 ^ 64) (st : Stream) (b : Bool) (st' : Stream) :
    bernoulli num den st = .ok (b, st') ↔
      ∃ u, uniformBelow den st = .ok (u, st') ∧ b = decide ((u : Int) < num) := by
  rw [bernoulli_eq h0 h1 h2 h3]
  cases hu : uniformBelow den st with
  | error e => simp
  | ok r =>
    obtain ⟨u, s⟩ := r
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hb, hs⟩; exact ⟨u, ⟨rfl, hs⟩, hb.symm⟩
    · rintro ⟨u', ⟨hu', hs⟩, hb⟩
      have : u' = u := hu'.symm
      subst this
      exact ⟨hb.symm, hs⟩

/-! ### B1: exactness, a pure counting argument on `Nat` -/

theorem countP_or {α : Type} (A B : α → Bool) (hd : ∀ x, ¬ (A x = true ∧ B x = true)) :
    ∀ l : List α, l.countP (fun x => A x || B x) = l.countP A + l.countP B
  | [] => by simp
  | x :: l => by
    rw [List.countP_cons, List.countP_cons, List.countP_cons, countP_or A B hd l]
    have := hd x
    cases ha : A x <;> cases hb : B x <;> simp_all <;> omega

theorem count_range_lt (k : Nat) : ∀ d, (List.range d).countP (fun u => decide (u < k)) = min d k
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.countP_append, count_range_lt k d]
    by_cases h : d < k <;> simp [h] <;> omega

/-- **B1 (exactness), the values:** among `u ∈ [0, den)` exactly `num` satisfy `u < num`. -/
theorem bernoulli_count_values {num : Int} {den : Nat} (h1 : 0 ≤ num) (h2 : num ≤ den) :
    (List.range den).countP (fun u : Nat => decide ((u : Int) < num)) = num.toNat := by
  have : ∀ u : Nat, decide ((u : Int) < num) = decide (u < num.toNat) := by
    intro u; simp only [decide_eq_decide]; omega
  rw [List.countP_congr (fun u _ => by rw [this u]), count_range_lt]
  omega

/-- Among the accepted words, those with residue below `k` number `k * q`, for `k ≤ n`. -/
theorem count_accepted_lt {n : Nat} (hn : 0 < n) :
    ∀ k, k ≤ n → (List.range (2 ^ 64)).countP (fun w => decide (threshold n ≤ w ∧ w % n < k)) =
      k * ((2 ^ 64 - threshold n) / n)
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := count_accepted_lt hn k (by omega)
    have hv := uniformBelow_exact hn k (by omega)
    have hor : ∀ w : Nat, decide (threshold n ≤ w ∧ w % n < k + 1) =
        (decide (threshold n ≤ w ∧ w % n < k) || decide (threshold n ≤ w ∧ w % n = k)) := by
      intro w
      by_cases h1 : threshold n ≤ w <;> by_cases h2 : w % n < k <;> by_cases h3 : w % n = k <;> simp [h1, h2, h3] <;> omega
    rw [List.countP_congr (fun w _ => by rw [hor w])]
    rw [countP_or _ _ (fun w => by simp only [decide_eq_true_eq]; omega), ih, hv]
    rw [Nat.succ_mul]

/-- **B1 (exactness), the words:** the accepted words that give `true` number `num * q` and all accepted words number `den * q`, where `q = (2^64 - threshold den) / den`: the share is exactly `num / den`. -/
theorem bernoulli_exact {num : Int} {den : Nat} (h0 : 0 < den) (h1 : 0 ≤ num) (h2 : num ≤ den) :
    (List.range (2 ^ 64)).countP (fun w => decide (threshold den ≤ w ∧ (w % den : Nat) < num.toNat)) =
        num.toNat * ((2 ^ 64 - threshold den) / den) ∧
    (List.range (2 ^ 64)).countP (fun w => decide (threshold den ≤ w)) =
        den * ((2 ^ 64 - threshold den) / den) := by
  refine ⟨count_accepted_lt h0 _ (by omega), ?_⟩
  rw [← count_accepted_lt h0 den (Nat.le_refl _)]
  apply List.countP_congr
  intro w _
  have := Nat.mod_lt w h0
  simp only [decide_eq_true_eq]
  omega

/-- The accepted words are a whole number of copies of `[0, den)`: `den * q = 2^64 - threshold den`. -/
theorem bernoulli_accepted_total {den : Nat} (h0 : 0 < den) :
    den * ((2 ^ 64 - threshold den) / den) = 2 ^ 64 - threshold den := by
  have h := Nat.div_add_mod (2 ^ 64) den
  unfold threshold
  rw [show 2 ^ 64 - 2 ^ 64 % den = den * (2 ^ 64 / den) by omega, Nat.mul_div_cancel_left _ h0]

/-! ### B2: the certain cases -/

/-- **B2:** `num = 0` gives `false`. -/
theorem bernoulli_zero {den : Nat} {st st' : Stream} {b : Bool} (h : bernoulli 0 den st = .ok (b, st')) :
    b = false := by
  have hv := bernoulli_valid h
  obtain ⟨u, _, hb⟩ := (bernoulli_ok_iff hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 st b st').mp h
  rw [hb]; simp

/-- **B2:** `num = den` gives `true`. -/
theorem bernoulli_full {den : Nat} {st st' : Stream} {b : Bool} (h : bernoulli (den : Int) den st = .ok (b, st')) :
    b = true := by
  have hv := bernoulli_valid h
  obtain ⟨u, hu, hb⟩ := (bernoulli_ok_iff hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 st b st').mp h
  have := (uniformBelow_lt hu).1
  rw [hb]; simp only [decide_eq_true_eq]; omega

/-- A valid bound with a small threshold always draws. -/
theorem uniformBelow_ok_of_small {n : Nat} (h0 : 0 < n) (h3 : n ≤ 2 ^ 64) (hth : threshold n < rejectionFuel)
    (st : Stream) : ∃ u st', uniformBelow n st = .ok (u, st') := by
  cases hu : uniformBelow n st with
  | ok r => exact ⟨r.1, r.2, rfl⟩
  | error e =>
    exfalso
    have := (uniformBelowWith_error_iff (fuel := rejectionFuel) h0 h3 st e).mp hu
    obtain ⟨rfl, _⟩ := this
    exact uniformBelowWith_ne_fuelExhausted hth st hu

/-- **B2, for every stream:** with a small threshold `num = 0` always answers `false`. -/
theorem bernoulli_zero_ok {den : Nat} (h0 : 0 < den) (h3 : den ≤ 2 ^ 64) (hth : threshold den < rejectionFuel)
    (st : Stream) : ∃ st', bernoulli 0 den st = .ok (false, st') := by
  obtain ⟨u, s, hu⟩ := uniformBelow_ok_of_small h0 h3 hth st
  refine ⟨s, (bernoulli_ok_iff h0 (by omega) (by omega) h3 st false s).mpr ⟨u, hu, ?_⟩⟩
  simp

/-- **B2, for every stream:** with a small threshold `num = den` always answers `true`. -/
theorem bernoulli_full_ok {den : Nat} (h0 : 0 < den) (h3 : den ≤ 2 ^ 64) (hth : threshold den < rejectionFuel)
    (st : Stream) : ∃ st', bernoulli (den : Int) den st = .ok (true, st') := by
  obtain ⟨u, s, hu⟩ := uniformBelow_ok_of_small h0 h3 hth st
  refine ⟨s, (bernoulli_ok_iff h0 (by omega) (by omega) h3 st true s).mpr ⟨u, hu, ?_⟩⟩
  have := (uniformBelow_lt hu).1
  have h : (u : Int) < (den : Int) := by omega
  simp [h]

/-! ### B3: refusals -/

/-- **B3:** `den = 0`. -/
theorem bernoulli_denZero (num : Int) (st : Stream) : bernoulli num 0 st = .error .probabilityDenominatorZero := by
  simp [bernoulli]

/-- **B3:** `num < 0`. -/
theorem bernoulli_neg {num : Int} (h : num < 0) {den : Nat} (hd : 0 < den) (st : Stream) :
    bernoulli num den st = .error .probabilityOutOfRange := by
  have : den ≠ 0 := by omega
  simp [bernoulli, this, h]

/-- **B3:** `num > den`. -/
theorem bernoulli_big {den : Nat} {num : Int} (h : (den : Int) < num) (hd : 0 < den) (st : Stream) :
    bernoulli num den st = .error .probabilityOutOfRange := by
  have : den ≠ 0 := by omega
  simp [bernoulli, this, h]

/-- **B3:** `den > 2^64` (with `0 ≤ num ≤ den`). -/
theorem bernoulli_tooLarge {den : Nat} {num : Int} (h1 : 0 ≤ num) (h2 : num ≤ den) (h : 2 ^ 64 < den)
    (st : Stream) : bernoulli num den st = .error .boundTooLarge := by
  have e0 : den ≠ 0 := by omega
  have e1 : ¬ (num < 0 ∨ (den : Int) < num) := by omega
  simp [bernoulli, e0, e1, maxBound, h]

/-! ### B4: a function of the stream; advance -/

/-- **B4:** the result is a function of `(num, den, st)`. -/
theorem bernoulli_det {num num' : Int} {den den' : Nat} {st st' : Stream} (hn : num = num') (hd : den = den')
    (hs : st = st') : bernoulli num den st = bernoulli num' den' st' := by subst hn; subst hd; subst hs; rfl

/-- **B4:** on success the stream advanced by `k` words, `1 ≤ k ≤ rejectionFuel`. -/
theorem bernoulli_advance {num : Int} {den : Nat} {st st' : Stream} {b : Bool}
    (h : bernoulli num den st = .ok (b, st')) : ∃ k, 1 ≤ k ∧ k ≤ rejectionFuel ∧ st' = st.advance k.toUInt64 := by
  have hv := bernoulli_valid h
  obtain ⟨u, hu, _⟩ := (bernoulli_ok_iff hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 st b st').mp h
  exact uniformBelowWith_advance hu

/-! ### Non-vacuity witnesses and the vectors -/

/-- The answer of a refused or successful draw as a refusal (for the vectors). -/
def bernErr (r : DrawWith Stream Bool) : Option Refusal :=
  match r with
  | .ok _ => none
  | .error e => some e

/-- `k` draws in a row: the answers as 0 or 1 and the final position. -/
def bdraws : Nat → Int → Nat → Stream → Option (List Nat × UInt64)
  | 0, _, _, st => some ([], st.pos)
  | k + 1, num, den, st =>
    match bernoulli num den st with
    | .ok (b, st') => (bdraws k num den st').map fun r => ((if b then 1 else 0) :: r.1, r.2)
    | .error _ => none

-- B1: the scaled-down analogue for 1/3 (8-bit words, threshold 1, 85 accepted words per residue; 85 give `true`).
example : (List.range 256).countP (fun w => decide (256 % 3 ≤ w ∧ w % 3 < 1)) = 1 * ((256 - 256 % 3) / 3) := by
  decide +kernel
example : (List.range 256).countP (fun w => decide (256 % 3 ≤ w)) = 3 * ((256 - 256 % 3) / 3) := by decide +kernel
-- B1 at full width: 1/3, 0/1, 1/1.
example : (List.range (2 ^ 64)).countP (fun w => decide (threshold 3 ≤ w ∧ (w % 3 : Nat) < (1 : Int).toNat)) =
    (1 : Int).toNat * ((2 ^ 64 - threshold 3) / 3) := (bernoulli_exact (num := 1) (den := 3) (by decide) (by decide) (by decide)).1
example : (List.range (2 ^ 64)).countP (fun w => decide (threshold 1 ≤ w ∧ (w % 1 : Nat) < (0 : Int).toNat)) =
    (0 : Int).toNat * ((2 ^ 64 - threshold 1) / 1) := (bernoulli_exact (num := 0) (den := 1) (by decide) (by decide) (by decide)).1
example : (List.range (2 ^ 64)).countP (fun w => decide (threshold 1 ≤ w)) = 1 * ((2 ^ 64 - threshold 1) / 1) :=
  (bernoulli_exact (num := 1) (den := 1) (by decide) (by decide) (by decide)).2
example : (List.range 3).countP (fun u : Nat => decide ((u : Int) < 1)) = (1 : Int).toNat :=
  bernoulli_count_values (num := 1) (den := 3) (by decide) (by decide)
example : 3 * ((2 ^ 64 - threshold 3) / 3) = 2 ^ 64 - threshold 3 := bernoulli_accepted_total (by decide)

-- B2 witnesses: (0, 1), (1, 1), (3, 3), for every stream.
example (st : Stream) : ∃ st', bernoulli 0 1 st = .ok (false, st') :=
  bernoulli_zero_ok (by decide) (by decide) (by decide) st
example (st : Stream) : ∃ st', bernoulli ((1 : Nat) : Int) 1 st = .ok (true, st') :=
  bernoulli_full_ok (by decide) (by decide) (by decide) st
example (st : Stream) : ∃ st', bernoulli ((3 : Nat) : Int) 3 st = .ok (true, st') :=
  bernoulli_full_ok (by decide) (by decide) (by decide) st
example : bernoulli 0 1 (Stream.ofSeed 1) = .ok (false, (Stream.ofSeed 1).advance 1) := by rfl
example : False ∨ (false = false) := Or.inr (bernoulli_zero (show bernoulli 0 1 (Stream.ofSeed 1) = .ok (false, (Stream.ofSeed 1).advance 1) by rfl))
example : true = true := bernoulli_full (den := 1) (show bernoulli ((1 : Nat) : Int) 1 (Stream.ofSeed 1) = .ok (true, (Stream.ofSeed 1).advance 1) by rfl)

-- B3 witnesses: (1, 0), (-1, 3), (4, 3), (1, 2^64 + 1).
example (st : Stream) : bernoulli 1 0 st = .error .probabilityDenominatorZero := bernoulli_denZero 1 st
example (st : Stream) : bernoulli (-1) 3 st = .error .probabilityOutOfRange := bernoulli_neg (by decide) (by decide) st
example (st : Stream) : bernoulli 4 3 st = .error .probabilityOutOfRange := bernoulli_big (by decide) (by decide) st
example (st : Stream) : bernoulli 1 (2 ^ 64 + 1) st = .error .boundTooLarge :=
  bernoulli_tooLarge (by decide) (by decide) (by decide) st
example : bernErr (bernoulli (-1) 3 (Stream.ofSeed 1)) = some .probabilityOutOfRange := by decide +kernel
example : bernErr (bernoulli 4 3 (Stream.ofSeed 1)) = some .probabilityOutOfRange := by decide +kernel
example : bernErr (bernoulli 1 0 (Stream.ofSeed 1)) = some .probabilityDenominatorZero := by decide +kernel
example : bernErr (bernoulli 1 (2 ^ 64 + 1) (Stream.ofSeed 1)) = some .boundTooLarge := by decide +kernel

-- B4 witness: a concrete success, and the advance it names.
example : ∃ k, 1 ≤ k ∧ k ≤ rejectionFuel ∧ (Stream.ofSeed 1).advance 1 = (Stream.ofSeed 1).advance k.toUInt64 :=
  bernoulli_advance (show bernoulli 0 1 (Stream.ofSeed 1) = .ok (false, (Stream.ofSeed 1).advance 1) by rfl)

-- The bernoulli vectors (eight draws in a row; 1 is `true`; position 8).
example : bdraws 8 1 3 (Stream.ofSeed 1) = some ([0, 1, 1, 0, 0, 0, 0, 1], 8) := by decide +kernel
example : bdraws 8 3 4 (Stream.ofSeed 0) = some ([1, 1, 1, 1, 1, 1, 0, 1], 8) := by decide +kernel
example : bdraws 8 0 1 (Stream.ofSeed 1) = some ([0, 0, 0, 0, 0, 0, 0, 0], 8) := by decide +kernel
example : bdraws 8 1 1 (Stream.ofSeed 1) = some ([1, 1, 1, 1, 1, 1, 1, 1], 8) := by decide +kernel

end VbmRng
