import VbmForecast.Brier
import VbmForecastProofs.Rep
/-! # S2 proofs: the Brier score

Properties 1, 2, 3, 4 (Brier part) and 5 (Brier part) of `docs/spec.md`, section 8, and the vectors V1-V4 as `example`s. Every claim is exact integer arithmetic; each conditional theorem has a non-vacuity witness over small literals. -/
namespace VbmForecast

/-! ## Sums -/

theorem sumInt_append (xs ys : List Int) : sumInt (xs ++ ys) = sumInt xs + sumInt ys := by
  induction xs with
  | nil => simp [sumInt]
  | cons x xs ih => simp only [List.cons_append, sumInt, ih]; omega

theorem sumInt_perm {xs ys : List Int} (h : xs.Perm ys) : sumInt xs = sumInt ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [sumInt, ih]
  | swap x y l => simp only [sumInt]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumInt_nonneg {xs : List Int} (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ sumInt xs := by
  induction xs with
  | nil => simp [sumInt]
  | cons x xs ih =>
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    simp only [sumInt]; omega

/-! ## Property 1: bounded, and zero exactly for a perfect forecast -/

theorem mul_self_nn (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos h h

theorem mul_self_zero {a : Int} (h : a * a = 0) : a = 0 := by
  rcases Int.mul_eq_zero.1 h with h | h <;> exact h

theorem mul_self_le {a b : Int} (h0 : 0 ≤ a) (h1 : a ≤ b) : a * a ≤ b * b :=
  Int.mul_le_mul h1 h1 h0 (Int.le_trans h0 h1)

theorem brierBinary_true (s : Scale) (p : Int) : brierBinary s ⟨p, true⟩ = (p - (s : Int)) * (p - (s : Int)) := rfl

theorem brierBinary_false (s : Scale) (p : Int) : brierBinary s ⟨p, false⟩ = p * p := by
  simp [brierBinary]

theorem brierBinary_nonneg (s : Scale) (e : BinaryEvent) : 0 ≤ brierBinary s e := by
  obtain ⟨p, hit⟩ := e
  cases hit
  · rw [brierBinary_false]; exact mul_self_nn _
  · rw [brierBinary_true]; exact mul_self_nn _

/-- `0 ≤ p ≤ s` gives a score of at most `s^2`. -/
theorem brierBinary_le (s : Scale) (e : BinaryEvent) (h0 : 0 ≤ e.p) (h1 : e.p ≤ (s : Int)) :
    brierBinary s e ≤ (s : Int) * s := by
  obtain ⟨p, hit⟩ := e
  have h0' : 0 ≤ p := h0
  have h1' : p ≤ (s : Int) := h1
  cases hit
  · rw [brierBinary_false]; exact mul_self_le h0' h1'
  · rw [brierBinary_true]
    have hA : 0 ≤ (s : Int) - p := Int.sub_nonneg_of_le h1'
    have hB : (s : Int) - p ≤ s := Int.sub_le_self _ h0'
    have := mul_self_le hA hB
    have e : (p - (s : Int)) * (p - (s : Int)) = ((s : Int) - p) * ((s : Int) - p) := by grind
    rw [e]; exact this

/-- Zero exactly when `p = s` and the event happened, or `p = 0` and it did not. -/
theorem brierBinary_eq_zero_iff (s : Scale) (e : BinaryEvent) :
    brierBinary s e = 0 ↔ (e.p = (s : Int) ∧ e.hit = true) ∨ (e.p = 0 ∧ e.hit = false) := by
  obtain ⟨p, hit⟩ := e
  cases hit
  · rw [brierBinary_false]
    constructor
    · intro h; exact Or.inr ⟨mul_self_zero h, rfl⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · cases h
      · have h' : p = 0 := h
        rw [h']; rfl
  · rw [brierBinary_true]
    constructor
    · intro h; exact Or.inl ⟨Int.sub_eq_zero.1 (mul_self_zero h), rfl⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · have h' : p = (s : Int) := h
        rw [h']; simp
      · cases h

theorem brierCatFrom_nonneg (s : Scale) (o : Nat) (ps : List Int) : ∀ j, 0 ≤ brierCatFrom s o j ps := by
  induction ps with
  | nil => intro j; simp [brierCatFrom]
  | cons p ps ih =>
    intro j
    have := ih (j + 1)
    simp only [brierCatFrom]
    have := mul_self_nn (p - (if j = o then (s : Int) else 0))
    omega

theorem brierCategorical_nonneg (s : Scale) (ps : List Int) (o : Nat) : 0 ≤ brierCategorical s ps o :=
  brierCatFrom_nonneg s o ps 0

/-- The bound `T^2 + s^2` on the sum from position `j`, with a sharper `T^2` when the outcome is outside the list. -/
theorem brierCatFrom_le (s : Scale) (o : Nat) (ps : List Int) (hp : ∀ p ∈ ps, 0 ≤ p) :
    ∀ j, brierCatFrom s o j ps ≤ sumInt ps * sumInt ps + (if j ≤ o ∧ o < j + ps.length then (s : Int) * s else 0) := by
  induction ps with
  | nil =>
    intro j
    simp only [brierCatFrom, sumInt, List.length_nil, Int.zero_mul, Nat.add_zero]
    split
    · have := Int.mul_nonneg (Int.natCast_nonneg s) (Int.natCast_nonneg s); omega
    · omega
  | cons p ps ih =>
    intro j
    have hp0 := hp p (by simp)
    have hT := sumInt_nonneg (fun y hy => hp y (by simp [hy]) : ∀ x ∈ ps, 0 ≤ x)
    have ih' := ih (fun y hy => hp y (by simp [hy])) (j + 1)
    have hs : (0 : Int) ≤ s := Int.natCast_nonneg s
    have hps : 0 ≤ p * sumInt ps := Int.mul_nonneg hp0 hT
    have hpS : 0 ≤ p * (s : Int) := Int.mul_nonneg hp0 hs
    simp only [brierCatFrom, sumInt, List.length_cons] at *
    by_cases hj : j = o
    · subst hj
      have e1 : ¬ (j + 1 ≤ j ∧ j < j + 1 + ps.length) := by omega
      have e2 : (j ≤ j ∧ j < j + (ps.length + 1)) := by omega
      simp only [e1, e2, and_self, ite_true, ite_false] at *
      grind
    · have e1 : (j + 1 ≤ o ∧ o < j + 1 + ps.length) ↔ (j ≤ o ∧ o < j + (ps.length + 1)) := by omega
      simp only [hj, ite_false, e1] at *
      grind

/-- A valid normalised categorical forecast scores at most `2 * s^2`. -/
theorem brierCategorical_le (s : Scale) (ps : List Int) (o : Nat) (hr : ∀ p ∈ ps, 0 ≤ p ∧ p ≤ (s : Int))
    (hn : sumInt ps = (s : Int)) : brierCategorical s ps o ≤ 2 * ((s : Int) * s) := by
  have := brierCatFrom_le s o ps (fun p hp => (hr p hp).1) 0
  rw [hn] at this
  unfold brierCategorical
  have hs : (0 : Int) ≤ (s : Int) * s := Int.mul_nonneg (Int.natCast_nonneg s) (Int.natCast_nonneg s)
  split at this <;> omega

/-- Zero exactly when the forecast is one-hot at the outcome (position `j + i` carries `s` iff it is the outcome). -/
theorem brierCatFrom_eq_zero_iff (s : Scale) (o : Nat) (ps : List Int) :
    ∀ j, brierCatFrom s o j ps = 0 ↔ ∀ i (h : i < ps.length), ps[i] = if j + i = o then (s : Int) else 0 := by
  induction ps with
  | nil => intro j; simp [brierCatFrom]
  | cons p ps ih =>
    intro j
    have h1 := brierCatFrom_nonneg s o ps (j + 1)
    have hn := mul_self_nn (p - (if j = o then (s : Int) else 0))
    simp only [brierCatFrom]
    constructor
    · intro h
      have hz : (p - (if j = o then (s : Int) else 0)) * (p - (if j = o then (s : Int) else 0)) = 0 := by omega
      have hr : brierCatFrom s o (j + 1) ps = 0 := by omega
      have hp : p = if j = o then (s : Int) else 0 := by have := mul_self_zero hz; omega
      intro i hi
      cases i with
      | zero => simpa using hp
      | succ i =>
        have := (ih (j + 1)).1 hr i (by simpa using hi)
        simpa [show j + (i + 1) = j + 1 + i by omega] using this
    · intro h
      have hp : p = if j = o then (s : Int) else 0 := by exact h 0 (by simp)
      have hr : brierCatFrom s o (j + 1) ps = 0 := by
        rw [ih (j + 1)]
        intro i hi
        have := h (i + 1) (by simpa using hi)
        simpa [show j + (i + 1) = j + 1 + i by omega] using this
      rw [hr, hp]; simp

theorem brierCategorical_eq_zero_iff (s : Scale) (ps : List Int) (o : Nat) :
    brierCategorical s ps o = 0 ↔ ∀ i (h : i < ps.length), ps[i] = if i = o then (s : Int) else 0 := by
  unfold brierCategorical
  rw [brierCatFrom_eq_zero_iff]; simp

-- Witnesses (`s = 10`): a perfect forecast scores 0, `p = 7` hit scores 9, `p = 0` hit attains the bound `s^2 = 100`.
example : brierBinary 10 ⟨10, true⟩ = 0 := by decide
example : brierBinary 10 ⟨0, false⟩ = 0 := by decide
example : brierBinary 10 ⟨7, true⟩ = 9 := by decide
example : brierBinary 10 ⟨0, true⟩ = 100 := by decide
example : brierCategorical 10 [0, 10, 0] 1 = 0 := by decide
example : brierCategorical 10 [0, 0, 10] 0 = 200 := by decide
example : sumInt [0, 0, 10] = (10 : Nat) ∧ ∀ p ∈ [0, 0, (10 : Int)], 0 ≤ p ∧ p ≤ ((10 : Nat) : Int) := by decide +kernel

/-! ## Property 2: strict propriety, binary -/

theorem expBrierBinary_diff (s : Scale) (q p : Int) :
    expBrierBinary s q p - expBrierBinary s q q = (s : Int) * ((p - q) * (p - q)) := by
  unfold expBrierBinary brierBinary; simp only [ite_true, Bool.false_eq_true, ite_false]; grind

theorem expBrierBinary_ge (s : Scale) (q p : Int) : expBrierBinary s q q ≤ expBrierBinary s q p := by
  have h := expBrierBinary_diff s q p
  have : 0 ≤ (s : Int) * ((p - q) * (p - q)) := Int.mul_nonneg (Int.natCast_nonneg s) (mul_self_nn _)
  omega

/-- Equality holds only for the true probability (`s > 0`). -/
theorem expBrierBinary_eq_iff (s : Scale) (hs : 0 < s) (q p : Int) :
    expBrierBinary s q p = expBrierBinary s q q ↔ p = q := by
  have h := expBrierBinary_diff s q p
  have hs' : (0 : Int) < s := Int.natCast_pos.2 hs
  constructor
  · intro he
    have h0 : (s : Int) * ((p - q) * (p - q)) = 0 := by omega
    rcases Int.mul_eq_zero.1 h0 with h | h
    · omega
    · have := mul_self_zero h; omega
  · intro he; subst he; omega

-- Witness: `s = 10`, `q = 7`, `p = 5`: `E = 250`, `E(q; q) = 210`, difference `40 = 10 * 4`.
example : expBrierBinary 10 7 5 = 250 := by decide
example : expBrierBinary 10 7 7 = 210 := by decide
example : expBrierBinary 10 7 5 - expBrierBinary 10 7 7 = 10 * ((5 - 7) * (5 - 7)) := by decide
example : expBrierBinary 10 7 5 ≠ expBrierBinary 10 7 7 := by decide

/-! ## Property 3: categorical propriety -/

/-- The sum of squares. -/
def brSq : List Int → Int
  | [] => 0
  | p :: ps => p * p + brSq ps

/-- The pairwise product sum. -/
def brDot : List Int → List Int → Int
  | p :: ps, q :: qs => p * q + brDot ps qs
  | _, _ => 0

/-- `Σ_{i ≥ 0} q_i * p_{o+i}`, the cross term of the expectation. -/
def brCross (ps : List Int) : Nat → List Int → Int
  | _, [] => 0
  | o, q :: qs => q * ps.getD o 0 + brCross ps (o + 1) qs

theorem brierCatFrom_closed (s : Scale) (o : Nat) (ps : List Int) :
    ∀ j, brierCatFrom s o j ps =
      brSq ps + (if j ≤ o ∧ o < j + ps.length then (s : Int) * s - 2 * s * ps.getD (o - j) 0 else 0) := by
  induction ps with
  | nil =>
    intro j
    simp only [brierCatFrom, brSq, List.length_nil, Nat.add_zero]
    split
    · omega
    · rfl
  | cons p ps ih =>
    intro j
    simp only [brierCatFrom, brSq, ih (j + 1), List.length_cons]
    by_cases hj : j = o
    · subst hj
      have e1 : ¬ (j + 1 ≤ j ∧ j < j + 1 + ps.length) := by omega
      have e2 : (j ≤ j ∧ j < j + (ps.length + 1)) := by omega
      simp only [e1, e2, and_self, ite_true, ite_false, Nat.sub_self, List.getD_cons_zero]
      grind
    · have e1 : (j + 1 ≤ o ∧ o < j + 1 + ps.length) ↔ (j ≤ o ∧ o < j + (ps.length + 1)) := by omega
      simp only [hj, ite_false, e1]
      by_cases hc : j ≤ o ∧ o < j + (ps.length + 1)
      · have : o - j = (o - (j + 1)) + 1 := by omega
        simp only [hc, and_self, ite_true, this, List.getD_cons_succ]
        grind
      · simp only [hc, ite_false]; grind

theorem brierCategorical_closed (s : Scale) (ps : List Int) (o : Nat) (h : o < ps.length) :
    brierCategorical s ps o = brSq ps + (s : Int) * s - 2 * s * ps.getD o 0 := by
  unfold brierCategorical
  rw [brierCatFrom_closed]
  have : 0 ≤ o ∧ o < 0 + ps.length := by omega
  simp only [this, and_self, ite_true, Nat.sub_zero]; omega

theorem expCatFrom_closed (s : Scale) (ps : List Int) (qs : List Int) :
    ∀ o, o + qs.length ≤ ps.length →
      expCatFrom s ps o qs = sumInt qs * (brSq ps + (s : Int) * s) - 2 * s * brCross ps o qs := by
  induction qs with
  | nil => intro o _; simp [expCatFrom, sumInt, brCross]
  | cons q qs ih =>
    intro o ho
    simp only [List.length_cons] at ho
    have := ih (o + 1) (by omega)
    simp only [expCatFrom, sumInt, brCross, brierCategorical_closed s ps o (by omega), this]
    grind

theorem brCross_eq (ps qs : List Int) : ∀ o, brCross ps o qs = brDot qs (ps.drop o) := by
  induction qs with
  | nil => intro o; simp [brCross, brDot]
  | cons q qs ih =>
    intro o
    simp only [brCross, ih (o + 1)]
    by_cases ho : o < ps.length
    · rw [List.drop_eq_getElem_cons ho]
      simp only [brDot, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho, Option.getD_some]
      rw [List.drop_eq_getElem_cons ho] at *
    · have h1 : ps.drop o = [] := List.drop_of_length_le (by omega)
      have h2 : ps.drop (o + 1) = [] := List.drop_of_length_le (by omega)
      simp [h1, h2, brDot, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ps.length ≤ o)]

theorem brDot_comm (ps qs : List Int) : brDot ps qs = brDot qs ps := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp [brDot]
  | cons p ps ih => cases qs with
    | nil => simp [brDot]
    | cons q qs => simp only [brDot, ih]; grind

theorem brDot_self (qs : List Int) : brDot qs qs = brSq qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [brDot, brSq, ih]

theorem sqDist_closed (ps qs : List Int) (h : ps.length = qs.length) :
    sqDist ps qs = brSq ps - 2 * brDot qs ps + brSq qs := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp_all [sqDist, brSq, brDot]
  | cons p ps ih =>
    cases qs with
    | nil => simp at h
    | cons q qs =>
      have := ih qs (by simpa using h)
      simp only [sqDist, brSq, brDot, this]; grind

/-- The expectation is `T * (Σ p^2 + s^2) - 2 s Σ q_i p_i` for `T = Σ q`. -/
theorem expBrierCat_closed (s : Scale) (qs ps : List Int) (h : qs.length ≤ ps.length) :
    expBrierCat s qs ps = sumInt qs * (brSq ps + (s : Int) * s) - 2 * s * brDot qs ps := by
  unfold expBrierCat
  rw [expCatFrom_closed s ps qs 0 (by omega), brCross_eq]; simp

/-- Categorical propriety: `E(p; q) - E(q; q) = s * Σ_j (p_j - q_j)^2` when `Σ q = s` and the lists are aligned. -/
theorem expBrierCat_diff (s : Scale) (qs ps : List Int) (hl : ps.length = qs.length) (hq : sumInt qs = (s : Int)) :
    expBrierCat s qs ps - expBrierCat s qs qs = (s : Int) * sqDist ps qs := by
  rw [expBrierCat_closed s qs ps (by omega), expBrierCat_closed s qs qs (by omega), sqDist_closed ps qs hl, brDot_self, hq]
  grind

theorem sqDist_nonneg (ps qs : List Int) : 0 ≤ sqDist ps qs := by
  induction ps generalizing qs with
  | nil => simp [sqDist]
  | cons p ps ih => cases qs with
    | nil => simp [sqDist]
    | cons q qs => have := ih qs; have := mul_self_nn (p - q); simp only [sqDist]; omega

theorem expBrierCat_ge (s : Scale) (qs ps : List Int) (hl : ps.length = qs.length) (hq : sumInt qs = (s : Int)) :
    expBrierCat s qs qs ≤ expBrierCat s qs ps := by
  have h := expBrierCat_diff s qs ps hl hq
  have := Int.mul_nonneg (Int.natCast_nonneg s) (sqDist_nonneg ps qs)
  omega

theorem sqDist_refl (ps : List Int) : sqDist ps ps = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sqDist, ih]

theorem sqDist_eq_zero_iff (ps qs : List Int) (hl : ps.length = qs.length) : sqDist ps qs = 0 ↔ ps = qs := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp_all [sqDist]
  | cons p ps ih => cases qs with
    | nil => simp at hl
    | cons q qs =>
      have h1 := sqDist_nonneg ps qs
      have h2 := mul_self_nn (p - q)
      have := ih qs (by simpa using hl)
      simp only [sqDist, List.cons.injEq]
      constructor
      · intro h
        have hz : (p - q) * (p - q) = 0 := by omega
        have : p = q := by have := mul_self_zero hz; omega
        exact ⟨this, (ih qs (by simpa using hl)).1 (by omega)⟩
      · rintro ⟨h1, h3⟩; subst h1; subst h3; simp [sqDist_refl]

/-- Strict: equality of the expectations holds only for the true distribution (`s > 0`). -/
theorem expBrierCat_eq_iff (s : Scale) (hs : 0 < s) (qs ps : List Int) (hl : ps.length = qs.length)
    (hq : sumInt qs = (s : Int)) : expBrierCat s qs ps = expBrierCat s qs qs ↔ ps = qs := by
  have h := expBrierCat_diff s qs ps hl hq
  have hs' : (0 : Int) < s := Int.natCast_pos.2 hs
  rw [← sqDist_eq_zero_iff ps qs hl]
  constructor
  · intro he
    have h0 : (s : Int) * sqDist ps qs = 0 := by omega
    rcases Int.mul_eq_zero.1 h0 with h | h <;> omega
  · intro he; rw [he] at h; omega

-- Witness: `s = 10`, `k = 3`, `q = (5, 3, 2)`, `p = (4, 4, 2)`: `E(p) - E(q) = 640 - 620 = 20 = 10 * 2`.
example : sumInt [5, 3, 2] = ((10 : Nat) : Int) := by decide
example : expBrierCat 10 [5, 3, 2] [4, 4, 2] = 640 := by decide
example : expBrierCat 10 [5, 3, 2] [5, 3, 2] = 620 := by decide
example : expBrierCat 10 [5, 3, 2] [4, 4, 2] - expBrierCat 10 [5, 3, 2] [5, 3, 2] = 10 * sqDist [4, 4, 2] [5, 3, 2] := by decide
example : expBrierCat 10 [5, 3, 2] [4, 4, 2] ≠ expBrierCat 10 [5, 3, 2] [5, 3, 2] := by decide

/-! ## Property 4 (Brier part): additive over events -/

theorem brierTotal_append (s : Scale) (xs ys : List BinaryEvent) :
    brierTotal s (xs ++ ys) = brierTotal s xs + brierTotal s ys := by
  unfold brierTotal; rw [List.map_append, sumInt_append]

theorem brierCatTotal_append (s : Scale) (xs ys : List CategoricalEvent) :
    brierCatTotal s (xs ++ ys) = brierCatTotal s xs + brierCatTotal s ys := by
  unfold brierCatTotal; rw [List.map_append, sumInt_append]

/-- A cons adds the score of its head. -/
theorem brierTotal_cons (s : Scale) (e : BinaryEvent) (es : List BinaryEvent) :
    brierTotal s (e :: es) = brierBinary s e + brierTotal s es := rfl

/-- The mean is the unreduced ratio `total / (n * s^2)`. -/
theorem brierMean_ok (s : Scale) (es : List BinaryEvent) (hs : 0 < s) (hn : 0 < es.length) :
    ∃ r, brierMean s es = .ok r ∧ r.num = brierTotal s es ∧ r.den = es.length * (s * s) := by
  unfold brierMean; simp only [hs, hn, dite_true]; exact ⟨_, rfl, rfl, rfl⟩

theorem brierMean_badScale (es : List BinaryEvent) : brierMean 0 es = .error .badScale := rfl

theorem brierMean_empty (s : Scale) (hs : 0 < s) : brierMean s [] = .error .empty := by
  unfold brierMean; simp only [hs, dite_true]; rfl

-- Witness: two literal samples at `s = 10`: totals `9 + 49 = 58` and `0 + 100 = 100`, joined `158`.
example : brierTotal 10 [⟨7, true⟩, ⟨7, false⟩] = 58 := by decide
example : brierTotal 10 [⟨10, true⟩, ⟨0, true⟩] = 100 := by decide
example : brierTotal 10 [⟨7, true⟩, ⟨7, false⟩, ⟨10, true⟩, ⟨0, true⟩] = 58 + 100 := by decide
example : brierCatTotal 10 [⟨[5, 3, 2], 0⟩, ⟨[5, 3, 2], 1⟩] = 38 + 78 := by decide
example : brierMean 10 [⟨7, true⟩, ⟨7, false⟩] = .ok ⟨58, 200, by decide⟩ := rfl

/-! ## Property 5 (Brier part): permutation invariance -/

theorem brierTotal_perm (s : Scale) {xs ys : List BinaryEvent} (h : xs.Perm ys) : brierTotal s xs = brierTotal s ys := by
  unfold brierTotal; exact sumInt_perm (h.map _)

theorem brierCatTotal_perm (s : Scale) {xs ys : List CategoricalEvent} (h : xs.Perm ys) :
    brierCatTotal s xs = brierCatTotal s ys := by
  unfold brierCatTotal; exact sumInt_perm (h.map _)

-- Witness: `[a, b, c] ~ [c, a, b]` with distinct scores `9, 49, 0`.
example : [BinaryEvent.mk 7 true, ⟨7, false⟩, ⟨10, true⟩].Perm [⟨10, true⟩, ⟨7, true⟩, ⟨7, false⟩] :=
  (List.Perm.cons _ (List.Perm.swap _ _ [])).trans (List.Perm.swap _ _ _)
example : brierTotal 10 [⟨7, true⟩, ⟨7, false⟩, ⟨10, true⟩] = brierTotal 10 [⟨10, true⟩, ⟨7, true⟩, ⟨7, false⟩] := by decide
example : brierBinary 10 ⟨7, true⟩ ≠ brierBinary 10 ⟨7, false⟩ ∧ brierBinary 10 ⟨10, true⟩ ≠ brierBinary 10 ⟨7, true⟩ := by decide

/-! ## The validated entry points -/

theorem brierBinaryV_ok (s : Scale) (e : BinaryEvent) (v : Int) :
    brierBinaryV s e = .ok v ↔ (0 < s ∧ 0 ≤ e.p ∧ e.p ≤ (s : Int)) ∧ v = brierBinary s e := by
  unfold brierBinaryV
  rw [bind_ok_iff, validateBinary_ok]
  simp only [pure, Except.pure, Except.ok.injEq]
  grind

theorem brierCategoricalV_ok (s : Scale) (lim : Limits) (e : CategoricalEvent) (v : Int) :
    brierCategoricalV s lim e = .ok v ↔ validateCategorical s lim e = .ok () ∧ v = brierCategorical s e.ps e.outcome := by
  unfold brierCategoricalV
  rw [bind_ok_iff]
  simp only [pure, Except.pure, Except.ok.injEq]
  grind

-- Witnesses: valid inputs score; each refusal is returned, never a number.
example : brierBinaryV 10 ⟨7, true⟩ = .ok 9 := rfl
example : brierBinaryV 0 ⟨7, true⟩ = .error .badScale := rfl
example : brierBinaryV 10 ⟨11, true⟩ = .error (.probOutOfRange 0 11) := rfl
example : brierCategoricalV 10 witLim ⟨[5, 3, 2], 0⟩ = .ok 38 := rfl
example : brierCategoricalV 10 witLim ⟨[5, 3, 2], 3⟩ = .error (.outcomeNotInSupport 3 3) := rfl
example : brierCategoricalV 10 witLim ⟨[5, 3, 3], 0⟩ = .error (.notNormalised 11) := rfl

/-! ## Vectors V1-V4 -/

example : brierBinary 10 ⟨7, true⟩ = 9 := by decide                                    -- V1
example : brierBinary 10 ⟨7, false⟩ = 49 := by decide                                   -- V2
example : brierCategorical 10 [5, 3, 2] 0 = 25 + 9 + 4 := by decide                     -- V3
example : brierCategorical 10 [5, 3, 2] 0 = 38 := by decide                             -- V3
example : expBrierBinary 10 7 5 = 7 * 25 + 3 * 25 := by decide                          -- V4
example : expBrierBinary 10 7 7 = 7 * 9 + 3 * 49 := by decide                           -- V4
example : expBrierBinary 10 7 5 - expBrierBinary 10 7 7 = 40 := by decide               -- V4
example : (40 : Int) = 10 * ((5 - 7) * (5 - 7)) := by decide                            -- V4

end VbmForecast
