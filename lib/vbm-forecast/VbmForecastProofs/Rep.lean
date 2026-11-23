import VbmForecast.Rep
/-! # S1 proofs: property 17 (validation is total and sound) and the `Ratio` order

For each validator: it returns `ok` exactly when its stated condition holds (soundness and completeness), and for each violated condition it returns the named refusal. Each has an `example` witness that the hypothesis can hold. -/
namespace VbmForecast

/-! ## `Ratio` is a total preorder, `eqv` an equivalence -/

theorem Ratio.le_refl (a : Ratio) : a.le a := Int.le_refl _

theorem Ratio.le_total (a b : Ratio) : a.le b ∨ b.le a := by
  unfold Ratio.le
  rcases Int.le_total (a.num * (b.den : Int)) (b.num * (a.den : Int)) with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [Int.mul_comm b.num, Int.mul_comm (a.den : Int)] at h <;> omega)

theorem Ratio.le_trans {a b c : Ratio} (h1 : a.le b) (h2 : b.le c) : a.le c := by
  unfold Ratio.le at *
  have hb : (0 : Int) < (b.den : Int) := by have := b.den_pos; omega
  have e1 := Int.mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg c.den)
  have e2 := Int.mul_le_mul_of_nonneg_right h2 (Int.natCast_nonneg a.den)
  have : (a.num * (c.den : Int)) * (b.den : Int) ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    calc (a.num * (c.den : Int)) * (b.den : Int) = (a.num * (b.den : Int)) * (c.den : Int) := by
          rw [Int.mul_assoc, Int.mul_comm (c.den : Int), ← Int.mul_assoc]
      _ ≤ (b.num * (a.den : Int)) * (c.den : Int) := e1
      _ = (b.num * (c.den : Int)) * (a.den : Int) := by
          rw [Int.mul_assoc, Int.mul_comm (a.den : Int), ← Int.mul_assoc]
      _ ≤ (c.num * (b.den : Int)) * (a.den : Int) := e2
      _ = (c.num * (a.den : Int)) * (b.den : Int) := by
          rw [Int.mul_assoc, Int.mul_comm (b.den : Int), ← Int.mul_assoc]
  exact Int.le_of_mul_le_mul_right this hb

theorem Ratio.eqv_refl (a : Ratio) : a.eqv a := rfl

theorem Ratio.eqv_symm {a b : Ratio} (h : a.eqv b) : b.eqv a := h.symm

theorem Ratio.eqv_iff_le (a b : Ratio) : a.eqv b ↔ a.le b ∧ b.le a := by
  unfold Ratio.eqv Ratio.le
  constructor
  · intro h; exact ⟨Int.le_of_eq h, by rw [Int.mul_comm b.num, Int.mul_comm (a.den : Int)] at h; exact Int.le_of_eq h.symm⟩
  · intro ⟨h1, h2⟩
    have : b.num * (a.den : Int) ≤ a.num * (b.den : Int) := by
      rw [Int.mul_comm b.num, Int.mul_comm (a.den : Int)] at *; omega
    omega

theorem Ratio.eqv_trans {a b c : Ratio} (h1 : a.eqv b) (h2 : b.eqv c) : a.eqv c :=
  (Ratio.eqv_iff_le a c).2
    ⟨Ratio.le_trans ((Ratio.eqv_iff_le a b).1 h1).1 ((Ratio.eqv_iff_le b c).1 h2).1,
     Ratio.le_trans ((Ratio.eqv_iff_le b c).1 h2).2 ((Ratio.eqv_iff_le a b).1 h1).2⟩

/-- The sum is commutative up to `eqv`. -/
theorem Ratio.add_comm_eqv (a b : Ratio) : (a.add b).eqv (b.add a) := by
  unfold Ratio.eqv Ratio.add
  simp only [Int.natCast_mul]
  rw [Int.add_comm (a.num * _), Int.mul_comm (b.den : Int) (a.den : Int)]

-- Non-vacuity witnesses: `1/2 ≤ 2/3`, `1/2 ~ 2/4`, `1/2 + 1/3 ~ 5/6`.
example : Ratio.le ⟨1, 2, by decide⟩ ⟨2, 3, by decide⟩ := by decide
example : ¬ Ratio.le ⟨2, 3, by decide⟩ ⟨1, 2, by decide⟩ := by decide
example : Ratio.eqv ⟨1, 2, by decide⟩ ⟨2, 4, by decide⟩ := by decide
example : Ratio.eqv (Ratio.add ⟨1, 2, by decide⟩ ⟨1, 3, by decide⟩) ⟨5, 6, by decide⟩ := by decide

/-! ## Bind lemmas for the validators -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]


theorem bind_ok_iff {α : Type} (a : Except Refusal Unit) (b : Except Refusal α) (v : α) :
    (a >>= fun _ => b) = .ok v ↔ a = .ok () ∧ b = .ok v := by
  cases a with
  | error e => simp [bind, Except.bind]
  | ok u => cases u; simp [bind, Except.bind]

theorem bind_err_left (a : Except Refusal Unit) (b : Except Refusal Unit) (r : Refusal)
    (h : a = .error r) : (a >>= fun _ => b) = .error r := by
  subst h; rfl

theorem bind_ok_right (a : Except Refusal Unit) (b : Except Refusal Unit)
    (h : a = .ok ()) : (a >>= fun _ => b) = b := by
  subst h; rfl

/-! ## The primitive checks -/

theorem checkScale_ok (s : Scale) : checkScale s = .ok () ↔ 0 < s := by
  unfold checkScale
  by_cases h : s = 0
  · simp [h]
  · simp [h, Nat.pos_of_ne_zero h]

/-- `badScale` for `s = 0`. -/
theorem checkScale_badScale : checkScale 0 = .error .badScale := rfl

theorem checkProbsFrom_ok (s : Scale) (ps : List Int) : ∀ i, checkProbsFrom s i ps = .ok () ↔ ∀ p ∈ ps, 0 ≤ p ∧ p ≤ (s : Int) := by
  induction ps with
  | nil => intro i; simp [checkProbsFrom]
  | cons p ps ih =>
    intro i
    unfold checkProbsFrom
    by_cases h : p < 0 ∨ (s : Int) < p
    · simp only [h, ite_true]
      constructor
      · intro h'; cases h'
      · intro h'; have := h' p (by simp); omega
    · simp only [h, ite_false]
      rw [ih]
      have h' : 0 ≤ p ∧ p ≤ (s : Int) := by omega
      simp [h']

theorem checkProbs_ok (s : Scale) (ps : List Int) : checkProbs s ps = .ok () ↔ ∀ p ∈ ps, 0 ≤ p ∧ p ≤ (s : Int) :=
  checkProbsFrom_ok s ps 0

/-- `probOutOfRange` carries the position and the value of the FIRST offending probability. -/
theorem checkProbsFrom_refuses (s : Scale) (pre rest : List Int) (p : Int) (i : Nat)
    (hpre : ∀ q ∈ pre, 0 ≤ q ∧ q ≤ (s : Int)) (hp : p < 0 ∨ (s : Int) < p) :
    checkProbsFrom s i (pre ++ p :: rest) = .error (.probOutOfRange (i + pre.length) p) := by
  induction pre generalizing i with
  | nil => simp [checkProbsFrom, hp]
  | cons q pre ih =>
    have hq := hpre q (by simp)
    have : ¬ (q < 0 ∨ (s : Int) < q) := by omega
    simp only [List.cons_append, checkProbsFrom, this, ite_false, List.length_cons]
    have := ih (i + 1) (fun x hx => hpre x (by simp [hx]))
    rw [this]; congr 2; omega

theorem checkNormalised_ok (s : Scale) (tol : Nat) (ps : List Int) :
    checkNormalised s tol ps = .ok () ↔ (sumInt ps - (s : Int)).natAbs ≤ tol := by
  unfold checkNormalised; split <;> simp_all

/-- `notNormalised` carries the sum. -/
theorem checkNormalised_refuses (s : Scale) (tol : Nat) (ps : List Int) (h : tol < (sumInt ps - (s : Int)).natAbs) :
    checkNormalised s tol ps = .error (.notNormalised (sumInt ps)) := by
  unfold checkNormalised; rw [ite_f (by omega)]

theorem checkOutcome_ok (outcome k : Nat) : checkOutcome outcome k = .ok () ↔ outcome < k := by
  unfold checkOutcome; split <;> simp_all

/-- `outcomeNotInSupport`. -/
theorem checkOutcome_refuses (outcome k : Nat) (h : k ≤ outcome) :
    checkOutcome outcome k = .error (.outcomeNotInSupport outcome k) := by
  unfold checkOutcome; rw [ite_f (by omega)]

theorem checkOutcomeCount_ok (lim : Limits) (k : Nat) :
    checkOutcomeCount lim k = .ok () ↔ 2 ≤ k ∧ k ≤ lim.maxOutcomes := by
  unfold checkOutcomeCount
  by_cases h0 : k = 0
  · simp [h0]
  by_cases h1 : k < 2
  · simp [h0, h1]; omega
  by_cases h2 : lim.maxOutcomes < k
  · simp [h0, h1, h2]
  · simp [h0, h1, h2]; omega

/-- `empty` for no outcomes. -/
theorem checkOutcomeCount_empty (lim : Limits) : checkOutcomeCount lim 0 = .error .empty := by
  unfold checkOutcomeCount; simp

/-- `tooFewOutcomes` for exactly one outcome. -/
theorem checkOutcomeCount_tooFew (lim : Limits) : checkOutcomeCount lim 1 = .error (.tooFewOutcomes 1) := by
  unfold checkOutcomeCount; simp

/-- `tooMany` for a width over the limit. -/
theorem checkOutcomeCount_tooMany (lim : Limits) (k : Nat) (h2 : 2 ≤ k) (h : lim.maxOutcomes < k) :
    checkOutcomeCount lim k = .error (.tooMany limitOutcomes k lim.maxOutcomes) := by
  unfold checkOutcomeCount
  rw [ite_f (by omega), ite_f (by omega), ite_t h]

theorem checkAligned_ok (a b : Nat) : checkAligned a b = .ok () ↔ a = b := by
  unfold checkAligned; split <;> simp_all

/-- `lengthMismatch`. -/
theorem checkAligned_refuses (a b : Nat) (h : a ≠ b) : checkAligned a b = .error (.lengthMismatch a b) := by
  unfold checkAligned; rw [ite_f h]

theorem incFromB_iff {prev : Int} {xs : List Int} : incFromB prev xs = true ↔ IncFrom prev xs := by
  induction xs generalizing prev with
  | nil => simp [incFromB, IncFrom]
  | cons x xs ih => simp [incFromB, IncFrom, ih]

theorem strictIncB_iff {xs : List Int} : strictIncB xs = true ↔ StrictInc xs := by
  cases xs with
  | nil => simp [strictIncB, StrictInc]
  | cons x xs => simp [strictIncB, StrictInc, incFromB_iff]

theorem checkIncreasing_ok (vals : List Int) : checkIncreasing vals = .ok () ↔ StrictInc vals := by
  unfold checkIncreasing
  rw [← strictIncB_iff]
  split <;> simp_all

/-- `supportNotIncreasing`. -/
theorem checkIncreasing_refuses (vals : List Int) (h : ¬ StrictInc vals) :
    checkIncreasing vals = .error .supportNotIncreasing := by
  unfold checkIncreasing
  rw [ite_f (fun hb => h (strictIncB_iff.1 hb))]

theorem checkLevel_ok (s level : Nat) : checkLevel s level = .ok () ↔ 0 < level ∧ level < s := by
  unfold checkLevel; split <;> simp_all

/-- `badLevel` for a quantile level. -/
theorem checkLevel_refuses (s level : Nat) (h : ¬ (0 < level ∧ level < s)) :
    checkLevel s level = .error (.badLevel level s) := by
  unfold checkLevel; rw [ite_f h]

theorem checkTail_ok (s tail : Nat) : checkTail s tail = .ok () ↔ 0 < tail ∧ 2 * tail < s := by
  unfold checkTail; split <;> simp_all

/-- `badLevel` for an interval tail. -/
theorem checkTail_refuses (s tail : Nat) (h : ¬ (0 < tail ∧ 2 * tail < s)) :
    checkTail s tail = .error (.badLevel tail s) := by
  unfold checkTail; rw [ite_f h]

theorem checkInterval_ok (lo hi : Int) : checkInterval lo hi = .ok () ↔ lo ≤ hi := by
  unfold checkInterval; split <;> simp_all <;> omega

/-- `crossedInterval`. -/
theorem checkInterval_refuses (lo hi : Int) (h : hi < lo) : checkInterval lo hi = .error (.crossedInterval lo hi) := by
  unfold checkInterval; rw [ite_t h]

theorem checkEdges_ok (lim : Limits) (s : Scale) (edges : List Nat) :
    checkEdges lim s edges = .ok () ↔
      ∃ e rest, edges = e :: rest ∧ e = 0 ∧ rest ≠ [] ∧ incFromB e rest = true ∧
        (e :: rest).getLast? = some s ∧ rest.length ≤ lim.maxBins := by
  cases edges with
  | nil => simp [checkEdges]
  | cons e rest =>
    dsimp only [checkEdges]
    by_cases h : e = 0 ∧ rest ≠ [] ∧ incFromB e rest = true ∧ (e :: rest).getLast? = some s
    · rw [ite_t h]
      by_cases hb : lim.maxBins < rest.length
      · rw [ite_t hb]
        simp only [reduceCtorEq, false_iff, not_exists]
        intro e' rest' hh
        have := hh.2.2.2.2.2
        have hr : (e :: rest).length = (e' :: rest').length := by rw [hh.1]
        simp at hr this
        omega
      · rw [ite_f hb]
        simp only [true_iff]
        exact ⟨e, rest, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2, by omega⟩
    · rw [ite_f h]
      simp only [reduceCtorEq, false_iff, not_exists]
      intro e' rest' hh
      obtain ⟨hh, h1, h2, h3, h4, _⟩ := hh
      obtain ⟨rfl, rfl⟩ : e = e' ∧ rest = rest' := by simpa using hh
      exact h ⟨h1, h2, h3, h4⟩

/-- `empty` for an empty edge list. -/
theorem checkEdges_empty (lim : Limits) (s : Scale) : checkEdges lim s [] = .error .empty := rfl

/-- `badEdges` for a malformed edge list. -/
theorem checkEdges_bad (lim : Limits) (s : Scale) (e : Nat) (rest : List Nat)
    (h : ¬ (e = 0 ∧ rest ≠ [] ∧ incFromB e rest = true ∧ (e :: rest).getLast? = some s)) :
    checkEdges lim s (e :: rest) = .error .badEdges := by
  dsimp only [checkEdges]; rw [ite_f h]

/-- `tooMany` for more bins than `maxBins`. -/
theorem checkEdges_tooMany (lim : Limits) (s : Scale) (e : Nat) (rest : List Nat)
    (h : e = 0 ∧ rest ≠ [] ∧ incFromB e rest = true ∧ (e :: rest).getLast? = some s)
    (hb : lim.maxBins < rest.length) :
    checkEdges lim s (e :: rest) = .error (.tooMany limitBins rest.length lim.maxBins) := by
  dsimp only [checkEdges]; rw [ite_t h, ite_t hb]

theorem checkSample_ok (lim : Limits) (n : Nat) : checkSample lim n = .ok () ↔ 0 < n ∧ n ≤ lim.maxEvents := by
  unfold checkSample
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h2 : lim.maxEvents < n
  · simp [h0, h2]
  · simp [h0, h2]; try omega

/-- `empty` for an empty sample. -/
theorem checkSample_empty (lim : Limits) : checkSample lim 0 = .error .empty := by
  unfold checkSample; simp

/-- `tooMany` for a sample over `maxEvents`. -/
theorem checkSample_tooMany (lim : Limits) (n : Nat) (h0 : 0 < n) (h : lim.maxEvents < n) :
    checkSample lim n = .error (.tooMany limitEvents n lim.maxEvents) := by
  unfold checkSample; rw [ite_f (by omega), ite_t h]

theorem checkDrawsFrom_ok (n : Nat) (ds : List Nat) : ∀ i, checkDrawsFrom n i ds = .ok () ↔ ∀ d ∈ ds, d < n := by
  induction ds with
  | nil => intro i; simp [checkDrawsFrom]
  | cons d ds ih =>
    intro i
    unfold checkDrawsFrom
    by_cases h : d < n
    · rw [ite_t h, ih]; simp [h]
    · rw [ite_f h]; simp only [reduceCtorEq, false_iff]; intro hh; exact h (hh d (by simp))

theorem checkDraws_ok (n : Nat) (ds : List Nat) : checkDraws n ds = .ok () ↔ ∀ d ∈ ds, d < n :=
  checkDrawsFrom_ok n ds 0

/-- `badDraws` carries the position and the value of the FIRST offending draw. -/
theorem checkDrawsFrom_refuses (n : Nat) (pre rest : List Nat) (d i : Nat)
    (hpre : ∀ x ∈ pre, x < n) (hd : n ≤ d) :
    checkDrawsFrom n i (pre ++ d :: rest) = .error (.badDraws (i + pre.length) d) := by
  induction pre generalizing i with
  | nil => simp [checkDrawsFrom]; omega
  | cons q pre ih =>
    have hq := hpre q (by simp)
    simp only [List.cons_append, checkDrawsFrom, ite_t hq, List.length_cons]
    rw [ih (i + 1) (fun x hx => hpre x (by simp [hx]))]; congr 2; omega

theorem checkNonzero_ok (num : Nat) : checkNonzero num = .ok () ↔ num ≠ 0 := by
  unfold checkNonzero; split <;> simp_all

/-- `zeroProbability`. -/
theorem checkNonzero_zero : checkNonzero 0 = .error .zeroProbability := rfl

/-! ## The validators: ok exactly when every stated condition holds -/

theorem validateBinary_ok (s : Scale) (e : BinaryEvent) :
    validateBinary s e = .ok () ↔ 0 < s ∧ 0 ≤ e.p ∧ e.p ≤ (s : Int) := by
  unfold validateBinary
  rw [bind_ok_iff, checkScale_ok, checkProbs_ok]; simp

/-- Scale zero is `badScale`, before anything else. -/
theorem validateBinary_badScale (e : BinaryEvent) : validateBinary 0 e = .error .badScale := rfl

/-- A probability out of range is `probOutOfRange 0 p`. -/
theorem validateBinary_probOutOfRange (s : Scale) (e : BinaryEvent) (hs : 0 < s) (h : e.p < 0 ∨ (s : Int) < e.p) :
    validateBinary s e = .error (.probOutOfRange 0 e.p) := by
  unfold validateBinary
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs)]
  have := checkProbsFrom_refuses s [] [] e.p 0 (by simp) h
  simpa [checkProbs] using this

theorem validateCategorical_ok (s : Scale) (lim : Limits) (e : CategoricalEvent) :
    validateCategorical s lim e = .ok () ↔
      0 < s ∧ (2 ≤ e.ps.length ∧ e.ps.length ≤ lim.maxOutcomes) ∧ (∀ p ∈ e.ps, 0 ≤ p ∧ p ≤ (s : Int)) ∧
        (sumInt e.ps - (s : Int)).natAbs ≤ lim.tol ∧ e.outcome < e.ps.length := by
  unfold validateCategorical
  rw [bind_ok_iff, bind_ok_iff, bind_ok_iff, bind_ok_iff, checkScale_ok, checkOutcomeCount_ok, checkProbs_ok,
    checkNormalised_ok, checkOutcome_ok]

/-- Scale zero is `badScale`. -/
theorem validateCategorical_badScale (lim : Limits) (e : CategoricalEvent) :
    validateCategorical 0 lim e = .error .badScale := rfl

/-- One outcome is `tooFewOutcomes`. -/
theorem validateCategorical_tooFew (s : Scale) (lim : Limits) (e : CategoricalEvent) (hs : 0 < s) (h : e.ps.length = 1) :
    validateCategorical s lim e = .error (.tooFewOutcomes 1) := by
  unfold validateCategorical
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_err_left _ _ _ (by rw [h]; exact checkOutcomeCount_tooFew lim)]

/-- No outcome is `empty`. -/
theorem validateCategorical_empty (s : Scale) (lim : Limits) (e : CategoricalEvent) (hs : 0 < s) (h : e.ps = []) :
    validateCategorical s lim e = .error .empty := by
  unfold validateCategorical
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_err_left _ _ _ (by rw [h]; exact checkOutcomeCount_empty lim)]

/-- A forecast wider than `maxOutcomes` is `tooMany`. -/
theorem validateCategorical_tooMany (s : Scale) (lim : Limits) (e : CategoricalEvent) (hs : 0 < s)
    (h2 : 2 ≤ e.ps.length) (h : lim.maxOutcomes < e.ps.length) :
    validateCategorical s lim e = .error (.tooMany limitOutcomes e.ps.length lim.maxOutcomes) := by
  unfold validateCategorical
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_err_left _ _ _ (checkOutcomeCount_tooMany lim _ h2 h)]

/-- A probability out of range is `probOutOfRange` at its position (the first offender). -/
theorem validateCategorical_probOutOfRange (s : Scale) (lim : Limits) (e : CategoricalEvent) (hs : 0 < s)
    (pre rest : List Int) (p : Int) (hl : e.ps = pre ++ p :: rest) (hpre : ∀ q ∈ pre, 0 ≤ q ∧ q ≤ (s : Int))
    (hp : p < 0 ∨ (s : Int) < p) (hc : 2 ≤ e.ps.length ∧ e.ps.length ≤ lim.maxOutcomes) :
    validateCategorical s lim e = .error (.probOutOfRange (0 + pre.length) p) := by
  unfold validateCategorical
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_ok_right _ _ ((checkOutcomeCount_ok lim _).2 hc)]
  rw [bind_err_left _ _ _ (by rw [hl]; exact checkProbsFrom_refuses s pre rest p 0 hpre hp)]

/-- A sum off by more than `tol` is `notNormalised`. -/
theorem validateCategorical_notNormalised (s : Scale) (lim : Limits) (e : CategoricalEvent) (hs : 0 < s)
    (hc : 2 ≤ e.ps.length ∧ e.ps.length ≤ lim.maxOutcomes) (hr : ∀ p ∈ e.ps, 0 ≤ p ∧ p ≤ (s : Int))
    (h : lim.tol < (sumInt e.ps - (s : Int)).natAbs) :
    validateCategorical s lim e = .error (.notNormalised (sumInt e.ps)) := by
  unfold validateCategorical
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_ok_right _ _ ((checkOutcomeCount_ok lim _).2 hc),
    bind_ok_right _ _ ((checkProbs_ok s _).2 hr), bind_err_left _ _ _ (checkNormalised_refuses s lim.tol _ h)]

/-- An outcome index past the forecast is `outcomeNotInSupport`. -/
theorem validateCategorical_outcome (s : Scale) (lim : Limits) (e : CategoricalEvent) (hs : 0 < s)
    (hc : 2 ≤ e.ps.length ∧ e.ps.length ≤ lim.maxOutcomes) (hr : ∀ p ∈ e.ps, 0 ≤ p ∧ p ≤ (s : Int))
    (hn : (sumInt e.ps - (s : Int)).natAbs ≤ lim.tol) (h : e.ps.length ≤ e.outcome) :
    validateCategorical s lim e = .error (.outcomeNotInSupport e.outcome e.ps.length) := by
  unfold validateCategorical
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_ok_right _ _ ((checkOutcomeCount_ok lim _).2 hc),
    bind_ok_right _ _ ((checkProbs_ok s _).2 hr), bind_ok_right _ _ ((checkNormalised_ok s _ _).2 hn)]
  exact checkOutcome_refuses _ _ h

theorem validateOrdered_ok (s : Scale) (lim : Limits) (e : OrderedEvent) :
    validateOrdered s lim e = .ok () ↔
      0 < s ∧ e.vals.length = e.ps.length ∧ (2 ≤ e.vals.length ∧ e.vals.length ≤ lim.maxOutcomes) ∧ StrictInc e.vals ∧
        (∀ p ∈ e.ps, 0 ≤ p ∧ p ≤ (s : Int)) ∧ (sumInt e.ps - (s : Int)).natAbs ≤ lim.tol := by
  unfold validateOrdered
  rw [bind_ok_iff, bind_ok_iff, bind_ok_iff, bind_ok_iff, bind_ok_iff, checkScale_ok, checkAligned_ok,
    checkOutcomeCount_ok, checkIncreasing_ok, checkProbs_ok, checkNormalised_ok]

/-- Scale zero is `badScale`. -/
theorem validateOrdered_badScale (lim : Limits) (e : OrderedEvent) : validateOrdered 0 lim e = .error .badScale := rfl

/-- Misaligned `vals` and `ps` are `lengthMismatch`. -/
theorem validateOrdered_lengthMismatch (s : Scale) (lim : Limits) (e : OrderedEvent) (hs : 0 < s)
    (h : e.vals.length ≠ e.ps.length) :
    validateOrdered s lim e = .error (.lengthMismatch e.vals.length e.ps.length) := by
  unfold validateOrdered
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_err_left _ _ _ (checkAligned_refuses _ _ h)]

/-- A support that is not strictly increasing is `supportNotIncreasing`. -/
theorem validateOrdered_notIncreasing (s : Scale) (lim : Limits) (e : OrderedEvent) (hs : 0 < s)
    (ha : e.vals.length = e.ps.length) (hc : 2 ≤ e.vals.length ∧ e.vals.length ≤ lim.maxOutcomes)
    (h : ¬ StrictInc e.vals) :
    validateOrdered s lim e = .error .supportNotIncreasing := by
  unfold validateOrdered
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_ok_right _ _ ((checkAligned_ok _ _).2 ha),
    bind_ok_right _ _ ((checkOutcomeCount_ok lim _).2 hc), bind_err_left _ _ _ (checkIncreasing_refuses _ h)]

/-- A support of fewer than two values is `tooFewOutcomes`. -/
theorem validateOrdered_tooFew (s : Scale) (lim : Limits) (e : OrderedEvent) (hs : 0 < s)
    (ha : e.vals.length = e.ps.length) (h : e.vals.length = 1) :
    validateOrdered s lim e = .error (.tooFewOutcomes 1) := by
  unfold validateOrdered
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_ok_right _ _ ((checkAligned_ok _ _).2 ha),
    bind_err_left _ _ _ (by rw [h]; exact checkOutcomeCount_tooFew lim)]

/-- A forecast whose sum is off by more than `tol` is `notNormalised`. -/
theorem validateOrdered_notNormalised (s : Scale) (lim : Limits) (e : OrderedEvent) (hs : 0 < s)
    (ha : e.vals.length = e.ps.length) (hc : 2 ≤ e.vals.length ∧ e.vals.length ≤ lim.maxOutcomes)
    (hi : StrictInc e.vals) (hr : ∀ p ∈ e.ps, 0 ≤ p ∧ p ≤ (s : Int))
    (h : lim.tol < (sumInt e.ps - (s : Int)).natAbs) :
    validateOrdered s lim e = .error (.notNormalised (sumInt e.ps)) := by
  unfold validateOrdered
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_ok_right _ _ ((checkAligned_ok _ _).2 ha),
    bind_ok_right _ _ ((checkOutcomeCount_ok lim _).2 hc), bind_ok_right _ _ ((checkIncreasing_ok _).2 hi),
    bind_ok_right _ _ ((checkProbs_ok s _).2 hr), checkNormalised_refuses s lim.tol _ h]

theorem validateQuantile_ok (s : Scale) (e : QuantileEvent) :
    validateQuantile s e = .ok () ↔ 0 < s ∧ 0 < e.level ∧ e.level < s := by
  unfold validateQuantile
  rw [bind_ok_iff, checkScale_ok, checkLevel_ok]

/-- Scale zero is `badScale`. -/
theorem validateQuantile_badScale (e : QuantileEvent) : validateQuantile 0 e = .error .badScale := rfl

/-- A level outside `(0, s)` is `badLevel`. -/
theorem validateQuantile_badLevel (s : Scale) (e : QuantileEvent) (hs : 0 < s) (h : ¬ (0 < e.level ∧ e.level < s)) :
    validateQuantile s e = .error (.badLevel e.level s) := by
  unfold validateQuantile
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs)]
  exact checkLevel_refuses _ _ h

theorem validateInterval_ok (s : Scale) (e : IntervalEvent) :
    validateInterval s e = .ok () ↔ 0 < s ∧ (0 < e.tail ∧ 2 * e.tail < s) ∧ e.lo ≤ e.hi := by
  unfold validateInterval
  rw [bind_ok_iff, bind_ok_iff, checkScale_ok, checkTail_ok, checkInterval_ok]

/-- Scale zero is `badScale`. -/
theorem validateInterval_badScale (e : IntervalEvent) : validateInterval 0 e = .error .badScale := rfl

/-- A tail outside its open range is `badLevel`. -/
theorem validateInterval_badLevel (s : Scale) (e : IntervalEvent) (hs : 0 < s) (h : ¬ (0 < e.tail ∧ 2 * e.tail < s)) :
    validateInterval s e = .error (.badLevel e.tail s) := by
  unfold validateInterval
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_err_left _ _ _ (checkTail_refuses _ _ h)]

/-- A crossed interval is `crossedInterval`. -/
theorem validateInterval_crossed (s : Scale) (e : IntervalEvent) (hs : 0 < s) (ht : 0 < e.tail ∧ 2 * e.tail < s)
    (h : e.hi < e.lo) : validateInterval s e = .error (.crossedInterval e.lo e.hi) := by
  unfold validateInterval
  rw [bind_ok_right _ _ ((checkScale_ok s).2 hs), bind_ok_right _ _ ((checkTail_ok _ _).2 ht)]
  exact checkInterval_refuses _ _ h

/-! ## Non-vacuity witnesses: for each refusal, a literal input that triggers it, and an input that passes -/

/-- Limits for the witnesses. -/
def witLim : Limits := ⟨100, 5, 4, 100, 3, 8, 0⟩

example : validateBinary 10 ⟨7, true⟩ = .ok () := rfl
example : validateBinary 0 ⟨7, true⟩ = .error .badScale := rfl
example : validateBinary 10 ⟨11, true⟩ = .error (.probOutOfRange 0 11) := rfl
example : validateBinary 10 ⟨-1, false⟩ = .error (.probOutOfRange 0 (-1)) := rfl
example : validateCategorical 10 witLim ⟨[5, 3, 2], 0⟩ = .ok () := rfl
example : validateCategorical 10 witLim ⟨[5, 3, 2], 3⟩ = .error (.outcomeNotInSupport 3 3) := rfl
example : validateCategorical 10 witLim ⟨[5, 3, 3], 0⟩ = .error (.notNormalised 11) := rfl
example : validateCategorical 10 { witLim with tol := 1 } ⟨[5, 3, 3], 0⟩ = .ok () := rfl
example : validateCategorical 10 witLim ⟨[5, 11, -6], 0⟩ = .error (.probOutOfRange 1 11) := rfl
example : validateCategorical 10 witLim ⟨[10], 0⟩ = .error (.tooFewOutcomes 1) := rfl
example : validateCategorical 10 witLim ⟨[], 0⟩ = .error .empty := rfl
example : validateCategorical 10 witLim ⟨[2, 2, 2, 2, 2, 0], 0⟩ = .error (.tooMany limitOutcomes 6 5) := rfl
example : validateOrdered 10 witLim ⟨[1, 2, 3], [5, 3, 2], 2⟩ = .ok () := rfl
example : validateOrdered 10 witLim ⟨[1, 2], [5, 3, 2], 2⟩ = .error (.lengthMismatch 2 3) := rfl
example : validateOrdered 10 witLim ⟨[1, 1, 3], [5, 3, 2], 2⟩ = .error .supportNotIncreasing := rfl
example : validateOrdered 10 witLim ⟨[3, 2, 1], [5, 3, 2], 2⟩ = .error .supportNotIncreasing := rfl
example : validateOrdered 10 witLim ⟨[1, 2, 3], [5, 3, 1], 2⟩ = .error (.notNormalised 9) := rfl
example : validateQuantile 10 ⟨9, 5, 8⟩ = .ok () := rfl
example : validateQuantile 10 ⟨10, 5, 8⟩ = .error (.badLevel 10 10) := rfl
example : validateQuantile 10 ⟨0, 5, 8⟩ = .error (.badLevel 0 10) := rfl
example : validateInterval 10 ⟨1, 2, 6, 9⟩ = .ok () := rfl
example : validateInterval 10 ⟨5, 2, 6, 9⟩ = .error (.badLevel 5 10) := rfl
example : validateInterval 10 ⟨1, 6, 2, 9⟩ = .error (.crossedInterval 6 2) := rfl
example : checkEdges witLim 10 [0, 5, 10] = .ok () := rfl
example : checkEdges witLim 10 [] = .error .empty := rfl
example : checkEdges witLim 10 [0, 10] = .ok () := rfl
example : checkEdges witLim 10 [0] = .error .badEdges := rfl
example : checkEdges witLim 10 [1, 5, 10] = .error .badEdges := rfl
example : checkEdges witLim 10 [0, 5, 5, 10] = .error .badEdges := rfl
example : checkEdges witLim 10 [0, 5, 9] = .error .badEdges := rfl
example : checkEdges witLim 10 [0, 1, 2, 3, 4, 10] = .error (.tooMany limitBins 5 4) := rfl
example : checkSample witLim 5 = .ok () := rfl
example : checkSample witLim 0 = .error .empty := rfl
example : checkSample witLim 101 = .error (.tooMany limitEvents 101 100) := rfl
example : checkDraws 3 [0, 1, 2] = .ok () := rfl
example : checkDraws 3 [0, 1, 3, 2] = .error (.badDraws 2 3) := rfl
example : checkNonzero 5 = .ok () := rfl
example : checkNonzero 0 = .error .zeroProbability := rfl
example : checkAligned 3 3 = .ok () := rfl
example : checkAligned 2 3 = .error (.lengthMismatch 2 3) := rfl

end VbmForecast
