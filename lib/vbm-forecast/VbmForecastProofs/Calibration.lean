import VbmForecast.Calibration
import VbmForecastProofs.Brier
/-! # S5 proofs: calibration

Properties 5 (the reliability table is permutation invariant), 6 (reliability counts; every valid probability falls in exactly one bin) and 7 (calibration error zero iff perfectly calibrated) of `docs/spec.md`, section 8, calibration in the large, and the vectors V9-V11. Exact integer arithmetic; each conditional theorem has a non-vacuity witness over small literals. -/
namespace VbmForecast

/-! ## Bins -/

theorem InB_lower : ∀ (ups : List Nat) (prev : Nat) (p : Int) (m : Nat), IncFrom prev ups → InB prev ups p m → (prev : Int) ≤ p
  | [], _, _, _, _, h => absurd h (by simp [InB])
  | u :: us, prev, p, 0, _, h => h.1
  | u :: us, prev, p, m + 1, hinc, h => by
    have h1 := InB_lower us u p m hinc.2 h
    have h2 := hinc.1
    omega

theorem binFrom_iff (ups : List Nat) : ∀ (prev k j : Nat) (p : Int), IncFrom prev ups → (prev : Int) ≤ p →
    (binFrom k ups p = some j ↔ k ≤ j ∧ InB prev ups p (j - k)) := by
  induction ups with
  | nil => intro prev k j p _ _; simp [binFrom, InB]
  | cons u us ih =>
    intro prev k j p hinc hp
    obtain ⟨hlt, hinc'⟩ := hinc
    cases us with
    | nil =>
      simp only [binFrom]
      by_cases h : p ≤ (u : Int)
      · simp only [h, ite_true, Option.some.injEq]
        constructor
        · intro hk; subst hk; simp only [Nat.le_refl, Nat.sub_self, true_and, InB]; omega
        · rintro ⟨hkj, hb⟩
          cases hm : j - k with
          | zero => omega
          | succ m => rw [hm] at hb; simp [InB] at hb
      · simp only [h, ite_false, reduceCtorEq, false_iff]
        rintro ⟨hkj, hb⟩
        cases hm : j - k with
        | zero => rw [hm] at hb; simp only [InB] at hb; omega
        | succ m => rw [hm] at hb; simp [InB] at hb
    | cons r rs =>
      simp only [binFrom]
      by_cases h : p < (u : Int)
      · simp only [h, ite_true, Option.some.injEq]
        constructor
        · intro hk; subst hk; simp only [Nat.le_refl, Nat.sub_self, true_and, InB]; omega
        · rintro ⟨hkj, hb⟩
          cases hm : j - k with
          | zero => omega
          | succ m =>
            rw [hm] at hb
            have := InB_lower _ _ _ _ hinc' hb
            omega
      · simp only [h, ite_false]
        have hu : (u : Int) ≤ p := by omega
        rw [ih u (k + 1) j p hinc' hu]
        constructor
        · rintro ⟨hkj, hb⟩
          refine ⟨by omega, ?_⟩
          have : j - k = (j - (k + 1)) + 1 := by omega
          rw [this]; exact hb
        · rintro ⟨hkj, hb⟩
          cases hm : j - k with
          | zero => rw [hm] at hb; simp [InB] at hb; omega
          | succ m =>
            rw [hm] at hb
            refine ⟨by omega, ?_⟩
            have : j - (k + 1) = m := by omega
            rw [this]; exact hb

theorem binOf_iff (e : Nat) (ups : List Nat) (hinc : IncFrom e ups) (p : Int) (j : Nat) :
    binOf (e :: ups) p = some j ↔ InBin (e :: ups) j p := by
  unfold binOf InBin
  by_cases h : (e : Int) ≤ p
  · simp only [h, ite_true]
    rw [binFrom_iff ups e 0 j p hinc h]; simp
  · simp only [h, ite_false, reduceCtorEq, false_iff]
    intro hb
    exact h (InB_lower _ _ _ _ hinc hb)

theorem binFrom_exists (s : Nat) (ups : List Nat) : ∀ (prev k : Nat) (p : Int), IncFrom prev ups → (prev : Int) ≤ p → ups ≠ [] →
    (prev :: ups).getLast? = some s → p ≤ (s : Int) → ∃ j, binFrom k ups p = some j ∧ j < k + ups.length := by
  induction ups with
  | nil => intro _ _ _ _ _ h; exact absurd rfl h
  | cons u us ih =>
    intro prev k p hinc hp _ hl hps
    cases us with
    | nil =>
      have : u = s := by simpa using hl
      subst this
      exact ⟨k, by simp [binFrom, hps], by simp⟩
    | cons r rs =>
      simp only [binFrom]
      by_cases h : p < (u : Int)
      · exact ⟨k, by simp [h], by simp⟩
      · simp only [h, ite_false]
        have hl' : (u :: r :: rs).getLast? = some s := by simpa using hl
        obtain ⟨j, hj, hjl⟩ := ih u (k + 1) p hinc.2 (by omega) (by simp) hl' hps
        exact ⟨j, hj, by simp only [List.length_cons] at hjl ⊢; omega⟩

/-- Edges `0 = e₀ < e₁ < ... < e_B = s`, `B ≥ 1`. -/
def GoodEdges (s : Scale) (edges : List Nat) : Prop :=
  ∃ e rest, edges = e :: rest ∧ e = 0 ∧ rest ≠ [] ∧ IncFrom e rest ∧ (e :: rest).getLast? = some s

/-- Every probability in `[0, s]` lies in exactly one bin: `binOf` finds it and no other bin holds it. -/
theorem bin_unique (s : Scale) (edges : List Nat) (hg : GoodEdges s edges) (p : Int) (h0 : 0 ≤ p) (h1 : p ≤ (s : Int)) :
    ∃ j, j < edges.length - 1 ∧ binOf edges p = some j ∧ InBin edges j p ∧ ∀ j', InBin edges j' p → j' = j := by
  obtain ⟨e, rest, rfl, rfl, hne, hinc, hl⟩ := hg
  obtain ⟨j, hj, hjl⟩ := binFrom_exists s rest 0 0 p hinc (by simpa using h0) hne hl h1
  have hb : binOf (0 :: rest) p = some j := by unfold binOf; simp [h0, hj]
  refine ⟨j, by simpa using hjl, hb, (binOf_iff 0 rest hinc p j).1 hb, ?_⟩
  intro j' hj'
  have := (binOf_iff 0 rest hinc p j').2 hj'
  rw [hb] at this; exact (Option.some.inj this).symm

-- Witness: `s = 10`, edges `[0, 5, 10]`: `4` is in bin 0, `5` in bin 1, `10` (the last edge) in bin 1.
example : GoodEdges 10 [0, 5, 10] := ⟨0, [5, 10], rfl, rfl, by decide, by simp [IncFrom], by decide⟩
example : binOf [0, 5, 10] 4 = some 0 := by decide
example : binOf [0, 5, 10] 5 = some 1 := by decide
example : binOf [0, 5, 10] 10 = some 1 := by decide
example : binOf [0, 5, 10] 0 = some 0 := by decide
example : binOf [0, 5, 10] 11 = none := by decide
example : binOf [0, 5, 10] (-1) = none := by decide
example : InBin [0, 5, 10] 1 10 := by simp [InBin, InB]

/-! ## The table -/

theorem checkRange_ok (s : Scale) (es : List BinaryEvent) :
    checkRange s es = .ok () ↔ ∀ e ∈ es, 0 ≤ e.p ∧ e.p ≤ (s : Int) := by
  unfold checkRange
  by_cases h : es.all (fun e => decide (0 ≤ e.p ∧ e.p ≤ (s : Int))) = true
  · rw [ite_t h]; simpa using h
  · rw [ite_f h]
    simp only [reduceCtorEq, false_iff]
    intro h'; exact h (by simpa using h')

theorem reliability_ok (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) (rows : List Row) :
    reliability s lim edges es = .ok rows ↔
      0 < s ∧ checkEdges lim s edges = .ok () ∧ (0 < es.length ∧ es.length ≤ lim.maxEvents) ∧
        (∀ e ∈ es, 0 ≤ e.p ∧ e.p ≤ (s : Int)) ∧ rows = table edges es := by
  unfold reliability
  rw [bind_ok_iff, bind_ok_iff, bind_ok_iff, bind_ok_iff, checkScale_ok, checkSample_ok, checkRange_ok]
  simp only [pure, Except.pure, Except.ok.injEq]
  grind

theorem table_length (edges : List Nat) (es : List BinaryEvent) : (table edges es).length = edges.length - 1 := by
  simp [table]

theorem incFrom_of_B : ∀ (rest : List Nat) (prev : Nat), incFromB prev rest = true → IncFrom prev rest
  | [], _, _ => trivial
  | x :: xs, prev, h => by
    simp only [incFromB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, incFrom_of_B xs x h.2⟩

/-- The good edges are what `checkEdges` accepts. -/
theorem goodEdges_of_check (lim : Limits) (s : Scale) (edges : List Nat) (h : checkEdges lim s edges = .ok ()) :
    GoodEdges s edges := by
  obtain ⟨e, rest, rfl, he, hne, hinc, hl, _⟩ := (checkEdges_ok lim s edges).1 h
  exact ⟨e, rest, rfl, he, hne, incFrom_of_B rest e hinc, hl⟩

/-! ## Summing the table -/

/-- `Σ_{j < n} f j`. -/
def sumR (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumR f n + f n

theorem sumR_add (f g : Nat → Nat) (n : Nat) : sumR (fun j => f j + g j) n = sumR f n + sumR g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumR, ih]; omega

theorem sumR_before (o : Option Nat) (w j0 : Nat) (h : o = some j0) : ∀ B, B ≤ j0 → sumR (fun j => if o = some j then w else 0) B = 0 := by
  intro B
  induction B with
  | zero => intro _; rfl
  | succ B ih =>
    intro hB
    have hne : ¬ (o = some B) := by rw [h]; simp; omega
    simp only [sumR, ih (by omega), ite_f hne]

theorem sumR_const_ite (o : Option Nat) (w j0 B : Nat) (h : o = some j0) (hj : j0 < B) :
    sumR (fun j => if o = some j then w else 0) B = w := by
  induction B with
  | zero => omega
  | succ B ih =>
    by_cases hb : j0 < B
    · have hne : ¬ (o = some B) := by rw [h]; simp; omega
      simp only [sumR, ih hb, ite_f hne]; omega
    · have hj0 : j0 = B := by omega
      subst hj0
      simp only [sumR, sumR_before o w j0 h j0 (Nat.le_refl _), ite_t h]; omega

theorem sum_range_map (f : Nat → Nat) (n : Nat) : ((List.range n).map f).sum = sumR f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [sumR]

theorem wBin_sum (edges : List Nat) (B : Nat) (w : BinaryEvent → Nat) (es : List BinaryEvent)
    (h : ∀ e ∈ es, ∃ j0, binOf edges e.p = some j0 ∧ j0 < B) :
    sumR (fun j => wBin edges j w es) B = (es.map w).sum := by
  induction es with
  | nil => simp only [wBin, List.map_nil, List.sum_nil]; clear h; induction B with | zero => rfl | succ n ih => simp [sumR, ih]
  | cons e es ih =>
    obtain ⟨j0, hj0, hjB⟩ := h e (by simp)
    have h' : ∀ x ∈ es, ∃ j0, binOf edges x.p = some j0 ∧ j0 < B := fun x hx => h x (by simp [hx])
    have := sumR_add (fun j => if binOf edges e.p = some j then w e else 0) (fun j => wBin edges j w es) B
    simp only [wBin, this, ih h', sumR_const_ite _ _ _ _ hj0 hjB, List.map_cons, List.sum_cons]

/-- The sums of a table's columns, given every forecast lies in one bin. -/
theorem table_col_sum (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent)
    (hc : checkEdges lim s edges = .ok ()) (hr : ∀ e ∈ es, 0 ≤ e.p ∧ e.p ≤ (s : Int)) (w : BinaryEvent → Nat)
    (col : Row → Nat) (hcol : ∀ j, col (rowAt edges es j) = wBin edges j w es) :
    ((table edges es).map col).sum = (es.map w).sum := by
  have hg := goodEdges_of_check lim s edges hc
  unfold table
  rw [List.map_map]
  have : (col ∘ rowAt edges es) = fun j => wBin edges j w es := funext hcol
  rw [this, sum_range_map]
  apply wBin_sum
  intro e he
  obtain ⟨j, hj, hb, _⟩ := bin_unique s edges hg e.p (hr e he).1 (hr e he).2
  exact ⟨j, hb, hj⟩

theorem hit_count (es : List BinaryEvent) : (es.map wHit).sum = (es.filter (·.hit)).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases hh : e.hit <;> simp [wHit, hh, ih] <;> omega

theorem prob_sum (s : Scale) (es : List BinaryEvent) (hr : ∀ e ∈ es, 0 ≤ e.p ∧ e.p ≤ (s : Int)) :
    (((es.map wProb).sum : Nat) : Int) = sumInt (es.map (·.p)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h1 := ih (fun x hx => hr x (by simp [hx]))
    have h0 : 0 ≤ e.p := (hr e (by simp)).1
    simp only [List.map_cons, List.sum_cons, sumInt, wProb] at h1 ⊢
    have h2 : ((e.p.toNat : Nat) : Int) = e.p := Int.toNat_of_nonneg h0
    omega

/-! ## Property 6: reliability counts -/

/-- The `n` of the rows sum to the number of events. -/
theorem reliability_n_sum (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) (rows : List Row)
    (h : reliability s lim edges es = .ok rows) : (rows.map Row.n).sum = es.length := by
  obtain ⟨_, hc, _, hr, rfl⟩ := (reliability_ok s lim edges es rows).1 h
  have := table_col_sum s lim edges es hc hr (fun _ => 1) Row.n (fun _ => rfl)
  rw [this]
  generalize es = xs
  induction xs with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- The `hits` of the rows sum to the number of `hit` events. -/
theorem reliability_hits_sum (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) (rows : List Row)
    (h : reliability s lim edges es = .ok rows) : (rows.map Row.hits).sum = (es.filter (·.hit)).length := by
  obtain ⟨_, hc, _, hr, rfl⟩ := (reliability_ok s lim edges es rows).1 h
  rw [table_col_sum s lim edges es hc hr wHit Row.hits (fun _ => rfl), hit_count]

/-- The `sumP` of the rows sum to `Σ p`. -/
theorem reliability_sumP_sum (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) (rows : List Row)
    (h : reliability s lim edges es = .ok rows) : (((rows.map Row.sumP).sum : Nat) : Int) = sumInt (es.map (·.p)) := by
  obtain ⟨_, hc, _, hr, rfl⟩ := (reliability_ok s lim edges es rows).1 h
  rw [table_col_sum s lim edges es hc hr wProb Row.sumP (fun _ => rfl)]
  exact prob_sum s es hr

/-- One row per bin. -/
theorem reliability_length (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) (rows : List Row)
    (h : reliability s lim edges es = .ok rows) : rows.length = edges.length - 1 := by
  obtain ⟨_, _, _, _, rfl⟩ := (reliability_ok s lim edges es rows).1 h
  exact table_length edges es

-- Witness: the vector of section 10 (V9) satisfies the hypothesis and the counts: `n = 3 + 4 = 7`, `hits = 1 + 3 = 4`, `sumP = 9 + 34 = 43`.
/-- The sample of vector V9: forecasts and outcomes `(2,0) (3,1) (4,0) (7,1) (8,1) (9,0) (10,1)`. -/
def v9 : List BinaryEvent := [⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩, ⟨7, true⟩, ⟨8, true⟩, ⟨9, false⟩, ⟨10, true⟩]

example : reliability 10 witLim [0, 5, 10] v9 = .ok [⟨0, 5, 3, 1, 9⟩, ⟨5, 10, 4, 3, 34⟩] := by rfl
example : (([Row.mk 0 5 3 1 9, ⟨5, 10, 4, 3, 34⟩].map Row.n).sum, ([Row.mk 0 5 3 1 9, ⟨5, 10, 4, 3, 34⟩].map Row.hits).sum,
    ([Row.mk 0 5 3 1 9, ⟨5, 10, 4, 3, 34⟩].map Row.sumP).sum) = (v9.length, (v9.filter (·.hit)).length, 43) := by decide +kernel
example : sumInt (v9.map (·.p)) = 43 := by decide +kernel

/-! ## Property 5 (table part): permutation invariance -/

theorem wBin_perm (edges : List Nat) (j : Nat) (w : BinaryEvent → Nat) {xs ys : List BinaryEvent} (h : xs.Perm ys) :
    wBin edges j w xs = wBin edges j w ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [wBin, ih]
  | swap x y l => simp only [wBin]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem table_perm (edges : List Nat) {xs ys : List BinaryEvent} (h : xs.Perm ys) : table edges xs = table edges ys := by
  unfold table rowAt
  simp only [wBin_perm edges _ _ h]

theorem checkRange_perm (s : Scale) {xs ys : List BinaryEvent} (h : xs.Perm ys) : checkRange s xs = checkRange s ys := by
  unfold checkRange
  have : xs.all (fun e => decide (0 ≤ e.p ∧ e.p ≤ (s : Int))) = ys.all (fun e => decide (0 ≤ e.p ∧ e.p ≤ (s : Int))) := by
    rw [Bool.eq_iff_iff]; simp only [List.all_eq_true]
    constructor
    · intro hh e he; exact hh e (h.mem_iff.2 he)
    · intro hh e he; exact hh e (h.mem_iff.1 he)
  rw [this]

/-- The reliability table, with its refusals, is the same for any order of the events. -/
theorem reliability_perm (s : Scale) (lim : Limits) (edges : List Nat) {xs ys : List BinaryEvent} (h : xs.Perm ys) :
    reliability s lim edges xs = reliability s lim edges ys := by
  unfold reliability
  rw [h.length_eq, checkRange_perm s h, table_perm edges h]

-- Witness: `[a, b, c] ~ [c, a, b]` with distinct events; the tables are equal and non-trivial.
example : [BinaryEvent.mk 2 false, ⟨7, true⟩, ⟨10, true⟩].Perm [⟨10, true⟩, ⟨2, false⟩, ⟨7, true⟩] :=
  (List.Perm.cons _ (List.Perm.swap _ _ [])).trans (List.Perm.swap _ _ _)
example : reliability 10 witLim [0, 5, 10] [⟨2, false⟩, ⟨7, true⟩, ⟨10, true⟩] =
    reliability 10 witLim [0, 5, 10] [⟨10, true⟩, ⟨2, false⟩, ⟨7, true⟩] := by rfl
example : reliability 10 witLim [0, 5, 10] [⟨2, false⟩, ⟨7, true⟩, ⟨10, true⟩] = .ok [⟨0, 5, 1, 0, 2⟩, ⟨5, 10, 2, 2, 17⟩] := by
  rfl

/-! ## Property 7: calibration error -/

/-- A sample is perfectly calibrated at the given bins: in every non-empty bin `hits * s = sumP`. -/
def Perfect (s : Scale) (rows : List Row) : Prop := ∀ r ∈ rows, 0 < r.n → r.hits * s = r.sumP

theorem wBin_zero (edges : List Nat) (j : Nat) (w : BinaryEvent → Nat) (es : List BinaryEvent)
    (h : wBin edges j (fun _ => 1) es = 0) : wBin edges j w es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [wBin] at *
    by_cases hb : binOf edges e.p = some j
    · rw [ite_t hb] at h; omega
    · rw [ite_f hb] at h ⊢; have := ih (by omega); omega

theorem rowAt_empty (edges : List Nat) (es : List BinaryEvent) (j : Nat) (h : (rowAt edges es j).n = 0) :
    (rowAt edges es j).hits = 0 ∧ (rowAt edges es j).sumP = 0 :=
  ⟨wBin_zero edges j wHit es h, wBin_zero edges j wProb es h⟩

theorem table_empty_rows (edges : List Nat) (es : List BinaryEvent) :
    ∀ r ∈ table edges es, r.n = 0 → r.hits = 0 ∧ r.sumP = 0 := by
  intro r hr hn
  unfold table at hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hr
  exact rowAt_empty edges es j hn

theorem sum_natAbs_zero (xs : List Int) : (xs.map Int.natAbs).sum = 0 ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp]; rw [← ih]; omega

theorem calibNum_zero_iff (s : Scale) (rows : List Row) (hrows : ∀ r ∈ rows, r.n = 0 → r.hits = 0 ∧ r.sumP = 0) :
    calibNum s rows = 0 ↔ Perfect s rows := by
  unfold calibNum Perfect
  have : (rows.map fun r => (((r.hits * s : Nat) : Int) - (r.sumP : Int)).natAbs) =
      (rows.map fun r => (((r.hits * s : Nat) : Int) - (r.sumP : Int))).map Int.natAbs := by simp [List.map_map, Function.comp_def]
  rw [this, sum_natAbs_zero]
  constructor
  · intro h r hr _
    have := h _ (List.mem_map.2 ⟨r, hr, rfl⟩); omega
  · intro h x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    by_cases hn : r.n = 0
    · obtain ⟨h1, h2⟩ := hrows r hr hn; simp [h1, h2]
    · have := h r hr (by omega); omega

/-- The calibration error is the stated ratio `Σ_j |hits_j * s - sumP_j| / (N * s)` once the table exists. -/
theorem calibrationError_ok (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) (rows : List Row)
    (h : reliability s lim edges es = .ok rows) :
    ∃ r, calibrationError s lim edges es = .ok r ∧ r.num = (calibNum s rows : Int) ∧ r.den = es.length * s := by
  obtain ⟨hs, _, ⟨hn, _⟩, _, _⟩ := (reliability_ok s lim edges es rows).1 h
  have hp : 0 < es.length * s := Nat.mul_pos hn hs
  unfold calibrationError
  rw [h]
  simp only [bind, Except.bind, ratioOf, hp, dite_true]
  exact ⟨_, rfl, rfl, rfl⟩

/-- Calibration error zero iff perfectly calibrated. -/
theorem calibrationError_zero_iff (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) (rows : List Row) (r : Ratio)
    (h : reliability s lim edges es = .ok rows) (hr : calibrationError s lim edges es = .ok r) :
    r.num = 0 ↔ Perfect s rows := by
  obtain ⟨r', hr', hn, _⟩ := calibrationError_ok s lim edges es rows h
  rw [hr'] at hr
  have : r' = r := Except.ok.inj hr
  subst this
  have ht := (reliability_ok s lim edges es rows).1 h
  rw [hn, ← calibNum_zero_iff s rows (by rw [ht.2.2.2.2]; exact table_empty_rows edges es)]
  omega

-- Witness: `s = 10`, edges `[0, 10]`, forecasts `5, 5` with outcomes hit, miss: `hits * s = 10 = sumP`, error `0`.
example : reliability 10 witLim [0, 10] [⟨5, true⟩, ⟨5, false⟩] = .ok [⟨0, 10, 2, 1, 10⟩] := by rfl
example : (calibrationError 10 witLim [0, 10] [⟨5, true⟩, ⟨5, false⟩]).map (fun r => (r.num, r.den)) = .ok (0, 20) := by rfl
example : Perfect 10 [⟨0, 10, 2, 1, 10⟩] := by
  intro r hr _; simp only [List.mem_singleton] at hr; subst hr; decide
-- Counter-witness: forecasts `5, 5` both hit: `hits * s = 20 ≠ 10 = sumP`, error `10 / 20`.
example : (calibrationError 10 witLim [0, 10] [⟨5, true⟩, ⟨5, true⟩]).map (fun r => (r.num, r.den)) = .ok (10, 20) := by rfl
example : ¬ Perfect 10 [⟨0, 10, 2, 2, 10⟩] := by
  intro h; have := h ⟨0, 10, 2, 2, 10⟩ (by simp) (by decide); revert this; decide

/-! ## Calibration in the large -/

theorem bind_ok_right' {α : Type} (a : Except Refusal Unit) (b : Except Refusal α) (h : a = .ok ()) :
    (a >>= fun _ => b) = b := by
  subst h; rfl


/-- The stated ratios, once the checks pass. -/
theorem citl_ok (s : Scale) (lim : Limits) (es : List BinaryEvent)
    (hs : 0 < s) (hn : 0 < es.length) (hm : es.length ≤ lim.maxEvents) (hr : ∀ e ∈ es, 0 ≤ e.p ∧ e.p ≤ (s : Int)) :
    ∃ m o g, citl s lim es = .ok (m, o, g) ∧
      m.num = sumInt (es.map (·.p)) ∧ m.den = es.length * s ∧
      o.num = ((es.filter (·.hit)).length : Int) ∧ o.den = es.length ∧
      g.num = ((es.filter (·.hit)).length : Int) * s - sumInt (es.map (·.p)) ∧ g.den = es.length * s := by
  have hp : 0 < es.length * s := Nat.mul_pos hn hs
  have c1 : checkScale s = .ok () := (checkScale_ok s).2 hs
  have c2 : checkSample lim es.length = .ok () := (checkSample_ok _ _).2 ⟨hn, hm⟩
  have c3 : checkProbs s (es.map (·.p)) = .ok () := (checkProbs_ok _ _).2 (by
    intro p hp'; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp'; exact hr e he)
  have key : citl s lim es = .ok (⟨sumInt (es.map (·.p)), es.length * s, hp⟩, ⟨((es.map wHit).sum : Nat), es.length, hn⟩,
      ⟨(((es.map wHit).sum : Nat) : Int) * s - sumInt (es.map (·.p)), es.length * s, hp⟩) := by
    unfold citl
    rw [bind_ok_right' _ _ c1, bind_ok_right' _ _ c2, bind_ok_right' _ _ c3]
    simp only [bind, Except.bind, ratioOf, hp, hn, dite_true]
    rfl
  refine ⟨_, _, _, key, rfl, rfl, ?_, rfl, ?_, rfl⟩ <;> simp only [hit_count]

/-- Zero gap iff `H * s = Σ p`. -/
theorem citl_gap_zero_iff (s : Scale) (lim : Limits) (es : List BinaryEvent) (m o g : Ratio)
    (hs : 0 < s) (hn : 0 < es.length) (hm : es.length ≤ lim.maxEvents) (hr : ∀ e ∈ es, 0 ≤ e.p ∧ e.p ≤ (s : Int))
    (h : citl s lim es = .ok (m, o, g)) :
    g.num = 0 ↔ ((es.filter (·.hit)).length : Int) * s = sumInt (es.map (·.p)) := by
  obtain ⟨m', o', g', h', _, _, _, _, hg, _⟩ := citl_ok s lim es hs hn hm hr
  rw [h'] at h
  have := Except.ok.inj h
  simp only [Prod.mk.injEq] at this
  obtain ⟨-, -, rfl⟩ := this
  omega

-- Witness: `s = 10`, `5, 5` hit and miss: gap zero (`H * s = 10 = Σ p`); `5, 5` both hit: gap `20 - 10 = 10 ≠ 0`.
example : (citl 10 witLim [⟨5, true⟩, ⟨5, false⟩]).map (fun t => (t.2.2.num, t.2.2.den)) = .ok (0, 20) := by rfl
example : (citl 10 witLim [⟨5, true⟩, ⟨5, true⟩]).map (fun t => (t.2.2.num, t.2.2.den)) = .ok (10, 20) := by rfl
example : (citl 0 witLim [⟨5, true⟩]).isOk = false := by decide +kernel
example : (citl 10 witLim []).isOk = false := by decide +kernel

/-! ## Vectors V9-V11 -/

example : reliability 10 witLim [0, 5, 10] v9 = .ok [⟨0, 5, 3, 1, 9⟩, ⟨5, 10, 4, 3, 34⟩] := rfl   -- V9
example : v9.length = 7 := by decide +kernel                                                                  -- V9: N = 7
example : (calibrationError 10 witLim [0, 5, 10] v9).map (fun r => (r.num, r.den)) = .ok (5, 70) := rfl   -- V10: 5/70 = 1/14
example : (citl 10 witLim v9).map (fun t => ((t.1.num, t.1.den), (t.2.1.num, t.2.1.den), (t.2.2.num, t.2.2.den))) =
    .ok ((43, 70), (4, 7), (-3, 70)) := by rfl                                                   -- V11: 43/70, 4/7 = 40/70, -3/70

end VbmForecast
