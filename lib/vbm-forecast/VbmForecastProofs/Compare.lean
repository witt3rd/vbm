import VbmForecast.Compare
import VbmForecastProofs.Rep
/-! # S6 proofs: comparison, bootstrap, minimum sample, verdict

Properties 12 (the bootstrap is a function of the data and the draws), 13 (identical resamples give the point interval), 14 (`ci` is well-formed), 15 (no verdict below the minimum sample) and 16 (the verdict is monotone in the evidence) of `docs/spec.md`, section 8, and the vectors V12-V14. Exact integer arithmetic; every conditional theorem has a non-vacuity witness over small literals. -/
namespace VbmForecast

/-- A refused check refuses the whole `do` block, whatever it returns. -/
theorem bindR_err {α : Type} (a : Except Refusal Unit) (b : Except Refusal α) (r : Refusal) (h : a = .error r) :
    (a >>= fun _ => b) = .error r := by
  subst h; rfl

/-- A passed check leaves the rest of the `do` block. -/
theorem bindR_ok {α : Type} (a : Except Refusal Unit) (b : Except Refusal α) (h : a = .ok ()) :
    (a >>= fun _ => b) = b := by
  subst h; rfl

/-! ## The differences -/

theorem pairedDiffs_ok (a b d : List Int) :
    pairedDiffs a b = .ok d ↔ a.length = b.length ∧ 0 < a.length ∧ d = List.zipWith (· - ·) a b := by
  unfold pairedDiffs
  by_cases h1 : a.length = b.length
  · rw [ite_f (Decidable.not_not.2 h1)]
    by_cases h2 : a.length = 0
    · rw [ite_t h2]
      constructor
      · intro h; cases h
      · rintro ⟨_, h, _⟩; omega
    · rw [ite_f h2]
      constructor
      · intro h; cases h; exact ⟨h1, by omega, rfl⟩
      · rintro ⟨_, _, rfl⟩; rfl
  · rw [ite_t h1]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact absurd h h1

theorem pairedDiffs_mismatch (a b : List Int) (h : a.length ≠ b.length) :
    pairedDiffs a b = .error (.lengthMismatch a.length b.length) := by
  unfold pairedDiffs; rw [ite_t h]

theorem pairedDiffs_empty : pairedDiffs [] [] = .error .empty := rfl

theorem pairedDiffs_length (a b d : List Int) (h : pairedDiffs a b = .ok d) : d.length = a.length := by
  obtain ⟨h1, _, rfl⟩ := (pairedDiffs_ok a b d).1 h
  simp [h1]

/-- A negative difference is a lower loss for A. -/
theorem pairedDiffs_neg (a b : List Int) (d : List Int) (h : pairedDiffs a b = .ok d) :
    ∀ i (hi : i < d.length), d[i] < 0 → ∃ (ha : i < a.length) (hb : i < b.length), a[i] < b[i] := by
  intro i hi hneg
  obtain ⟨h1, _, rfl⟩ := (pairedDiffs_ok a b d).1 h
  simp only [List.length_zipWith] at hi
  have hia : i < a.length := by omega
  have hib : i < b.length := by omega
  refine ⟨hia, hib, ?_⟩
  simp only [List.getElem_zipWith] at hneg
  omega

example : pairedDiffs [3, 1, 4] [1, 2, 4] = .ok [2, -1, 0] := by rfl
example : pairedDiffs [3, 1] [1] = .error (.lengthMismatch 2 1) := by rfl
example : (diffMean [2, -1, 3]).map (fun r => (r.num, r.den)) = .ok (4, 3) := rfl

theorem diffMean_ok (d : List Int) (r : Ratio) (h : diffMean d = .ok r) : r.num = diffSum d ∧ r.den = d.length := by
  unfold diffMean at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem diffMean_pos (d : List Int) (h : 0 < d.length) : ∃ r, diffMean d = .ok r := by
  unfold diffMean; simp [h]

/-! ## The bootstrap sums -/

theorem chunks_length (n : Nat) : ∀ (R : Nat) (ds : List Nat), (chunks n R ds).length = R
  | 0, _ => rfl
  | R + 1, ds => by simp [chunks, chunks_length n R]

theorem chunks_chunk_length (n : Nat) : ∀ (R : Nat) (ds : List Nat), ds.length = R * n →
    ∀ c ∈ chunks n R ds, c.length = n
  | 0, _, _ => by simp [chunks]
  | R + 1, ds, h => by
    intro c hc
    simp only [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [List.length_take]
      have : (R + 1) * n = R * n + n := by rw [Nat.succ_mul]
      omega
    · refine chunks_chunk_length n R _ ?_ c hc
      simp only [List.length_drop]
      have : (R + 1) * n = R * n + n := by rw [Nat.succ_mul]
      omega

theorem chunks_mem (n : Nat) : ∀ (R : Nat) (ds : List Nat), ∀ c ∈ chunks n R ds, ∀ x ∈ c, x ∈ ds
  | 0, _ => by simp [chunks]
  | R + 1, ds => by
    intro c hc x hx
    simp only [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop (chunks_mem n R _ c hc x hx)

theorem checkResamples_ok (lim : Limits) (R : Nat) :
    checkResamples lim R = .ok () ↔ 0 < R ∧ R ≤ lim.maxResamples := by
  unfold checkResamples
  by_cases h0 : R = 0
  · simp [h0]
  · by_cases h : lim.maxResamples < R
    · simp [h0, h]
    · simp [h0, h]; omega

theorem bootstrapSums_ok (lim : Limits) (d : List Int) (R : Nat) (draws : List Nat) (sums : List Int) :
    bootstrapSums lim d R draws = .ok sums ↔
      (0 < d.length ∧ d.length ≤ lim.maxEvents) ∧ (0 < R ∧ R ≤ lim.maxResamples) ∧
      draws.length = R * d.length ∧ (∀ x ∈ draws, x < d.length) ∧
      sums = (chunks d.length R draws).map (resampleSum d) := by
  unfold bootstrapSums
  simp only [bind_ok_iff, checkSample_ok, checkResamples_ok, checkAligned_ok, checkDraws_ok]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    have : (Except.ok sums : Except Refusal (List Int)) = .ok _ := h5.symm
    exact (Except.ok.inj this)
  · rintro ⟨h1, h2, h3, h4, rfl⟩
    exact ⟨h1, h2, h3, h4, rfl⟩

theorem bootstrapSums_length (lim : Limits) (d : List Int) (R : Nat) (draws : List Nat) (sums : List Int)
    (h : bootstrapSums lim d R draws = .ok sums) : sums.length = R := by
  obtain ⟨_, _, _, _, rfl⟩ := (bootstrapSums_ok lim d R draws sums).1 h
  simp [chunks_length]

theorem bootstrapSums_empty (lim : Limits) (R : Nat) (draws : List Nat) :
    bootstrapSums lim [] R draws = .error .empty := by
  unfold bootstrapSums
  simp only [List.length_nil]
  rw [bindR_err _ _ _ (checkSample_empty lim)]

theorem bootstrapSums_tooManyEvents (lim : Limits) (d : List Int) (R : Nat) (draws : List Nat)
    (h0 : 0 < d.length) (h : lim.maxEvents < d.length) :
    bootstrapSums lim d R draws = .error (.tooMany limitEvents d.length lim.maxEvents) := by
  unfold bootstrapSums
  rw [bindR_err _ _ _ (checkSample_tooMany lim _ h0 h)]

theorem bootstrapSums_tooManyResamples (lim : Limits) (d : List Int) (R : Nat) (draws : List Nat)
    (hs : 0 < d.length ∧ d.length ≤ lim.maxEvents) (h : lim.maxResamples < R) :
    bootstrapSums lim d R draws = .error (.tooMany limitResamples R lim.maxResamples) := by
  unfold bootstrapSums
  have hr : checkResamples lim R = .error (.tooMany limitResamples R lim.maxResamples) := by
    unfold checkResamples
    by_cases h0 : R = 0
    · omega
    · rw [ite_f h0, ite_t h]
  rw [bindR_ok _ _ ((checkSample_ok lim _).2 hs), bindR_err _ _ _ hr]

theorem bootstrapSums_mismatch (lim : Limits) (d : List Int) (R : Nat) (draws : List Nat)
    (hs : 0 < d.length ∧ d.length ≤ lim.maxEvents) (hr : 0 < R ∧ R ≤ lim.maxResamples)
    (h : draws.length ≠ R * d.length) :
    bootstrapSums lim d R draws = .error (.lengthMismatch draws.length (R * d.length)) := by
  unfold bootstrapSums
  rw [bindR_ok _ _ ((checkSample_ok lim _).2 hs), bindR_ok _ _ ((checkResamples_ok lim _).2 hr),
    bindR_err _ _ _ (checkAligned_refuses _ _ h)]

theorem bootstrapSums_badDraws (lim : Limits) (d : List Int) (R : Nat) (pre rest : List Nat) (x : Nat)
    (hs : 0 < d.length ∧ d.length ≤ lim.maxEvents) (hr : 0 < R ∧ R ≤ lim.maxResamples)
    (hl : (pre ++ x :: rest).length = R * d.length) (hpre : ∀ y ∈ pre, y < d.length) (hx : d.length ≤ x) :
    bootstrapSums lim d R (pre ++ x :: rest) = .error (.badDraws pre.length x) := by
  unfold bootstrapSums
  have hd : checkDraws d.length (pre ++ x :: rest) = .error (.badDraws pre.length x) := by
    have := checkDrawsFrom_refuses d.length pre rest x 0 hpre hx
    simpa [checkDraws] using this
  rw [bindR_ok _ _ ((checkSample_ok lim _).2 hs), bindR_ok _ _ ((checkResamples_ok lim _).2 hr),
    bindR_ok _ _ ((checkAligned_ok _ _).2 hl), bindR_err _ _ _ hd]

/-! ### Property 12: a function of the data and the draws -/

theorem resampleSum_congr (d d' : List Int) (idx : List Nat) (h : ∀ i ∈ idx, d.getD i 0 = d'.getD i 0) :
    resampleSum d idx = resampleSum d' idx := by
  unfold resampleSum
  congr 1
  exact List.map_congr_left h

/-- Equal inputs, equal outputs: no hidden state and no clock. -/
theorem bootstrapSums_deterministic (lim : Limits) (d d' : List Int) (R R' : Nat) (draws draws' : List Nat)
    (h1 : d = d') (h2 : R = R') (h3 : draws = draws') :
    bootstrapSums lim d R draws = bootstrapSums lim d' R' draws' := by
  subst h1 h2 h3; rfl

/-- The result depends on `d` only through its length and its values at the drawn indices. -/
theorem bootstrapSums_congr (lim : Limits) (d d' : List Int) (R : Nat) (draws : List Nat)
    (hlen : d.length = d'.length) (h : ∀ i ∈ draws, d.getD i 0 = d'.getD i 0) :
    bootstrapSums lim d R draws = bootstrapSums lim d' R draws := by
  have hmap : (chunks d.length R draws).map (resampleSum d) = (chunks d.length R draws).map (resampleSum d') :=
    List.map_congr_left fun c hc => resampleSum_congr d d' c fun i hi => h i (chunks_mem _ _ _ c hc i hi)
  unfold bootstrapSums
  rw [← hlen, hmap]

/-- With an adapter `gen seed n R`, the sums are a function of `(d, seed)`. -/
theorem bootstrapSums_of_seed (lim : Limits) (gen : Nat → Nat → Nat → List Nat) (d : List Int) (R seed seed' : Nat)
    (h : seed = seed') : bootstrapSums lim d R (gen seed d.length R) = bootstrapSums lim d R (gen seed' d.length R) := by
  subst h; rfl

def v12d : List Int := [2, -1, 3]
def v12draws : List Nat := [0, 0, 0, 1, 1, 1, 2, 2, 2, 0, 1, 2]

/-- V12, the sums. -/
example : bootstrapSums witLim v12d 4 v12draws = .ok [6, -3, 9, 4] := by rfl
/-- Run twice: the same. -/
example : bootstrapSums witLim v12d 4 v12draws = bootstrapSums witLim v12d 4 v12draws := rfl
/-- The two data lists differ at index 1, which no draw touches: the sums agree. -/
example : bootstrapSums witLim [2, 0, 3] 3 [0, 0, 0, 2, 2, 2, 0, 2, 0] = bootstrapSums witLim [2, 9, 3] 3 [0, 0, 0, 2, 2, 2, 0, 2, 0] :=
  bootstrapSums_congr witLim _ _ 3 _ rfl (by decide)
example : bootstrapSums witLim v12d 4 [0, 0, 0] = .error (.lengthMismatch 3 12) := by rfl
example : bootstrapSums witLim v12d 4 [0, 0, 0, 1, 1, 1, 2, 2, 3, 0, 1, 2] = .error (.badDraws 8 3) := by rfl
example : bootstrapSums witLim v12d 101 [] = .error (.tooMany limitResamples 101 100) := by rfl
example : bootstrapSums witLim [] 4 [] = .error .empty := by rfl

/-! ## `ci` -/

theorem sortInts_perm (xs : List Int) : (sortInts xs).Perm xs := List.mergeSort_perm _ _

theorem sortInts_length (xs : List Int) : (sortInts xs).length = xs.length := (sortInts_perm xs).length_eq

theorem sortInts_mem (xs : List Int) (x : Int) : x ∈ sortInts xs ↔ x ∈ xs := (sortInts_perm xs).mem_iff

theorem sortInts_sorted (xs : List Int) : (sortInts xs).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
  exact this.imp (by intro a b h; simpa using h)

/-- The lower index. -/
def ciK (B t s : Nat) : Nat := B * t / s

theorem ciK_lt (B t s : Nat) (hB : 0 < B) (ht : 2 * t < s) : ciK B t s < B := by
  unfold ciK
  have hs : 0 < s := by omega
  rw [Nat.div_lt_iff_lt_mul hs]
  exact Nat.mul_lt_mul_of_pos_left (by omega) hB

/-- `k ≤ B - 1 - k`: the interval is never crossed. -/
theorem ciK_le (B t s : Nat) (ht : 2 * t < s) : 2 * ciK B t s < B ∨ B = 0 := by
  unfold ciK
  by_cases hB : B = 0
  · exact Or.inr hB
  · left
    have hs : 0 < s := by omega
    have h1 : B * t / s * s ≤ B * t := Nat.div_mul_le_self _ _
    have h2 : 0 < B := by omega
    have h3 : 2 * (B * t / s) * s < B * s := by
      have : 2 * (B * t / s) * s = 2 * (B * t / s * s) := by rw [Nat.mul_assoc]
      have h4 : B * (2 * t) < B * s := Nat.mul_lt_mul_of_pos_left ht h2
      rw [this]; have : B * (2 * t) = 2 * (B * t) := by rw [← Nat.mul_assoc, Nat.mul_comm B 2, Nat.mul_assoc]
      omega
    exact Nat.lt_of_mul_lt_mul_right h3

theorem ci_ok (sums : List Int) (n t s : Nat) (L U : Ratio) :
    ci sums n t s = .ok (L, U) ↔ (0 < t ∧ 2 * t < s) ∧ 0 < sums.length ∧ 0 < n ∧ L.den = n ∧ U.den = n ∧
      L.num = (sortInts sums).getD (ciK sums.length t s) 0 ∧
      U.num = (sortInts sums).getD (sums.length - 1 - ciK sums.length t s) 0 := by
  unfold ci ciK
  by_cases h1 : 0 < t ∧ 2 * t < s
  · by_cases h2 : sums.length = 0
    · simp [h1, h2]
    · by_cases h3 : 0 < n
      · rw [ite_f (by simpa using h1), ite_f h2, dite_eq_left_of_eq_true (eq_true h3)]
        constructor
        · intro h
          have h' := Except.ok.inj h
          cases h'
          exact ⟨h1, by omega, h3, rfl, rfl, rfl, rfl⟩
        · rintro ⟨_, _, _, hL, hU, hn, hm⟩
          obtain ⟨Ln, Ld, Lp⟩ := L
          obtain ⟨Un, Ud, Up⟩ := U
          simp only at hL hU hn hm
          subst hL hU hn hm
          rfl
      · have : n = 0 := by omega
        subst this
        simp [h1, h2]
  · simp [h1]

theorem ci_badLevel (sums : List Int) (n t s : Nat) (h : ¬ (0 < t ∧ 2 * t < s)) :
    ci sums n t s = .error (.badLevel t s) := by
  unfold ci; rw [ite_t h]

theorem ci_empty (n t s : Nat) (h : 0 < t ∧ 2 * t < s) : ci [] n t s = .error .empty := by
  unfold ci; rw [ite_f (by simpa using h)]; rfl

/-! ### Property 14: `ci` is well-formed -/

theorem sorted_getD_le (l : List Int) (hl : l.Pairwise (· ≤ ·)) (i j : Nat) (hij : i ≤ j) (hj : j < l.length) :
    l.getD i 0 ≤ l.getD j 0 := by
  have hi : i < l.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Int.le_refl _
  · exact List.pairwise_iff_getElem.1 hl i j hi hj hlt

theorem getD_mem (l : List Int) (i : Nat) (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi

/-- The interval is made of two order statistics: both are resample sums, and the lower is at most the upper. -/
theorem ci_wellFormed (sums : List Int) (n t s : Nat) (L U : Ratio) (h : ci sums n t s = .ok (L, U)) :
    (sortInts sums).Perm sums ∧ (sortInts sums).Pairwise (· ≤ ·) ∧ L.num ∈ sums ∧ U.num ∈ sums ∧ L.num ≤ U.num ∧
    L.le U ∧ L.den = n ∧ U.den = n ∧
    ∀ lo hi : Int, (∀ z ∈ sums, lo ≤ z ∧ z ≤ hi) → lo ≤ L.num ∧ L.num ≤ hi ∧ lo ≤ U.num ∧ U.num ≤ hi := by
  obtain ⟨ht, hB, hn, hL, hU, hLn, hUn⟩ := (ci_ok sums n t s L U).1 h
  have hk := ciK_lt sums.length t s hB ht.2
  have hk2 := ciK_le sums.length t s ht.2
  have hlen := sortInts_length sums
  have hLm : L.num ∈ sums := by
    rw [hLn]; exact (sortInts_mem _ _).1 (getD_mem _ _ (by omega))
  have hUm : U.num ∈ sums := by
    rw [hUn]; exact (sortInts_mem _ _).1 (getD_mem _ _ (by omega))
  have hle : L.num ≤ U.num := by
    rw [hLn, hUn]; exact sorted_getD_le _ (sortInts_sorted sums) _ _ (by omega) (by omega)
  refine ⟨sortInts_perm sums, sortInts_sorted sums, hLm, hUm, hle, ?_, hL, hU, ?_⟩
  · unfold Ratio.le; rw [hL, hU]; exact Int.mul_le_mul_of_nonneg_right hle (Int.natCast_nonneg _)
  · intro lo hi hb
    exact ⟨(hb _ hLm).1, (hb _ hLm).2, (hb _ hUm).1, (hb _ hUm).2⟩

/-- `mergeSort` recurses by a well-founded measure, which no evaluator unfolds: a sorted permutation is unique, so the vector is proved by that. -/
theorem sortInts_eq (xs ys : List Int) (hp : ys.Perm xs) (hs : ys.Pairwise (· ≤ ·)) : sortInts xs = ys :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Int.le_antisymm h1 h2) (sortInts_sorted xs) hs ((sortInts_perm xs).trans hp.symm)

/-- V12: sorted. -/
theorem sortInts_v12 : sortInts [6, -3, 9, 4] = [-3, 4, 6, 9] :=
  sortInts_eq _ _ (by decide) (by decide)
theorem sortInts_const6 : sortInts [6, 6] = [6, 6] := sortInts_eq _ _ (List.Perm.refl _) (by decide)
example : ci [6, -3, 9, 4] 3 2 10 = .ok (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩) := by
  unfold ci; simp [sortInts_v12]
/-- The observed mean `4/3` lies inside `(-3/3, 9/3)`. -/
example : (Ratio.mk (-3) 3 (by decide)).le ⟨4, 3, by decide⟩ ∧ (Ratio.mk 4 3 (by decide)).le ⟨9, 3, by decide⟩ := by
  decide +kernel
example : (ci [] 3 2 10).map (fun c => c.1.num) = .error .empty := by rfl
example : (ci [1] 3 5 10).map (fun c => c.1.num) = .error (.badLevel 5 10) := by rfl
example : 2 * ciK 4 2 10 < 4 := by decide +kernel

/-! ### Property 13: identical resamples give the point interval -/

theorem getD_const (l : List Int) (x : Int) (h : ∀ y ∈ l, y = x) (i : Nat) (hi : i < l.length) : l.getD i 0 = x :=
  h _ (getD_mem l i hi)

/-- If every resample sum equals `x`, then `ci = (x/n, x/n)`. -/
theorem ci_const (sums : List Int) (x : Int) (n t s : Nat) (hsums : ∀ y ∈ sums, y = x)
    (ht : 0 < t ∧ 2 * t < s) (hB : 0 < sums.length) (hn : 0 < n) :
    ∃ L U : Ratio, ci sums n t s = .ok (L, U) ∧ L.num = x ∧ U.num = x ∧ L.den = n ∧ U.den = n := by
  have hk := ciK_lt sums.length t s hB ht.2
  have hk2 := ciK_le sums.length t s ht.2
  have hlen := sortInts_length sums
  have hall : ∀ y ∈ sortInts sums, y = x := fun y hy => hsums y ((sortInts_mem _ _).1 hy)
  refine ⟨⟨x, n, hn⟩, ⟨x, n, hn⟩, ?_, rfl, rfl, rfl, rfl⟩
  rw [ci_ok]
  refine ⟨ht, hB, hn, rfl, rfl, ?_, ?_⟩
  · exact (getD_const _ x hall _ (by omega)).symm
  · exact (getD_const _ x hall _ (by omega)).symm

theorem resampleSum_const (d : List Int) (c : Int) (idx : List Nat) (h : ∀ i ∈ idx, d.getD i 0 = c) :
    resampleSum d idx = (idx.length : Int) * c := by
  unfold resampleSum
  induction idx with
  | nil => simp [sumInt]
  | cons i is ih =>
    have h1 := h i (List.mem_cons_self ..)
    have h2 := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [List.map_cons, sumInt, List.length_cons, h1, h2]
    have e : ((is.length + 1 : Nat) : Int) = (is.length : Int) + 1 := by omega
    rw [e, Int.add_mul, Int.one_mul]; omega

theorem getD_replicate (n : Nat) (c : Int) (i : Nat) (h : i < n) : (List.replicate n c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]; simp

theorem sumInt_replicate (n : Nat) (c : Int) : sumInt (List.replicate n c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [List.replicate_succ, sumInt, ih]
    have e : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [e, Int.add_mul, Int.one_mul]; omega

/-- All differences equal `c`: every resample sum is `n*c`. -/
theorem bootstrapSums_const (lim : Limits) (n : Nat) (c : Int) (R : Nat) (draws : List Nat)
    (sums : List Int) (h : bootstrapSums lim (List.replicate n c) R draws = .ok sums) :
    ∀ y ∈ sums, y = (n : Int) * c := by
  obtain ⟨_, _, hl, hd, rfl⟩ := (bootstrapSums_ok _ _ _ _ _).1 h
  simp only [List.length_replicate] at hl hd
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨ch, hch, rfl⟩ := hy
  have hlen := chunks_chunk_length n R draws hl ch (by simpa using hch)
  rw [resampleSum_const _ c ch (fun i hi => getD_replicate n c i (hd i (chunks_mem _ _ _ ch (by simpa using hch) i hi)))]
  rw [hlen]

/-- If all differences equal `c`, the interval is `[c, c]` (as `n*c / n`) and contains the observed mean. -/
theorem bootstrap_const_contains (lim : Limits) (n : Nat) (c : Int) (R : Nat) (draws : List Nat) (t s : Nat)
    (sums : List Int) (hb : bootstrapSums lim (List.replicate n c) R draws = .ok sums) (ht : 0 < t ∧ 2 * t < s) :
    ∃ L U m : Ratio, ci sums n t s = .ok (L, U) ∧ diffMean (List.replicate n c) = .ok m ∧
      L.eqv ⟨c, 1, by decide⟩ ∧ U.eqv ⟨c, 1, by decide⟩ ∧ L.le m ∧ m.le U := by
  obtain ⟨⟨h0, _⟩, ⟨hR, _⟩, _⟩ := (bootstrapSums_ok _ _ _ _ _).1 hb
  simp only [List.length_replicate] at h0
  have hlen := bootstrapSums_length _ _ _ _ _ hb
  obtain ⟨L, U, hci, hL, hU, hLd, hUd⟩ :=
    ci_const sums ((n : Int) * c) n t s (bootstrapSums_const lim n c R draws sums hb) ht (by omega) h0
  have hm : diffMean (List.replicate n c) = .ok ⟨(n : Int) * c, n, h0⟩ := by
    unfold diffMean
    simp [h0, diffSum, sumInt_replicate]
  refine ⟨L, U, ⟨(n : Int) * c, n, h0⟩, hci, hm, ?_, ?_, ?_, ?_⟩
  · unfold Ratio.eqv; rw [hL, hLd]; simp [Int.mul_comm]
  · unfold Ratio.eqv; rw [hU, hUd]; simp [Int.mul_comm]
  · unfold Ratio.le; rw [hL, hLd]; exact Int.le_refl _
  · unfold Ratio.le; rw [hU, hUd]; exact Int.le_refl _

/-- Witness: `d = [2,2,2]`, valid draws. -/
example : bootstrapSums witLim (List.replicate 3 2) 2 [0, 1, 2, 2, 2, 1] = .ok [6, 6] := by rfl
example : ci [6, 6] 3 2 10 = .ok (⟨6, 3, by decide⟩, ⟨6, 3, by decide⟩) := by
  unfold ci; simp [sortInts_const6]

/-! ## The verdict -/

/-- Property 15: below the minimum sample, `refused`, whatever the interval and the sum. -/
theorem verdict_refused (lim : Limits) (n : Nat) (obsSum : Int) (c : Ratio × Ratio) (h : n < lim.minEvents) :
    verdict lim n obsSum c = .refused n lim.minEvents := by
  unfold verdict; rw [ite_t h]

/-- And through the whole comparison: whatever the draws, the sample too small is refused (no interval). -/
theorem compare_refused (lim : Limits) (s t R : Nat) (a b d : List Int) (draws : List Nat)
    (hd : pairedDiffs a b = .ok d) (h : d.length < lim.minEvents) :
    ∃ m, compareForecasters lim s t R a b draws = .ok (.refused d.length lim.minEvents, m, none) := by
  have hpos : 0 < d.length := by
    obtain ⟨h1, h2, rfl⟩ := (pairedDiffs_ok a b d).1 hd
    simpa [h1] using h2
  obtain ⟨m, hm⟩ := diffMean_pos d hpos
  refine ⟨m, ?_⟩
  unfold compareForecasters
  rw [hd]
  simp only [hm]
  rw [ite_t h]

theorem compare_pairedDiffs_error (lim : Limits) (s t R : Nat) (a b : List Int) (draws : List Nat) (r : Refusal)
    (h : pairedDiffs a b = .error r) : compareForecasters lim s t R a b draws = .error r := by
  unfold compareForecasters; rw [h]

example : verdict { witLim with minEvents := 30 } 3 4 (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩) = .refused 3 30 := by rfl
example : verdict { witLim with minEvents := 30 } 3 (-12) (⟨-9, 3, by decide⟩, ⟨-3, 3, by decide⟩) = .refused 3 30 := by rfl

/-! ### Property 16: monotone in the evidence -/

/-- `I ⊆ J` as intervals over one denominator (compared through the numerators). -/
def Nested (I J : Ratio × Ratio) : Prop := J.1.num ≤ I.1.num ∧ I.2.num ≤ J.2.num

/-- (a) A tighter interval cannot lose a conclusion. -/
theorem verdict_nested (lim : Limits) (n : Nat) (obsSum : Int) (I J : Ratio × Ratio) (hN : Nested I J)
    (hJ : verdict lim n obsSum J = .better ∨ verdict lim n obsSum J = .worse) :
    verdict lim n obsSum I = verdict lim n obsSum J := by
  obtain ⟨h1, h2⟩ := hN
  unfold verdict at *
  by_cases hn : n < lim.minEvents
  · simp [hn] at hJ
  · simp only [hn, ite_false] at *
    by_cases hb : J.2.num < 0 ∧ obsSum < 0
    · have hb' : I.2.num < 0 ∧ obsSum < 0 := ⟨by omega, hb.2⟩
      rw [ite_t hb, ite_t hb']
    · rw [ite_f hb] at hJ ⊢
      by_cases hw : 0 < J.1.num ∧ 0 < obsSum
      · have hw' : 0 < I.1.num ∧ 0 < obsSum := ⟨by omega, hw.2⟩
        have hb' : ¬ (I.2.num < 0 ∧ obsSum < 0) := by omega
        rw [ite_f hb', ite_t hw', ite_t hw]
      · rw [ite_f hw] at hJ; simp at hJ

theorem verdict_minEvents (lim : Limits) (m : Nat) (n : Nat) (obsSum : Int) (c : Ratio × Ratio) (hm : lim.minEvents ≤ m) :
    verdict { lim with minEvents := m } n obsSum c = verdict lim n obsSum c ∨
      verdict { lim with minEvents := m } n obsSum c = .refused n m := by
  unfold verdict
  by_cases h : n < lim.minEvents
  · right; simp only; rw [ite_t (by omega)]
  · by_cases h2 : n < m
    · right; simp only; rw [ite_t h2]
    · left; simp only; rw [ite_f h, ite_f h2]

/-- (b) Raising the minimum never turns `better` into `worse` or back. -/
theorem verdict_minEvents_sign (lim : Limits) (m : Nat) (n : Nat) (obsSum : Int) (c : Ratio × Ratio) (hm : lim.minEvents ≤ m) :
    (verdict lim n obsSum c = .better → verdict { lim with minEvents := m } n obsSum c ≠ .worse) ∧
    (verdict lim n obsSum c = .worse → verdict { lim with minEvents := m } n obsSum c ≠ .better) := by
  rcases verdict_minEvents lim m n obsSum c hm with h | h <;> rw [h] <;> constructor <;> intro h1 <;> simp [h1]

/-- (c) The conclusions and their evidence. -/
theorem verdict_better_iff (lim : Limits) (n : Nat) (obsSum : Int) (c : Ratio × Ratio) :
    verdict lim n obsSum c = .better ↔ lim.minEvents ≤ n ∧ c.2.num < 0 ∧ obsSum < 0 := by
  unfold verdict
  by_cases h1 : n < lim.minEvents
  · simp [h1] <;> omega
  · by_cases h2 : c.2.num < 0 ∧ obsSum < 0
    · simp [h1, h2] <;> omega
    · rw [ite_f h1, ite_f h2]
      by_cases h3 : 0 < c.1.num ∧ 0 < obsSum <;> simp [h3] <;> omega

theorem verdict_worse_iff (lim : Limits) (n : Nat) (obsSum : Int) (c : Ratio × Ratio) :
    verdict lim n obsSum c = .worse ↔ lim.minEvents ≤ n ∧ ¬ (c.2.num < 0 ∧ obsSum < 0) ∧ 0 < c.1.num ∧ 0 < obsSum := by
  unfold verdict
  by_cases h1 : n < lim.minEvents
  · simp [h1] <;> omega
  · by_cases h2 : c.2.num < 0 ∧ obsSum < 0
    · simp [h1, h2] <;> omega
    · rw [ite_f h1, ite_f h2]
      by_cases h3 : 0 < c.1.num ∧ 0 < obsSum <;> simp [h3] <;> omega

/-- `better` and `worse` are never both: a conclusion carries the sign of its evidence. -/
theorem verdict_better_ne_worse (lim : Limits) (n : Nat) (obsSum : Int) (c : Ratio × Ratio) :
    verdict lim n obsSum c = .better → verdict lim n obsSum c ≠ .worse := by
  intro h h'; rw [h] at h'; cases h'

/-- Both at once would need `L > 0` and `U < 0`: impossible for an interval that is not crossed. -/
theorem not_better_and_worse_evidence (c : Ratio × Ratio) (h : c.1.num ≤ c.2.num) :
    ¬ ((c.2.num < 0 ∧ 0 < c.1.num)) := by omega

/-- Witness (a): `n = 40`, `obsSum = -12`, `J = (-5,-1) ⊇ I = (-4,-2)`, both `better`. -/
example : verdict { witLim with minEvents := 30 } 40 (-12) (⟨-4, 40, by decide⟩, ⟨-2, 40, by decide⟩) = .better := by rfl
example : verdict { witLim with minEvents := 30 } 40 (-12) (⟨-5, 40, by decide⟩, ⟨-1, 40, by decide⟩) = .better := by rfl
example : Nested (⟨-4, 40, by decide⟩, ⟨-2, 40, by decide⟩) (⟨-5, 40, by decide⟩, ⟨-1, 40, by decide⟩) := by
  unfold Nested; decide
/-- Witness (b): raising `minEvents` from 30 to 50 refuses. -/
example : verdict { witLim with minEvents := 50 } 40 (-12) (⟨-4, 40, by decide⟩, ⟨-2, 40, by decide⟩) = .refused 40 50 := by rfl
/-- Witness (c): a `worse`. -/
example : verdict { witLim with minEvents := 30 } 40 12 (⟨2, 40, by decide⟩, ⟨4, 40, by decide⟩) = .worse := by rfl
/-- V14: `minEvents = 3`, `obsSum = 4`, interval `(-3/3, 9/3)`: `inconclusive`. -/
example : verdict witLim 3 4 (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩) = .inconclusive := by rfl

/-! ## `compareForecasters` end to end (V12-V14) -/

theorem ci_v12 : ci [6, -3, 9, 4] 3 2 10 = .ok (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩) := by
  unfold ci; simp [sortInts_v12]

theorem bootstrap_v12 : bootstrapSums witLim [2, -1, 3] 4 v12draws = .ok [6, -3, 9, 4] := by rfl

/-- V12 and V14 end to end: differences `[2,-1,3]`, `minEvents = 3`, `obsSum = 4`, interval `(-3, 9)`: `inconclusive`. -/
example : compareForecasters witLim 10 2 4 [3, 1, 4] [1, 2, 1] v12draws =
    .ok (.inconclusive, ⟨4, 3, by decide⟩, some (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩)) := by
  have hp : pairedDiffs [3, 1, 4] [1, 2, 1] = .ok [2, -1, 3] := by rfl
  have hm : diffMean [2, -1, 3] = .ok ⟨4, 3, by decide⟩ := by rfl
  unfold compareForecasters
  rw [hp]
  simp only [hm]
  rw [ite_f (by decide), bootstrap_v12]
  simp only [List.length_cons, List.length_nil]
  rw [ci_v12]
  rfl
example : (compareForecasters { witLim with minEvents := 30 } 10 2 4 [3, 1, 4] [1, 2, 1] []).map
    (fun r => (r.1, r.2.1.num, r.2.1.den, r.2.2.map fun c => (c.1.num, c.2.num))) =
    .ok (.refused 3 30, 4, 3, none) := by rfl

end VbmForecast
