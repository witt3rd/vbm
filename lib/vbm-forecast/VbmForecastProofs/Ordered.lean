import VbmForecast.Ordered
import VbmForecastProofs.Brier
/-! # S3 proofs: ordered rules

Properties 4 and 5 (the totals of RPS, pinball and interval), 8 (RPS is the sum of binary Brier scores of its threshold events; the interval score is twice the sum of two pinball scores) and 9 (an `level/s`-quantile minimises the expected pinball over a finite distribution), and the vectors V5-V7. Exact integer arithmetic; each conditional theorem has a non-vacuity witness over small literals. -/
namespace VbmForecast

/-! ## Property 4: additive over events -/

theorem rpsTotal_append (s : Scale) (xs ys : List OrderedEvent) : rpsTotal s (xs ++ ys) = rpsTotal s xs + rpsTotal s ys := by
  unfold rpsTotal; rw [List.map_append, sumInt_append]

theorem pinballTotal_append (s : Scale) (xs ys : List QuantileEvent) :
    pinballTotal s (xs ++ ys) = pinballTotal s xs + pinballTotal s ys := by
  unfold pinballTotal; rw [List.map_append, sumInt_append]

theorem intervalTotal_append (s : Scale) (xs ys : List IntervalEvent) :
    intervalTotal s (xs ++ ys) = intervalTotal s xs + intervalTotal s ys := by
  unfold intervalTotal; rw [List.map_append, sumInt_append]

/-- A cons adds the score of its head. -/
theorem rpsTotal_cons (s : Scale) (e : OrderedEvent) (es : List OrderedEvent) : rpsTotal s (e :: es) = rps s e + rpsTotal s es := rfl

theorem pinballTotal_cons (s : Scale) (e : QuantileEvent) (es : List QuantileEvent) :
    pinballTotal s (e :: es) = pinball s e + pinballTotal s es := rfl

theorem intervalTotal_cons (s : Scale) (e : IntervalEvent) (es : List IntervalEvent) :
    intervalTotal s (e :: es) = intervalScore s e + intervalTotal s es := rfl

-- Witness (`s = 10`): the RPS of V5 is 29 and a second event adds its own score; pinball and interval totals added by hand.
example : rpsTotal 10 [⟨[1, 2, 3], [5, 3, 2], 2⟩, ⟨[1, 2, 3], [5, 3, 2], 3⟩] = 29 + 89 := by decide
example : rpsTotal 10 ([⟨[1, 2, 3], [5, 3, 2], 2⟩] ++ [⟨[1, 2, 3], [5, 3, 2], 3⟩]) = rpsTotal 10 [⟨[1, 2, 3], [5, 3, 2], 2⟩] + rpsTotal 10 [⟨[1, 2, 3], [5, 3, 2], 3⟩] := by decide
example : pinballTotal 10 [⟨9, 5, 8⟩, ⟨9, 5, 3⟩] = 27 + 2 := by decide
example : intervalTotal 10 [⟨1, 2, 6, 9⟩, ⟨1, 2, 6, 4⟩] = 68 + 8 := by decide

/-! ## Property 5: permutation invariance -/

theorem rpsTotal_perm (s : Scale) {xs ys : List OrderedEvent} (h : xs.Perm ys) : rpsTotal s xs = rpsTotal s ys := by
  unfold rpsTotal; exact sumInt_perm (h.map _)

theorem pinballTotal_perm (s : Scale) {xs ys : List QuantileEvent} (h : xs.Perm ys) : pinballTotal s xs = pinballTotal s ys := by
  unfold pinballTotal; exact sumInt_perm (h.map _)

theorem intervalTotal_perm (s : Scale) {xs ys : List IntervalEvent} (h : xs.Perm ys) : intervalTotal s xs = intervalTotal s ys := by
  unfold intervalTotal; exact sumInt_perm (h.map _)

-- Witness: `[a, b] ~ [b, a]` with distinct scores (`29` and `25`; `27` and `2`; `68` and `8`).
example : [OrderedEvent.mk [1, 2, 3] [5, 3, 2] 2, ⟨[1, 2, 3], [5, 3, 2], 3⟩].Perm [⟨[1, 2, 3], [5, 3, 2], 3⟩, ⟨[1, 2, 3], [5, 3, 2], 2⟩] :=
  List.Perm.swap _ _ []
example : rps 10 ⟨[1, 2, 3], [5, 3, 2], 2⟩ ≠ rps 10 ⟨[1, 2, 3], [5, 3, 2], 3⟩ := by decide
example : pinballTotal 10 [⟨9, 5, 8⟩, ⟨9, 5, 3⟩] = pinballTotal 10 [⟨9, 5, 3⟩, ⟨9, 5, 8⟩] := by decide
example : pinball 10 ⟨9, 5, 8⟩ ≠ pinball 10 ⟨9, 5, 3⟩ := by decide
example : intervalTotal 10 [⟨1, 2, 6, 9⟩, ⟨1, 2, 6, 4⟩] = intervalTotal 10 [⟨1, 2, 6, 4⟩, ⟨1, 2, 6, 9⟩] := by decide
example : intervalScore 10 ⟨1, 2, 6, 9⟩ ≠ intervalScore 10 ⟨1, 2, 6, 4⟩ := by decide

/-! ## Property 8: RPS is a sum of binary Brier scores; interval is twice two pinballs -/

/-- RPS is the sum of the binary Brier scores of its threshold events `obs ≤ vals_j`, forecast `F_j`. -/
theorem rps_eq_sum_brier (s : Scale) (e : OrderedEvent) : rps s e = sumInt ((rpsEvents e).map (brierBinary s)) := rfl

/-- The same, for the totals. -/
theorem rpsTotal_eq_sum_brier (s : Scale) (es : List OrderedEvent) :
    rpsTotal s es = sumInt (es.map fun e => sumInt ((rpsEvents e).map (brierBinary s))) := rfl

/-- Every threshold event of an ordered event is one of `m - 1` binary events, each hit exactly when `obs ≤ vals_j`. -/
theorem rpsEvents_hit (e : OrderedEvent) (b : BinaryEvent) (hb : b ∈ rpsEvents e) :
    ∃ v F, (v, F) ∈ rpsThr e.vals e.ps ∧ b = ⟨F, decide (e.obs ≤ v)⟩ := by
  unfold rpsEvents at hb
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
  exact ⟨t.1, t.2, ht, rfl⟩

/-- The interval score is twice the sum of the pinball scores of its two ends: level `t` at `lo`, level `s - t` at `hi`. -/
theorem intervalScore_eq_pinball (s : Scale) (e : IntervalEvent) (ht : 2 * e.tail < s) (hc : e.lo ≤ e.hi) :
    intervalScore s e = 2 * (pinball s ⟨e.tail, e.lo, e.obs⟩ + pinball s ⟨s - e.tail, e.hi, e.obs⟩) := by
  unfold intervalScore pinball
  have h1 : ((s - e.tail : Nat) : Int) = (s : Int) - (e.tail : Int) := by omega
  simp only [h1]
  have hs : (0 : Int) ≤ e.tail := Int.natCast_nonneg _
  split <;> split <;> split <;> grind

-- Witnesses (`s = 10`): V5, and the interval identity of V7 on its inputs.
example : sumInt ((rpsEvents ⟨[1, 2, 3], [5, 3, 2], 2⟩).map (brierBinary 10)) = 29 := by decide
example : (rpsEvents ⟨[1, 2, 3], [5, 3, 2], 2⟩).map (fun b => (b.p, b.hit)) = [(5, false), (8, true)] := by decide
example : 2 * 1 < 10 ∧ 2 ≤ 6 ∧ intervalScore 10 ⟨1, 2, 6, 9⟩ = 2 * (pinball 10 ⟨1, 2, 9⟩ + pinball 10 ⟨9, 6, 9⟩) := by decide

/-! ## Property 9: a quantile minimises the expected pinball -/

/-- The mass of the true distribution strictly below `r`. -/
def massBelow (vals qs : List Int) (r : Int) : Int := sumInt ((vals.zip qs).map fun vq => if vq.1 < r then vq.2 else 0)

/-- The mass of the true distribution at or below `r`. -/
def massAtMost (vals qs : List Int) (r : Int) : Int := sumInt ((vals.zip qs).map fun vq => if vq.1 ≤ r then vq.2 else 0)

/-- `r` is a `level/s`-quantile of the distribution: `P(X < r) ≤ level/s ≤ P(X ≤ r)`, in units of `1/s`. -/
def IsQuantile (level : Nat) (vals qs : List Int) (r : Int) : Prop :=
  massBelow vals qs r ≤ (level : Int) ∧ (level : Int) ≤ massAtMost vals qs r

instance (level : Nat) (vals qs : List Int) (r : Int) : Decidable (IsQuantile level vals qs r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The supporting line of the pinball loss at `r` with the slope `s*c - level`, `c` the indicator of the observation being below `r` (`c = 1`) or above it (`c = 0`), either at `r`: the loss at any `r'` lies above the line. -/
theorem pinball_support (s level : Nat) (hl : level ≤ s) (r r' x c : Int) (hc : c = 0 ∨ c = 1)
    (h1 : x < r → c = 1) (h2 : r < x → c = 0) :
    pinball s ⟨level, r, x⟩ + (r' - r) * ((s : Int) * c - level) ≤ pinball s ⟨level, r', x⟩ := by
  obtain ⟨b, rfl⟩ : ∃ b, s = level + b := ⟨s - level, by omega⟩
  have ha : (0 : Int) ≤ level := Int.natCast_nonneg _
  have hb : (0 : Int) ≤ b := Int.natCast_nonneg _
  unfold pinball
  simp only
  push_cast
  rcases hc with rfl | rfl <;> split <;> split <;> first
    | (exfalso; omega)
    | skip
  all_goals
    try have q1 := Int.mul_nonneg ha (show 0 ≤ x - r' by omega)
    try have q2 := Int.mul_nonneg hb (show 0 ≤ x - r' by omega)
    try have q3 := Int.mul_nonneg ha (show 0 ≤ r' - x by omega)
    try have q4 := Int.mul_nonneg hb (show 0 ≤ r' - x by omega)
    try have q5 := Int.mul_nonneg ha (show 0 ≤ r - r' by omega)
    try have q6 := Int.mul_nonneg hb (show 0 ≤ r - r' by omega)
    try have q7 := Int.mul_nonneg ha (show 0 ≤ r' - r by omega)
    try have q8 := Int.mul_nonneg hb (show 0 ≤ r' - r by omega)
    try have q9 := Int.mul_nonneg ha (show 0 ≤ x - r by omega)
    try have q10 := Int.mul_nonneg hb (show 0 ≤ r - x by omega)
    try have q11 := Int.mul_nonneg hb (show 0 ≤ x - r by omega)
    try have q12 := Int.mul_nonneg ha (show 0 ≤ r - x by omega)
    grind

/-- Weighted supporting lines: the expected pinball at `r'` lies above the expected pinball at `r` plus `(r' - r) * (s * Σ q·c - level * Σ q)`. -/
theorem expPinball_support (s level : Nat) (hl : level ≤ s) (r r' : Int) (c : Int → Int) (hc : ∀ x, c x = 0 ∨ c x = 1)
    (h1 : ∀ x, x < r → c x = 1) (h2 : ∀ x, r < x → c x = 0) :
    ∀ L : List (Int × Int), (∀ vq ∈ L, 0 ≤ vq.2) →
      sumInt (L.map fun vq => vq.2 * pinball s ⟨level, r, vq.1⟩) +
          (r' - r) * ((s : Int) * sumInt (L.map fun vq => vq.2 * c vq.1) - level * sumInt (L.map fun vq => vq.2))
        ≤ sumInt (L.map fun vq => vq.2 * pinball s ⟨level, r', vq.1⟩) := by
  intro L
  induction L with
  | nil => intro _; simp [sumInt]
  | cons vq L ih =>
    intro hq
    have hq0 := hq vq (by simp)
    have ih' := ih (fun y hy => hq y (by simp [hy]))
    have hp := pinball_support s level hl r r' vq.1 (c vq.1) (hc vq.1) (h1 vq.1) (h2 vq.1)
    have := Int.mul_le_mul_of_nonneg_left hp hq0
    simp only [List.map_cons, sumInt]
    grind

/-- The sum of the masses of the paired list is the sum of `qs` when the lists are aligned. -/
theorem sumInt_zip_snd (vals qs : List Int) (h : vals.length = qs.length) : sumInt ((vals.zip qs).map fun vq => vq.2) = sumInt qs := by
  induction vals generalizing qs with
  | nil => cases qs <;> simp_all [sumInt]
  | cons v vals ih => cases qs with
    | nil => simp at h
    | cons q qs => simp only [List.zip_cons_cons, List.map_cons, sumInt, ih qs (by simpa using h)]

theorem zip_snd_nonneg (vals qs : List Int) (h : ∀ q ∈ qs, 0 ≤ q) : ∀ vq ∈ vals.zip qs, 0 ≤ vq.2 := fun _ hvq => h _ (List.of_mem_zip hvq).2

/-- **Pinball properness**: for a finite distribution `(vals, qs)` (aligned, nonnegative masses summing to `s`) and `level ≤ s`, a `level/s`-quantile `r` minimises the expected pinball over every report `r'`. -/
theorem expPinball_quantile_le (s level : Nat) (hl : level ≤ s) (vals qs : List Int) (hlen : vals.length = qs.length)
    (hq : ∀ q ∈ qs, 0 ≤ q) (hsum : sumInt qs = (s : Int)) (r : Int) (hr : IsQuantile level vals qs r) (r' : Int) :
    expPinball s level vals qs r ≤ expPinball s level vals qs r' := by
  obtain ⟨hlo, hhi⟩ := hr
  have hnn := zip_snd_nonneg vals qs hq
  have hs := sumInt_zip_snd vals qs hlen
  unfold expPinball
  by_cases hrr : r ≤ r'
  · have key := expPinball_support s level hl r r' (fun x => if x ≤ r then 1 else 0) (fun x => by by_cases h : x ≤ r <;> simp [h])
      (fun x hx => by simp [Int.le_of_lt hx]) (fun x hx => by simp [Int.not_le.2 hx]) (vals.zip qs) hnn
    have e : sumInt ((vals.zip qs).map fun vq => vq.2 * (if vq.1 ≤ r then (1 : Int) else 0)) = massAtMost vals qs r := by
      unfold massAtMost; congr 1; apply List.map_congr_left; intro vq _; by_cases h : vq.1 ≤ r <;> simp [h]
    simp only [e, hs, hsum] at key
    have : 0 ≤ (r' - r) * ((s : Int) * massAtMost vals qs r - level * s) := by
      apply Int.mul_nonneg (by omega)
      have := Int.mul_le_mul_of_nonneg_left hhi (Int.natCast_nonneg s)
      grind
    omega
  · have key := expPinball_support s level hl r r' (fun x => if x < r then 1 else 0) (fun x => by by_cases h : x < r <;> simp [h])
      (fun x hx => by simp [hx]) (fun x hx => by simp [Int.not_lt.2 (Int.le_of_lt hx)]) (vals.zip qs) hnn
    have e : sumInt ((vals.zip qs).map fun vq => vq.2 * (if vq.1 < r then (1 : Int) else 0)) = massBelow vals qs r := by
      unfold massBelow; congr 1; apply List.map_congr_left; intro vq _; by_cases h : vq.1 < r <;> simp [h]
    simp only [e, hs, hsum] at key
    have : 0 ≤ (r - r') * ((level : Int) * s - (s : Int) * massBelow vals qs r) := by
      apply Int.mul_nonneg (by omega)
      have := Int.mul_le_mul_of_nonneg_left hlo (Int.natCast_nonneg s)
      grind
    have e2 : (r' - r) * ((s : Int) * massBelow vals qs r - level * s) = (r - r') * ((level : Int) * s - (s : Int) * massBelow vals qs r) := by grind
    omega

-- Witness (`s = 10`, level 9, masses `(3, 3, 4)` on `{1, 2, 3}`): `3` is a 9/10-quantile (`6 ≤ 9 ≤ 10`), `2` is not (`6 < 9`), and `3` does minimise: expected pinball `9` against `39` at `2`.
example : sumInt [3, 3, 4] = ((10 : Nat) : Int) ∧ (∀ q ∈ [3, 3, (4 : Int)], 0 ≤ q) ∧ [1, 2, 3].length = [3, 3, 4].length := by decide +kernel
example : IsQuantile 9 [1, 2, 3] [3, 3, 4] 3 := by decide
example : ¬ IsQuantile 9 [1, 2, 3] [3, 3, 4] 2 := by decide
example : expPinball 10 9 [1, 2, 3] [3, 3, 4] 3 = 9 := by decide
example : expPinball 10 9 [1, 2, 3] [3, 3, 4] 2 = 39 := by decide
example : expPinball 10 9 [1, 2, 3] [3, 3, 4] 3 ≤ expPinball 10 9 [1, 2, 3] [3, 3, 4] 2 := by decide

/-! ## The validated entry points -/

theorem rpsV_ok (s : Scale) (lim : Limits) (e : OrderedEvent) (v : Int) :
    rpsV s lim e = .ok v ↔ validateOrdered s lim e = .ok () ∧ v = rps s e := by
  unfold rpsV
  rw [bind_ok_iff]
  simp only [pure, Except.pure, Except.ok.injEq]
  grind

theorem pinballV_ok (s : Scale) (e : QuantileEvent) (v : Int) :
    pinballV s e = .ok v ↔ (0 < s ∧ 0 < e.level ∧ e.level < s) ∧ v = pinball s e := by
  unfold pinballV
  rw [bind_ok_iff, validateQuantile_ok]
  simp only [pure, Except.pure, Except.ok.injEq]
  grind

theorem intervalScoreV_ok (s : Scale) (e : IntervalEvent) (v : Int) :
    intervalScoreV s e = .ok v ↔ (0 < s ∧ (0 < e.tail ∧ 2 * e.tail < s) ∧ e.lo ≤ e.hi) ∧ v = intervalScore s e := by
  unfold intervalScoreV
  rw [bind_ok_iff, validateInterval_ok]
  simp only [pure, Except.pure, Except.ok.injEq]
  grind

example : rpsV 10 witLim ⟨[1, 2, 3], [5, 3, 2], 2⟩ = .ok 29 := rfl
example : rpsV 10 witLim ⟨[1, 2, 3], [5, 3, 1], 2⟩ = .error (.notNormalised 9) := rfl
example : pinballV 10 ⟨9, 5, 8⟩ = .ok 27 := rfl
example : pinballV 10 ⟨10, 5, 8⟩ = .error (.badLevel 10 10) := rfl
example : intervalScoreV 10 ⟨1, 2, 6, 9⟩ = .ok 68 := rfl
example : intervalScoreV 10 ⟨1, 6, 2, 9⟩ = .error (.crossedInterval 6 2) := rfl

/-! ## Vectors V5-V7 -/

example : rps 10 ⟨[1, 2, 3], [5, 3, 2], 2⟩ = 25 + 4 := by decide                         -- V5
example : rps 10 ⟨[1, 2, 3], [5, 3, 2], 2⟩ = 29 := by decide                             -- V5
example : pinball 10 ⟨9, 5, 8⟩ = 9 * 3 := by decide                                      -- V6
example : pinball 10 ⟨9, 5, 3⟩ = 1 * 2 := by decide                                      -- V6
example : pinball 10 ⟨9, 5, 8⟩ = 27 ∧ pinball 10 ⟨9, 5, 3⟩ = 2 := by decide              -- V6
example : intervalScore 10 ⟨1, 2, 6, 9⟩ = 2 * 1 * 4 + 2 * 10 * 3 := by decide            -- V7
example : intervalScore 10 ⟨1, 2, 6, 9⟩ = 68 := by decide                                -- V7
example : pinball 10 ⟨1, 2, 9⟩ = 7 ∧ pinball 10 ⟨9, 6, 9⟩ = 27 := by decide              -- V7
example : intervalScore 10 ⟨1, 2, 6, 9⟩ = 2 * (7 + 27) := by decide                      -- V7

end VbmForecast
