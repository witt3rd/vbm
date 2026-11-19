import VbmForecast.LogScore
import VbmForecastProofs.Rep
/-! # S4 proofs: the logarithmic score

Property 10 (the exact comparison: antisymmetric, transitive, and consistent with the enclosures), property 11 (`log2Enclosure` is sound and has width at most 2) and the vector V8. `Log2Lower` and `Log2Upper` are the exact power relations of `docs/spec.md`, section 3.2. -/
namespace VbmForecast

/-! ## Property 10: the exact comparison -/

theorem natProd_append (xs ys : List Nat) : natProd (xs ++ ys) = natProd xs * natProd ys := by
  induction xs with
  | nil => simp [natProd]
  | cons x xs ih => simp only [List.cons_append, natProd, ih, Nat.mul_assoc]

theorem natProd_perm {xs ys : List Nat} (h : xs.Perm ys) : natProd xs = natProd ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [natProd, ih]
  | swap x y l => simp only [natProd, Nat.mul_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- `logCompare` is `compare` on the products. -/
theorem logCompare_eq (as bs : List Nat) : logCompare as bs = compare (natProd as) (natProd bs) := rfl

theorem logCompare_antisymm (as bs : List Nat) : logCompare as bs = (logCompare bs as).swap := by
  unfold logCompare; rw [Nat.compare_swap]

theorem logCompare_gt_iff (as bs : List Nat) : logCompare as bs = .gt ↔ natProd bs < natProd as := by
  unfold logCompare; rw [Nat.compare_eq_gt]

theorem logCompare_gt_swap (as bs : List Nat) : logCompare as bs = .gt ↔ logCompare bs as = .lt := by
  rw [logCompare_antisymm]; cases logCompare bs as <;> simp

theorem logCompare_trans {as bs cs : List Nat} (h1 : logCompare as bs = .gt) (h2 : logCompare bs cs = .gt) : logCompare as cs = .gt := by
  rw [logCompare_gt_iff] at *; exact Nat.lt_trans h2 h1

theorem logCompare_perm {as as' bs bs' : List Nat} (ha : as.Perm as') (hb : bs.Perm bs') : logCompare as bs = logCompare as' bs' := by
  unfold logCompare; rw [natProd_perm ha, natProd_perm hb]

theorem logCompare_append (as bs as' bs' : List Nat) :
    logCompare (as ++ as') (bs ++ bs') = compare (natProd as * natProd as') (natProd bs * natProd bs') := by
  unfold logCompare; rw [natProd_append, natProd_append]

-- Witness (V8): realised probabilities (5,8) against (6,4) at `s = 10`: products 40 and 24, A is better; and the converse is lt.
example : natProd [5, 8] = 40 ∧ natProd [6, 4] = 24 := by decide
example : logCompare [5, 8] [6, 4] = .gt := by decide
example : logCompare [6, 4] [5, 8] = .lt := by decide
example : logCompare [5, 8] [8, 5] = .eq := by decide
example : logCompare [0, 8] [0, 4] = .eq := by decide
example : logCompare [5, 8] [0, 4] = .gt := by decide
example : logCompare [3, 2] [5, 4] = .lt ∧ logCompare [5, 4] [7, 1] = .gt ∧ logCompare [3, 2] [7, 1] = .lt := by decide

theorem logCompareV_ok (lim : Limits) (as bs : List Nat) (o : Ordering) :
    logCompareV lim as bs = .ok o ↔ as.length = bs.length ∧ 0 < as.length ∧ as.length ≤ lim.maxEvents ∧ o = logCompare as bs := by
  unfold logCompareV
  rw [bind_ok_iff, bind_ok_iff, checkAligned_ok, checkSample_ok]
  simp only [pure, Except.pure, Except.ok.injEq]
  grind

theorem logCompareV_lengthMismatch (lim : Limits) (as bs : List Nat) (h : as.length ≠ bs.length) :
    logCompareV lim as bs = .error (.lengthMismatch as.length bs.length) := by
  unfold logCompareV; rw [checkAligned_refuses _ _ h]; rfl

theorem logCompareV_empty (lim : Limits) : logCompareV lim [] [] = .error .empty := by
  unfold logCompareV; simp [checkAligned, checkSample]; rfl

example : logCompareV witLim [5, 8] [6, 4] = .ok .gt := rfl
example : logCompareV witLim [5, 8] [6] = .error (.lengthMismatch 2 1) := rfl

/-- The minimum-sample rule comes first, whatever the lists are. -/
theorem logVerdict_refused (lim : Limits) (as bs : List Nat) (h : as.length < lim.minEvents) :
    logVerdict lim as bs = .ok (.refused as.length lim.minEvents) := by
  unfold logVerdict; simp [h]

theorem logVerdict_decided (lim : Limits) (as bs : List Nat) (o : Ordering) (h : ¬ as.length < lim.minEvents) :
    logVerdict lim as bs = .ok (.decided o) ↔ logCompareV lim as bs = .ok o := by
  unfold logVerdict; simp only [h, ↓reduceIte]
  cases hc : logCompareV lim as bs with
  | error e => simp [bind, Except.bind]
  | ok v => simp [bind, Except.bind, pure, Except.pure]

example : logVerdict { witLim with minEvents := 3 } [5, 8] [6, 4] = .ok (.refused 2 3) := rfl
example : logVerdict { witLim with minEvents := 2 } [5, 8] [6, 4] = .ok (.decided .gt) := rfl
example : logVerdict { witLim with minEvents := 2 } [5, 8] [6, 4, 1] = .error (.lengthMismatch 2 3) := rfl

/-! ## Property 11: the enclosure is sound and has width at most 2 -/

/-- The error step of one squaring: `(t + E)^2 ≤ c m (t' + 6 E)` when `t^2 < c m (t' + 1)`. -/
theorem sq_err (c m t t' E : Nat) (hc : c = 1 ∨ c = 2) (ht : t < 2 * m) (hE : 1 ≤ E) (hEm : E ≤ m)
    (hq : t * t < c * m * (t' + 1)) : (t + E) * (t + E) ≤ c * m * (t' + 6 * E) := by
  have h1 : t * E ≤ 2 * m * E := Nat.mul_le_mul_right E (Nat.le_of_lt ht)
  have h2 : E * E ≤ m * E := Nat.mul_le_mul_right E hEm
  have h3 : m * 1 ≤ m * E := Nat.mul_le_mul_left m hE
  have e1 : (t + E) * (t + E) = t * t + 2 * (t * E) + E * E := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm E t]; omega
  have e2 : 2 * m * E = 2 * (m * E) := Nat.mul_assoc 2 m E
  have e3 : m * (6 * E) = 6 * (m * E) := by rw [Nat.mul_left_comm]
  have e4 : 2 * m * (6 * E) = 12 * (m * E) := by rw [Nat.mul_assoc, e3]; omega
  rw [Nat.mul_add] at hq
  rcases hc with rfl | rfl
  · rw [e1, Nat.mul_add, Nat.one_mul, e3]; simp only [Nat.one_mul, Nat.mul_one] at *; omega
  · rw [e1, Nat.mul_add, e4]; simp only [Nat.mul_one] at *; omega

theorem step_lower (c m t t' B A P : Nat) (hm : 0 < m) (ht' : t' * (c * m) ≤ t * t) (h : t * B * A ≤ m * P) :
    t' * (c * (B * B)) * (A * A) ≤ m * (P * P) := by
  have h1 : (t * B * A) * (t * B * A) ≤ (m * P) * (m * P) := Nat.mul_le_mul h h
  have h2 : m * (t' * (c * (B * B)) * (A * A)) ≤ m * (m * (P * P)) := by
    calc m * (t' * (c * (B * B)) * (A * A)) = (t' * (c * m)) * (B * B * (A * A)) := by ac_rfl
      _ ≤ (t * t) * (B * B * (A * A)) := Nat.mul_le_mul_right _ ht'
      _ = (t * B * A) * (t * B * A) := by ac_rfl
      _ ≤ (m * P) * (m * P) := h1
      _ = m * (m * (P * P)) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left h2 hm

theorem step_upper (c m t t' E B A P : Nat) (hm : 0 < m) (hn : (t + E) * (t + E) ≤ c * m * (t' + 6 * E))
    (h : m * P ≤ B * (t + E) * A) : m * (P * P) ≤ c * (B * B) * (t' + 6 * E) * (A * A) := by
  have h1 : (m * P) * (m * P) ≤ (B * (t + E) * A) * (B * (t + E) * A) := Nat.mul_le_mul h h
  have h2 : m * (m * (P * P)) ≤ m * (c * (B * B) * (t' + 6 * E) * (A * A)) := by
    calc m * (m * (P * P)) = (m * P) * (m * P) := by ac_rfl
      _ ≤ (B * (t + E) * A) * (B * (t + E) * A) := h1
      _ = ((t + E) * (t + E)) * (B * B * (A * A)) := by ac_rfl
      _ ≤ (c * m * (t' + 6 * E)) * (B * B * (A * A)) := Nat.mul_le_mul_right _ hn
      _ = m * (c * (B * B) * (t' + 6 * E) * (A * A)) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left h2 hm

theorem pow_two_succ (a j : Nat) : a ^ (2 ^ (j + 1)) = a ^ (2 ^ j) * a ^ (2 ^ j) := by
  rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]

/-- The invariant of the mantissa after `j` squarings: in `[m, 2m)`, at or below the truth, and above it by at most `6^j` units. -/
def LogInv (m p den j : Nat) (r : LogState) : Prop :=
  m ≤ r.t ∧ r.t < 2 * m ∧ r.t * 2 ^ r.b * den ^ (2 ^ j) ≤ m * p ^ (2 ^ j) ∧
    m * p ^ (2 ^ j) ≤ 2 ^ r.b * (r.t + 6 ^ j) * den ^ (2 ^ j)

theorem logInv_step (c m p den j b b' t t' : Nat) (hc : c = 1 ∨ c = 2) (hm : 0 < m) (hE : 6 ^ j ≤ m)
    (ht' : t' = t * t / (c * m)) (hB : 2 ^ b' = c * (2 ^ b * 2 ^ b)) (hlo : c * m * m ≤ t * t) (hhi : t * t < 2 * m * (c * m))
    (h : LogInv m p den j ⟨b, t⟩) : LogInv m p den (j + 1) ⟨b', t'⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  have hcm : 0 < c * m := by rcases hc with rfl | rfl <;> omega
  have hE1 : 1 ≤ 6 ^ j := Nat.one_le_pow _ _ (by omega)
  have hq : t * t < c * m * (t' + 1) := by rw [ht']; exact Nat.lt_mul_div_succ _ hcm
  have hq2 : t' * (c * m) ≤ t * t := by rw [ht']; exact Nat.div_mul_le_self _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · show m ≤ t'; rw [ht']; exact (Nat.le_div_iff_mul_le hcm).2 (by rw [Nat.mul_comm]; exact hlo)
  · show t' < 2 * m; rw [ht']; exact (Nat.div_lt_iff_lt_mul hcm).2 (by rw [Nat.mul_comm]; exact hhi)
  · show t' * 2 ^ b' * den ^ (2 ^ (j + 1)) ≤ m * p ^ (2 ^ (j + 1))
    rw [pow_two_succ den, pow_two_succ p, hB]
    exact step_lower c m t t' (2 ^ b) (den ^ 2 ^ j) (p ^ 2 ^ j) hm hq2 h3
  · show m * p ^ (2 ^ (j + 1)) ≤ 2 ^ b' * (t' + 6 ^ (j + 1)) * den ^ (2 ^ (j + 1))
    rw [pow_two_succ den, pow_two_succ p, hB, Nat.pow_succ, Nat.mul_comm (6 ^ j) 6]
    exact step_upper c m t t' (6 ^ j) (2 ^ b) (den ^ 2 ^ j) (p ^ 2 ^ j) hm (sq_err c m t t' _ hc h2 hE1 hE hq) h4

theorem two_pow_double (b : Nat) : 2 ^ (2 * b) = 2 ^ b * 2 ^ b := by
  rw [← Nat.pow_add]; congr 1; omega

theorem logStep_inv (m p den j : Nat) (hm : 0 < m) (hE : 6 ^ j ≤ m) (r : LogState) (h : LogInv m p den j r) :
    LogInv m p den (j + 1) (logStep m r) := by
  have h1 := h.1
  have h2 := h.2.1
  have hmm : m * m ≤ r.t * r.t := Nat.mul_le_mul h1 h1
  have hmm2 : r.t * r.t < 2 * m * (2 * m) := Nat.mul_lt_mul_of_lt_of_le h2 (Nat.le_of_lt h2) (by omega)
  unfold logStep
  by_cases hc : 2 * m * m ≤ r.t * r.t
  · simp only [hc, ↓reduceIte]
    refine logInv_step 2 m p den j _ _ r.t _ (by omega) hm hE rfl ?_ hc ?_ h
    · rw [Nat.pow_succ, two_pow_double, Nat.mul_comm]
    · exact hmm2
  · simp only [hc, ↓reduceIte]
    refine logInv_step 1 m p den j _ _ r.t _ (by omega) hm hE (by simp) ?_ ?_ ?_ h
    · rw [two_pow_double, Nat.one_mul]
    · simpa using hmm
    · have := Nat.lt_of_not_ge hc
      rw [Nat.one_mul, Nat.mul_assoc]; rw [Nat.mul_assoc] at this; exact this

theorem logRun_inv (m p den : Nat) (hm : 0 < m) (hden : 0 < den) (hp1 : den ≤ p) (hp2 : p < 2 * den) (J : Nat) (hJ : 6 ^ J ≤ m) :
    ∀ j, j ≤ J → LogInv m p den j (logRun m j ⟨0, m * p / den⟩) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Nat.le_div_iff_mul_le hden).2 (Nat.mul_le_mul_left m hp1)
    · exact (Nat.div_lt_iff_lt_mul hden).2 (by
        have := Nat.mul_lt_mul_of_pos_left hp2 hm
        rw [Nat.mul_left_comm, ← Nat.mul_assoc] at this; exact this)
    · show m * p / den * 2 ^ 0 * den ^ (2 ^ 0) ≤ m * p ^ (2 ^ 0)
      simp only [Nat.pow_zero, Nat.pow_one, Nat.mul_one]
      exact Nat.div_mul_le_self _ _
    · show m * p ^ (2 ^ 0) ≤ 2 ^ 0 * (m * p / den + 6 ^ 0) * den ^ (2 ^ 0)
      simp only [Nat.pow_zero, Nat.pow_one, Nat.one_mul]
      have := Nat.lt_mul_div_succ (m * p) hden
      rw [Nat.mul_comm den] at this; exact Nat.le_of_lt this
  | succ j ih =>
    intro hj
    exact logStep_inv m p den j hm (Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) hJ) _ (ih (by omega))

/-! ### From the invariant to the enclosure relations -/

theorem lower_of (a kn D Nn : Nat) (h : 2 ^ a * D ≤ 2 ^ kn * Nn) :
    2 ^ ((a : Int) - (kn : Int)).toNat * D ≤ 2 ^ (-((a : Int) - (kn : Int))).toNat * Nn := by
  by_cases hk : kn ≤ a
  · have e1 : ((a : Int) - (kn : Int)).toNat = a - kn := by omega
    have e2 : (-((a : Int) - (kn : Int))).toNat = 0 := by omega
    rw [e1, e2, Nat.pow_zero, Nat.one_mul]
    have e3 : 2 ^ a = 2 ^ kn * 2 ^ (a - kn) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e3, Nat.mul_assoc] at h
    exact Nat.le_of_mul_le_mul_left h (Nat.two_pow_pos kn)
  · have e1 : ((a : Int) - (kn : Int)).toNat = 0 := by omega
    have e2 : (-((a : Int) - (kn : Int))).toNat = kn - a := by omega
    rw [e1, e2, Nat.pow_zero, Nat.one_mul]
    have e3 : 2 ^ kn = 2 ^ a * 2 ^ (kn - a) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e3, Nat.mul_assoc] at h
    exact Nat.le_of_mul_le_mul_left h (Nat.two_pow_pos a)

theorem upper_of (a kn D Nn : Nat) (h : Nn * 2 ^ kn ≤ 2 ^ a * D) :
    Nn * 2 ^ (-((a : Int) - (kn : Int))).toNat ≤ 2 ^ ((a : Int) - (kn : Int)).toNat * D := by
  by_cases hk : kn ≤ a
  · have e1 : ((a : Int) - (kn : Int)).toNat = a - kn := by omega
    have e2 : (-((a : Int) - (kn : Int))).toNat = 0 := by omega
    rw [e1, e2, Nat.pow_zero, Nat.mul_one]
    have e3 : 2 ^ a = 2 ^ kn * 2 ^ (a - kn) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e3, Nat.mul_assoc, Nat.mul_comm Nn] at h
    exact Nat.le_of_mul_le_mul_left h (Nat.two_pow_pos kn)
  · have e1 : ((a : Int) - (kn : Int)).toNat = 0 := by omega
    have e2 : (-((a : Int) - (kn : Int))).toNat = kn - a := by omega
    rw [e1, e2, Nat.pow_zero, Nat.one_mul]
    have e3 : 2 ^ kn = 2 ^ a * 2 ^ (kn - a) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e3, ← Nat.mul_assoc, Nat.mul_comm Nn, Nat.mul_assoc] at h
    exact Nat.le_of_mul_le_mul_left h (Nat.two_pow_pos a)

theorem redK_spec (den : Nat) : ∀ f num, 0 < num → num < 2 * den → den ≤ num * 2 ^ f →
    den ≤ num * 2 ^ redK den num f ∧ num * 2 ^ redK den num f < 2 * den := by
  intro f
  induction f with
  | zero => intro num _ h2 h3; simp only [redK, Nat.pow_zero, Nat.mul_one] at *; exact ⟨h3, h2⟩
  | succ f ih =>
    intro num h1 h2 h3
    unfold redK
    by_cases hd : den ≤ num
    · simp only [hd, ↓reduceIte, Nat.pow_zero, Nat.mul_one, true_and]; exact h2
    · simp only [hd, ↓reduceIte]
      have h3' : den ≤ 2 * num * 2 ^ f := by
        have : num * 2 ^ (f + 1) = 2 * num * 2 ^ f := by rw [Nat.pow_succ]; ac_rfl
        omega
      obtain ⟨a, b⟩ := ih (2 * num) (by omega) (by omega) h3'
      have e : num * 2 ^ (redK den (2 * num) f + 1) = 2 * num * 2 ^ redK den (2 * num) f := by rw [Nat.pow_succ]; ac_rfl
      rw [e]
      exact ⟨a, b⟩

theorem pow_mul_pow (num k F : Nat) : (num * 2 ^ k) ^ (2 ^ F) = num ^ (2 ^ F) * 2 ^ (k * 2 ^ F) := by
  rw [Nat.mul_pow, ← Nat.pow_mul]

theorem two_pow_F_le (F : Nat) : 6 ^ F ≤ 2 ^ logWidth F := by
  unfold logWidth
  have : 2 ^ (3 * F + 4) = 16 * 8 ^ F := by
    rw [Nat.pow_add, Nat.pow_mul, Nat.mul_comm]
  rw [this]
  have : 6 ^ F ≤ 8 ^ F := Nat.pow_le_pow_left (by omega) F
  omega

/-- The core of the enclosure (the case `p ≠ den`, `den < p < 2 den`): the general soundness of `(lo, hi)`. -/
theorem enclosure_core (num den F : Nat) (p k : Nat) (hp : p = num * 2 ^ k) (hden : 0 < den) (h1 : den < p) (h2 : p < 2 * den) :
    let m := 2 ^ logWidth F
    let r := logRun m F ⟨0, m * p / den⟩
    let kn : Nat := k * 2 ^ F
    Log2Lower num den F ((r.b : Int) - (kn : Int)) ∧
    Log2Upper num den F ((r.b : Int) + (if r.t + 6 ^ F ≤ 2 * m then 1 else 2) - (kn : Int)) := by
  intro m r kn
  have hm : 0 < m := Nat.two_pow_pos _
  have hinv : LogInv m p den F r := logRun_inv m p den hm hden (Nat.le_of_lt h1) h2 F (two_pow_F_le F) F (Nat.le_refl _)
  obtain ⟨i1, i2, i3, i4⟩ := hinv
  have hP : p ^ (2 ^ F) = num ^ (2 ^ F) * 2 ^ kn := by rw [hp]; exact pow_mul_pow num k F
  have hE : 6 ^ F ≤ m := two_pow_F_le F
  constructor
  · apply lower_of
    have : m * (2 ^ r.b * den ^ 2 ^ F) ≤ m * (p ^ 2 ^ F) := by
      calc m * (2 ^ r.b * den ^ 2 ^ F) = m * 2 ^ r.b * den ^ 2 ^ F := by ac_rfl
        _ ≤ r.t * 2 ^ r.b * den ^ 2 ^ F := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ i1)
        _ ≤ m * p ^ 2 ^ F := i3
    have := Nat.le_of_mul_le_mul_left this hm
    rw [hP] at this; rw [Nat.mul_comm (2 ^ kn)]; exact this
  · by_cases hc : r.t + 6 ^ F ≤ 2 * m
    · simp only [hc, ↓reduceIte]
      have e : (r.b : Int) + 1 - (kn : Int) = ((r.b + 1 : Nat) : Int) - (kn : Int) := by push_cast; rfl
      rw [e]; apply upper_of
      have : m * p ^ 2 ^ F ≤ m * (2 ^ (r.b + 1) * den ^ 2 ^ F) := by
        calc m * p ^ 2 ^ F ≤ 2 ^ r.b * (r.t + 6 ^ F) * den ^ 2 ^ F := i4
          _ ≤ 2 ^ r.b * (2 * m) * den ^ 2 ^ F := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc)
          _ = m * (2 ^ (r.b + 1) * den ^ 2 ^ F) := by rw [Nat.pow_succ]; ac_rfl
      have := Nat.le_of_mul_le_mul_left this hm
      rw [hP] at this; exact this
    · simp only [hc, ↓reduceIte]
      have e : (r.b : Int) + 2 - (kn : Int) = ((r.b + 2 : Nat) : Int) - (kn : Int) := by push_cast; rfl
      rw [e]; apply upper_of
      have : m * p ^ 2 ^ F ≤ m * (2 ^ (r.b + 2) * den ^ 2 ^ F) := by
        calc m * p ^ 2 ^ F ≤ 2 ^ r.b * (r.t + 6 ^ F) * den ^ 2 ^ F := i4
          _ ≤ 2 ^ r.b * (4 * m) * den ^ 2 ^ F := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
          _ = m * (2 ^ (r.b + 2) * den ^ 2 ^ F) := by rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 from rfl]; ac_rfl
      have := Nat.le_of_mul_le_mul_left this hm
      rw [hP] at this; exact this

/-- Soundness and width, for every successful enclosure. -/
theorem log2Enclosure_sound (num den F : Nat) (lo hi : Int) (h : log2Enclosure num den F = .ok (lo, hi)) :
    Log2Lower num den F lo ∧ Log2Upper num den F hi ∧ lo ≤ hi ∧ hi - lo ≤ 2 := by
  unfold log2Enclosure at h
  by_cases h0 : den = 0
  · simp [h0] at h
  by_cases h1 : den < num
  · simp [h0, h1] at h
  by_cases h2 : num = 0
  · simp [h0, h2] at h
  simp only [h0, h1, h2, ↓reduceIte] at h
  have hden : 0 < den := Nat.pos_of_ne_zero h0
  have hnum : 0 < num := Nat.pos_of_ne_zero h2
  have hle : num ≤ den := by omega
  have hspec := redK_spec den den num hnum (by omega) (by
    have : den < 2 ^ den := Nat.lt_two_pow_self
    calc den ≤ 1 * 2 ^ den := by omega
      _ ≤ num * 2 ^ den := Nat.mul_le_mul_right _ hnum)
  generalize hk : redK den num den = k at h hspec
  obtain ⟨hs1, hs2⟩ := hspec
  by_cases hp : num * 2 ^ k = den
  · simp only [hp, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hP : den ^ (2 ^ F) = num ^ (2 ^ F) * 2 ^ (k * 2 ^ F) := by rw [← hp]; exact pow_mul_pow num k F
    have e3 : ((-((k * 2 ^ F : Nat) : Int))).toNat = 0 := by omega
    have e4 : ((-(-((k * 2 ^ F : Nat) : Int)))).toNat = k * 2 ^ F := by omega
    refine ⟨?_, ?_, by omega, by omega⟩
    · unfold Log2Lower; rw [e3, e4, Nat.pow_zero, Nat.one_mul, hP, Nat.mul_comm]; exact Nat.le_refl _
    · unfold Log2Upper; rw [e4, e3, Nat.pow_zero, Nat.one_mul, hP]; exact Nat.le_refl _
  · simp only [hp, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlt : den < num * 2 ^ k := by omega
    obtain ⟨c1, c2⟩ := enclosure_core num den F (num * 2 ^ k) k rfl hden hlt hs2
    refine ⟨c1, ?_, ?_, ?_⟩
    · exact c2
    · split <;> omega
    · split <;> omega

theorem log2Enclosure_total (num den F : Nat) (h0 : 0 < num) (h1 : num ≤ den) : ∃ lo hi, log2Enclosure num den F = .ok (lo, hi) := by
  unfold log2Enclosure
  have : den ≠ 0 := by omega
  have : ¬ den < num := by omega
  have : num ≠ 0 := by omega
  simp only [*, ↓reduceIte]
  split <;> exact ⟨_, _, rfl⟩

theorem log2Enclosure_badScale (num F : Nat) : log2Enclosure num 0 F = .error .badScale := by
  simp [log2Enclosure]

theorem log2Enclosure_zero (den F : Nat) (h : 0 < den) : log2Enclosure 0 den F = .error .zeroProbability := by
  have : den ≠ 0 := by omega
  simp [log2Enclosure, this]

theorem log2Enclosure_over (num den F : Nat) (h : den < num) (h0 : 0 < den) :
    log2Enclosure num den F = .error (.probOutOfRange 0 (num : Int)) := by
  have : den ≠ 0 := by omega
  simp [log2Enclosure, this, h]

/-- The named limit `F ≤ logBits`, then the enclosure: sound with width at most 2 for every `0 < num ≤ den`, `F ≤ logBits`. -/
theorem log2EnclosureV_sound (lim : Limits) (num den F : Nat) (lo hi : Int) (h : log2EnclosureV lim num den F = .ok (lo, hi)) :
    F ≤ lim.logBits ∧ Log2Lower num den F lo ∧ Log2Upper num den F hi ∧ hi - lo ≤ 2 := by
  unfold log2EnclosureV at h
  by_cases hl : lim.logBits < F
  · simp [hl] at h
  · simp only [hl, ↓reduceIte] at h
    obtain ⟨a, b, _, d⟩ := log2Enclosure_sound num den F lo hi h
    exact ⟨by omega, a, b, d⟩

theorem log2EnclosureV_limit (lim : Limits) (num den F : Nat) (h : lim.logBits < F) :
    log2EnclosureV lim num den F = .error (.tooMany limitLogBits F lim.logBits) := by
  unfold log2EnclosureV; simp [h]

-- Witnesses (V8): `x = 1/2` encloses `-2^F` (exactly), `x = 1` gives `(0, 0)`, and a proper fraction gets a width of 1 or 2.
theorem log2Enclosure_half (F : Nat) : log2Enclosure 1 2 F = .ok (-(2 ^ F : Int), -(2 ^ F : Int)) := by
  have : redK 2 1 2 = 1 := rfl
  simp [log2Enclosure, this]

theorem log2Enclosure_one (den F : Nat) (h : 0 < den) : log2Enclosure den den F = .ok (0, 0) := by
  have : den ≠ 0 := by omega
  have hk : redK den den den = 0 := by
    cases den with
    | zero => omega
    | succ n => simp [redK]
  simp [log2Enclosure, this, hk]

example : log2Enclosure 1 2 3 = .ok (-8, -8) := rfl
example : log2Enclosure 1 1 3 = .ok (0, 0) := rfl
example : log2Enclosure 3 4 3 = .ok (-4, -3) := rfl
example : log2Enclosure 0 4 3 = .error .zeroProbability := rfl
example : log2Enclosure 5 4 3 = .error (.probOutOfRange 0 5) := rfl
example : log2EnclosureV witLim 1 2 9 = .error (.tooMany limitLogBits 9 8) := rfl
example : log2EnclosureV witLim 1 3 3 = .ok (-13, -12) := rfl

/-! ## Property 10, continued: the comparison and the enclosures agree -/

/-- A larger numerator over the same denominator only raises a lower bound. -/
theorem Log2Lower_mono {P Q D F : Nat} (h : P ≤ Q) {t : Int} (hl : Log2Lower P D F t) : Log2Lower Q D F t := by
  unfold Log2Lower at *
  exact Nat.le_trans hl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _))

theorem Log2Upper_mono {P Q D F : Nat} (h : P ≤ Q) {t : Int} (hu : Log2Upper Q D F t) : Log2Upper P D F t := by
  unfold Log2Upper at *
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h _)) hu

/-- If `logCompare as bs` is not `lt`, every lower bound of B's realised-outcome product is one of A's, and every upper bound of A's is one of B's. -/
theorem logCompare_enclosure (as bs : List Nat) (D F : Nat) (h : logCompare as bs ≠ .lt) :
    (∀ t, Log2Lower (natProd bs) D F t → Log2Lower (natProd as) D F t) ∧
    (∀ t, Log2Upper (natProd as) D F t → Log2Upper (natProd bs) D F t) := by
  have : natProd bs ≤ natProd as := by
    unfold logCompare at h
    rcases Nat.lt_or_ge (natProd as) (natProd bs) with h' | h'
    · exact absurd (Nat.compare_eq_lt.2 h') h
    · exact h'
  exact ⟨fun t hl => Log2Lower_mono this hl, fun t hu => Log2Upper_mono this hu⟩

/-- Separation: if an upper bound `x` of B's log value lies strictly below a lower bound `y` of A's (over one denominator `D > 0`), then A's product is larger. -/
theorem separated_lt {PA PB D F : Nat} (hD : 0 < D) {x y : Int} (hB : Log2Upper PB D F x) (hA : Log2Lower PA D F y) (hxy : x < y) : PB < PA := by
  unfold Log2Upper at hB; unfold Log2Lower at hA
  have hDp : 0 < D ^ (2 ^ F) := Nat.pow_pos hD
  have hPA : 0 < PA ^ 2 ^ F := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, Nat.mul_zero] at hA
    have := Nat.mul_pos (Nat.two_pow_pos y.toNat) hDp
    omega
  have hmul := Nat.mul_le_mul hB hA
  have e1 : PB ^ 2 ^ F * 2 ^ (-x).toNat * (2 ^ y.toNat * D ^ 2 ^ F) = (PB ^ 2 ^ F * 2 ^ ((-x).toNat + y.toNat)) * D ^ 2 ^ F := by
    rw [Nat.pow_add]; ac_rfl
  have e2 : 2 ^ x.toNat * D ^ 2 ^ F * (2 ^ (-y).toNat * PA ^ 2 ^ F) = (2 ^ (x.toNat + (-y).toNat) * PA ^ 2 ^ F) * D ^ 2 ^ F := by
    rw [Nat.pow_add]; ac_rfl
  rw [e1, e2] at hmul
  have h3 := Nat.le_of_mul_le_mul_right hmul hDp
  have hlt : 2 ^ (x.toNat + (-y).toNat) < 2 ^ ((-x).toNat + y.toNat) := Nat.pow_lt_pow_right (by omega) (by omega)
  have h5 : PB ^ 2 ^ F * 2 ^ ((-x).toNat + y.toNat) < PA ^ 2 ^ F * 2 ^ ((-x).toNat + y.toNat) := by
    calc PB ^ 2 ^ F * 2 ^ ((-x).toNat + y.toNat) ≤ 2 ^ (x.toNat + (-y).toNat) * PA ^ 2 ^ F := h3
      _ < 2 ^ ((-x).toNat + y.toNat) * PA ^ 2 ^ F := Nat.mul_lt_mul_of_pos_right hlt hPA
      _ = PA ^ 2 ^ F * 2 ^ ((-x).toNat + y.toNat) := Nat.mul_comm _ _
  have h6 := Nat.lt_of_mul_lt_mul_right h5
  exact (Nat.pow_lt_pow_iff_left (Nat.ne_of_gt (Nat.two_pow_pos F))).1 h6

/-- Enclosures that separate give the exact verdict: A's log value is bounded below by `y`, B's above by `x`, `x < y` (A's loss is strictly lower), then `logCompare = gt`. -/
theorem logCompare_of_separated (as bs : List Nat) {D F : Nat} (hD : 0 < D) {x y : Int}
    (hB : Log2Upper (natProd bs) D F x) (hA : Log2Lower (natProd as) D F y) (hxy : x < y) : logCompare as bs = .gt :=
  (logCompare_gt_iff as bs).2 (separated_lt hD hB hA hxy)

-- Witness (V8): at `D = 100`, `F = 2`: A = (5,8) has product 40 and B = (6,4) has 24; `4 * log2 (24/100) ≤ -8 < -6 ≤ 4 * log2 (40/100)`, so A is better.
example : Log2Upper 24 100 2 (-8) := by unfold Log2Upper; decide
example : Log2Lower 40 100 2 (-6) := by unfold Log2Lower; decide
example : Log2Upper (natProd [6, 4]) 100 2 (-8) ∧ Log2Lower (natProd [5, 8]) 100 2 (-6) ∧ logCompare [5, 8] [6, 4] = .gt := by
  refine ⟨by unfold Log2Upper natProd; decide, by unfold Log2Lower natProd; decide, by decide⟩
example : Log2Upper (natProd [6, 4]) 100 2 (-8) → Log2Lower (natProd [5, 8]) 100 2 (-6) → logCompare [5, 8] [6, 4] = .gt := fun hB hA =>
  logCompare_of_separated [5, 8] [6, 4] (D := 100) (F := 2) (by decide) (x := -8) (y := -6) hB hA (by decide)
example : logCompare [5, 8] [6, 4] ≠ .lt ∧ Log2Lower 24 100 2 (-9) := by
  refine ⟨by decide, by unfold Log2Lower; decide⟩

end VbmForecast
