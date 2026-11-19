import VbmProb.Dist.Normalize
import VbmProbProofs.Dist
import VbmProbProofs.Dist.Canon
/-! # `normalize`: the property DS5, with its witnesses

The result's probabilities sum to exactly 1 (the type says so, and `normalize` builds the proof); the probability at each key is the key's weight over the total; zero-weight keys are absent; the refusals `negativeWeight i` and `zeroTotalWeight` are exact; an input that `make` accepts is returned unchanged; scaling every weight by `c > 0` changes nothing. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-- A list of zeros sums to 0. -/
theorem sum_all_zero : ∀ m : List Rat, (∀ x ∈ m, x = 0) → m.sum = 0
  | [], _ => rfl
  | y :: m, h => by
    simp only [List.sum_cons, h y (by simp), sum_all_zero m (fun z hz => h z (by simp [hz])), Rat.zero_add]

/-! ## Sums of rationals -/

theorem sum_nonneg' : ∀ l : List Rat, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
  | [], _ => Rat.le_refl
  | x :: l, h => by
    simp only [List.sum_cons]
    exact Rat.add_nonneg (h x (by simp)) (sum_nonneg' l fun y hy => h y (by simp [hy]))

/-- A nonneg list that sums to 0 is all zeros. -/
theorem sum_zero_all : ∀ l : List Rat, (∀ x ∈ l, 0 ≤ x) → l.sum = 0 → ∀ x ∈ l, x = 0
  | [], _, _ => by simp
  | x :: l, h, hs => by
    simp only [List.sum_cons] at hs
    have hx := h x (by simp)
    have hl := sum_nonneg' l (fun y hy => h y (by simp [hy]))
    have hx0 : x = 0 := by grind
    have hl0 : l.sum = 0 := by grind
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx0
    · exact sum_zero_all l (fun z hz => h z (by simp [hz])) hl0 y hy

/-- An element of a nonneg list is at most the sum. -/
theorem le_sum : ∀ l : List Rat, (∀ x ∈ l, 0 ≤ x) → ∀ x ∈ l, x ≤ l.sum
  | [], _, x, hx => by simp at hx
  | y :: l, h, x, hx => by
    simp only [List.sum_cons]
    have hl := sum_nonneg' l (fun z hz => h z (by simp [hz]))
    have hy := h y (by simp)
    rcases List.mem_cons.mp hx with rfl | hx
    · grind
    · have := le_sum l (fun z hz => h z (by simp [hz])) x hx
      grind

theorem probOf_val {q : Rat} (h0 : 0 ≤ q) (h1 : q ≤ 1) : (probOf q).val = q := by
  unfold probOf; simp [h0, h1]

omit [Key α] in
/-- Positive weights over their total are probabilities, and they are positive. -/
theorem div_bounds {L : List (α × Rat)} (hp : ∀ a ∈ L, 0 < a.2) {b : α × Rat} (hb : b ∈ L) :
    0 < b.2 / (L.map (·.2)).sum ∧ b.2 / (L.map (·.2)).sum ≤ 1 := by
  have hnn : ∀ x ∈ L.map (·.2), 0 ≤ x := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx; exact Rat.le_of_lt (hp c hc)
  have hle := le_sum _ hnn b.2 (List.mem_map_of_mem hb)
  have hbp := hp b hb
  have hT : 0 < (L.map (·.2)).sum := by grind
  have hTi : 0 < ((L.map (·.2)).sum)⁻¹ := Rat.inv_pos.mpr hT
  refine ⟨by rw [Rat.div_def]; exact Rat.mul_pos hbp hTi, ?_⟩
  rw [Rat.div_def]
  have := Rat.mul_le_mul_of_nonneg_right hle (Rat.le_of_lt hTi)
  rwa [Rat.mul_inv_cancel _ (by grind)] at this

omit [Key α] in
theorem sum_probOf (T : Rat) : ∀ L : List (α × Rat), (∀ a ∈ L, 0 ≤ a.2 / T ∧ a.2 / T ≤ 1) →
    ((L.map (fun a => (a.1, probOf (a.2 / T)))).map (·.2.val)).sum = (L.map (·.2)).sum / T
  | [], _ => by simp [Rat.div_def]
  | a :: L, h => by
    have ih := sum_probOf T L (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, probOf_val (h a (by simp)).1 (h a (by simp)).2, Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]

/-- The distribution built from nonempty positive weights with increasing keys. -/
theorem ofAtoms_normAtoms {L : List (α × Rat)} (hne : L ≠ []) (hp : ∀ a ∈ L, 0 < a.2)
    (hk : (L.map (·.1)).Pairwise (· < ·)) :
    ∃ d : Dist α, ofAtoms (normAtoms L) = .ok d ∧ d.atoms = normAtoms L := by
  have hb := fun b hb => div_bounds hp (b := b) hb
  have hsum : ((normAtoms L).map (·.2.val)).sum = 1 := by
    unfold normAtoms
    rw [sum_probOf _ L (fun b h => ⟨Rat.le_of_lt (hb b h).1, (hb b h).2⟩)]
    have hT : 0 < (L.map (·.2)).sum := by
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, L = x :: xs := by
        cases L with
        | nil => exact absurd rfl hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      have := le_sum _ (fun y hy => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy; exact Rat.le_of_lt (hp c hc)) x.2 (List.mem_map_of_mem (by simp))
      have := hp x (by simp)
      grind
    rw [Rat.div_def, Rat.mul_inv_cancel _ (by grind)]
  have hpos : ∀ a ∈ normAtoms L, 0 < a.2.val := by
    intro a ha
    obtain ⟨b, hbL, rfl⟩ := List.mem_map.mp ha
    show 0 < (probOf _).val
    rw [probOf_val (Rat.le_of_lt (hb b hbL).1) (hb b hbL).2]
    exact (hb b hbL).1
  have hkeys : ((normAtoms L).map (·.1)).Pairwise (· < ·) := by
    have : (normAtoms L).map (·.1) = L.map (·.1) := by
      simp [normAtoms, List.map_map, Function.comp_def]
    rw [this]; exact hk
  refine ⟨⟨normAtoms L, hkeys, hpos, hsum⟩, ?_, rfl⟩
  unfold ofAtoms
  split
  · rfl
  · next hh => exact absurd ⟨hkeys, hpos, hsum⟩ hh

theorem mem_normWeights {ws : List (α × Rat)} {a : α × Rat} :
    a ∈ normWeights ws ↔ a ∈ canon ws ∧ 0 < a.2 := by
  simp [normWeights]

theorem normWeights_keys (ws : List (α × Rat)) : ((normWeights ws).map (·.1)).Pairwise (· < ·) :=
  (canon_keys_increasing ws).sublist ((List.filter_sublist).map _)

theorem normWeights_pos (ws : List (α × Rat)) : ∀ a ∈ normWeights ws, 0 < a.2 :=
  fun _ h => (mem_normWeights.mp h).2

/-! ## Non-negativity of the canonical weights -/

theorem canonMerge_nonneg (cur : α × Rat) (ys : List (α × Rat)) (hc : 0 ≤ cur.2) (hy : ∀ y ∈ ys, 0 ≤ y.2) :
    ∀ a ∈ canonMerge cur ys, 0 ≤ a.2 := by
  induction ys generalizing cur with
  | nil => intro a ha; simp [canonMerge] at ha; subst ha; exact hc
  | cons y ys ih =>
    intro a ha
    unfold canonMerge at ha
    have hy' := hy y (by simp)
    by_cases h : cur.1 < y.1
    · simp only [h, ↓reduceIte, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hc
      · exact ih y hy' (fun z hz => hy z (by simp [hz])) a ha
    · simp only [h, ↓reduceIte] at ha
      exact ih (cur.1, cur.2 + y.2) (Rat.add_nonneg hc hy') (fun z hz => hy z (by simp [hz])) a ha

theorem canon_nonneg (ws : List (α × Rat)) (h : ∀ a ∈ ws, 0 ≤ a.2) : ∀ a ∈ canon ws, 0 ≤ a.2 := by
  unfold canon
  have hp := List.mergeSort_perm ws (fun a b => keyLe a.1 b.1)
  generalize ws.mergeSort (fun a b => keyLe a.1 b.1) = l at hp
  have hl : ∀ a ∈ l, 0 ≤ a.2 := fun a ha => h a (hp.mem_iff.mp ha)
  cases l with
  | nil => simp [canonMergeAll]
  | cons x xs => exact canonMerge_nonneg x xs (hl x (by simp)) (fun z hz => hl z (by simp [hz]))

omit [Key α] in
theorem sum_filter_pos : ∀ l : List (α × Rat), (∀ a ∈ l, 0 ≤ a.2) →
    ((l.filter (fun a => decide (0 < a.2))).map (·.2)).sum = (l.map (·.2)).sum
  | [], _ => rfl
  | a :: l, h => by
    have ih := sum_filter_pos l (fun b hb => h b (by simp [hb]))
    have ha := h a (by simp)
    by_cases hz : 0 < a.2
    · simp [hz, ih]
    · have : a.2 = 0 := by grind
      simp [ih, this, Rat.zero_add]

theorem weightTotal_normWeights (ws : List (α × Rat)) (h : ∀ a ∈ ws, 0 ≤ a.2) :
    ((normWeights ws).map (·.2)).sum = (ws.map (·.2)).sum := by
  unfold normWeights
  rw [sum_filter_pos _ (canon_nonneg ws h)]
  exact canon_weightSum ws

/-! ## The weight at a key of a canonical list -/

omit [Key α] in
theorem wa_not [DecidableEq α] (k : α) : ∀ L : List (α × Rat), k ∉ L.map (·.1) → weightAt k L = 0
  | [], _ => rfl
  | x :: L, h => by
    have hx : x.1 ≠ k := fun e => h (by simp [e])
    have := wa_not k L (fun hh => h (by simp [hh]))
    simp only [weightAt, List.filter_cons, hx, decide_false] at this ⊢
    simpa [hx] using this

theorem wa_mem [DecidableEq α] (k : α) (c : Rat) : ∀ L : List (α × Rat),
    (L.map (·.1)).Pairwise (· < ·) → (k, c) ∈ L → weightAt k L = c
  | [], _, h => by simp at h
  | x :: L, hk, h => by
    have hp := List.pairwise_cons.mp hk
    rcases List.mem_cons.mp h with he | hm
    · subst he
      have hn : k ∉ L.map (·.1) := fun hh => by
        obtain ⟨b, hb, e⟩ := List.mem_map.mp hh
        exact Key.lt_irrefl k (e ▸ hp.1 b.1 (List.mem_map_of_mem hb))
      have := wa_not k L hn
      simp only [weightAt, List.filter_cons] at this ⊢
      simp [this, Rat.add_zero]
    · have hlt : x.1 < k := hp.1 k (List.mem_map_of_mem (f := (·.1)) hm)
      have hx : x.1 ≠ k := fun e => Key.lt_irrefl _ (e ▸ hlt)
      have := wa_mem k c L hp.2 hm
      simp only [weightAt, List.filter_cons] at this ⊢
      simpa [hx] using this

/-! ## DS5 -/

/-- DS5, the zero-weight test: `normWeights` is empty exactly when all the (non-negative) weights are 0. -/
theorem normWeights_eq_nil_iff (ws : List (α × Rat)) (h : ∀ a ∈ ws, 0 ≤ a.2) :
    normWeights ws = [] ↔ ∀ a ∈ ws, a.2 = 0 := by
  have hc := canon_nonneg ws h
  have hs := canon_weightSum ws
  constructor
  · intro he a ha
    have hcz : ∀ x ∈ canon ws, x.2 = 0 := by
      intro x hx
      by_cases hz : 0 < x.2
      · have : x ∈ normWeights ws := mem_normWeights.mpr ⟨hx, hz⟩
        rw [he] at this; simp at this
      · have := hc x hx; grind
    have hsum : ((canon ws).map (·.2)).sum = 0 := by
      have : ∀ x ∈ (canon ws).map (·.2), x = 0 := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hcz y hy
      clear hs hc hcz he
      generalize (canon ws).map (·.2) = m at this ⊢
      induction m with
      | nil => rfl
      | cons y m ih => exact sum_all_zero _ this
    have : (ws.map (·.2)).sum = 0 := hs.symm.trans hsum
    exact sum_zero_all _ (fun x hx => by obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hx; exact h c hc') this _
      (List.mem_map_of_mem ha)
  · intro hz
    have hsum : (ws.map (·.2)).sum = 0 := by
      have : ∀ x ∈ ws.map (·.2), x = 0 := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hz y hy
      generalize ws.map (·.2) = m at this ⊢
      induction m with
      | nil => rfl
      | cons y m ih => exact sum_all_zero _ this
    have hcs : ((canon ws).map (·.2)).sum = 0 := hsum ▸ hs
    have hall := sum_zero_all _ (fun x hx => by obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hx; exact hc c hc') hcs
    cases hn : normWeights ws with
    | nil => rfl
    | cons x xs =>
      have hx : x ∈ normWeights ws := by rw [hn]; simp
      have ⟨hx1, hx2⟩ := mem_normWeights.mp hx
      have := hall x.2 (List.mem_map_of_mem hx1)
      grind

/-- DS5, the refusal `zeroTotalWeight`: given the limits hold and no weight is negative, `normalize` refuses
`zeroTotalWeight` exactly when every weight is 0. -/
theorem normalize_zeroTotalWeight_iff {lim : Limits} {ws : List (α × Rat)}
    (hn : ¬ lim.maxAtoms < ws.length) (hb : ∀ a ∈ ws, a.2.bits ≤ lim.maxBits) (hnn : ∀ a ∈ ws, 0 ≤ a.2) :
    normalize lim ws = .error .zeroTotalWeight ↔ ∀ a ∈ ws, a.2 = 0 := by
  have h1 : firstWhere (fun a : α × Rat => decide (lim.maxBits < a.2.bits)) ws 0 = none :=
    (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simpa using hb a ha
  have h2 : firstWhere (fun a : α × Rat => decide (a.2 < 0)) ws 0 = none :=
    (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simpa using Rat.not_lt.mpr (hnn a ha)
  have e : normalize lim ws = normCore ws := by simp [normalize, hn, h1, h2]
  rw [e, ← normWeights_eq_nil_iff ws hnn]
  unfold normCore
  by_cases he : normWeights ws = []
  · simp [he]
  · simp only [he, ↓reduceIte, iff_false]
    intro hh
    obtain ⟨d, hd, -⟩ := ofAtoms_normAtoms (L := normWeights ws) he (normWeights_pos ws) (normWeights_keys ws)
    rw [hd] at hh; cases hh

/-- DS5, acceptance: with the limits holding, no negative weight and one positive weight, `normalize` accepts,
and the atoms are the kept weights over their total. -/
theorem normalize_ok {lim : Limits} {ws : List (α × Rat)}
    (hn : ¬ lim.maxAtoms < ws.length) (hb : ∀ a ∈ ws, a.2.bits ≤ lim.maxBits) (hnn : ∀ a ∈ ws, 0 ≤ a.2)
    (hpos : ∃ a ∈ ws, 0 < a.2) :
    ∃ d : Dist α, normalize lim ws = .ok d ∧ d.atoms = normAtoms (normWeights ws) := by
  have h1 : firstWhere (fun a : α × Rat => decide (lim.maxBits < a.2.bits)) ws 0 = none :=
    (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simpa using hb a ha
  have h2 : firstWhere (fun a : α × Rat => decide (a.2 < 0)) ws 0 = none :=
    (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simpa using Rat.not_lt.mpr (hnn a ha)
  have he : normWeights ws ≠ [] := fun h => by
    obtain ⟨a, ha, hp⟩ := hpos
    have := (normWeights_eq_nil_iff ws hnn).mp h a ha
    rw [this] at hp; exact Rat.lt_irrefl hp
  obtain ⟨d, hd, hat⟩ := ofAtoms_normAtoms he (normWeights_pos ws) (normWeights_keys ws)
  refine ⟨d, ?_, hat⟩
  simp [normalize, hn, h1, h2, normCore, he, hd]

/-- DS5, the first refusals: the first negative weight (given the limits hold). -/
theorem normalize_negativeWeight {lim : Limits} {ws : List (α × Rat)} {i : Nat} {a : α × Rat}
    (hn : ¬ lim.maxAtoms < ws.length)
    (hb : firstWhere (fun a : α × Rat => decide (lim.maxBits < a.2.bits)) ws 0 = none)
    (h : firstWhere (fun a : α × Rat => decide (a.2 < 0)) ws 0 = some (i, a)) :
    normalize lim ws = .error (.negativeWeight i) := by
  simp [normalize, hn, hb, h]

/-- DS5, the limit refusals come first. -/
theorem normalize_tooManyAtoms {lim : Limits} {ws : List (α × Rat)} (h : lim.maxAtoms < ws.length) :
    normalize lim ws = .error (.tooManyAtoms ws.length lim.maxAtoms) := by
  simp [normalize, h]

theorem normalize_numberTooLarge {lim : Limits} {ws : List (α × Rat)} {i : Nat} {a : α × Rat}
    (hn : ¬ lim.maxAtoms < ws.length)
    (h : firstWhere (fun a : α × Rat => decide (lim.maxBits < a.2.bits)) ws 0 = some (i, a)) :
    normalize lim ws = .error (.numberTooLarge i a.2.bits lim.maxBits) := by
  simp [normalize, hn, h]

/-- DS5, the sum: the probabilities of the result sum to exactly 1 (the field `total`). -/
theorem normalize_total {lim : Limits} {ws : List (α × Rat)} {d : Dist α} (_ : normalize lim ws = .ok d) :
    (d.atoms.map (·.2.val)).sum = 1 := d.total

/-- DS5, the probability at each key is the weight at that key over the total weight. -/
theorem normalize_prob [DecidableEq α] {ws : List (α × Rat)} {d : Dist α}
    (hnn : ∀ a ∈ ws, 0 ≤ a.2) (hd : d.atoms = normAtoms (normWeights ws)) :
    ∀ a ∈ d.atoms, a.2.val = weightAt a.1 ws / (ws.map (·.2)).sum := by
  intro a ha
  rw [hd] at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have hbc := (mem_normWeights.mp hb)
  have hw : weightAt b.1 ws = b.2 := by
    rw [← canon_weightAt]
    exact wa_mem b.1 b.2 _ (canon_keys_increasing ws) (by simpa using hbc.1)
  show (probOf _).val = _
  have hbd := div_bounds (normWeights_pos ws) hb
  rw [probOf_val (Rat.le_of_lt hbd.1) hbd.2, hw, weightTotal_normWeights ws hnn]

/-- DS5, the support: a key is present exactly when its weight is positive (zero-weight keys are absent). -/
theorem normalize_support [DecidableEq α] {ws : List (α × Rat)} {d : Dist α}
    (hd : d.atoms = normAtoms (normWeights ws)) (k : α) :
    k ∈ d.support ↔ 0 < weightAt k ws := by
  have hsup : d.support = (normWeights ws).map (·.1) := by
    unfold support; rw [hd]; simp [normAtoms, List.map_map, Function.comp_def]
  rw [hsup]
  constructor
  · intro hk
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
    have hbc := mem_normWeights.mp hb
    have : weightAt b.1 ws = b.2 := by
      rw [← canon_weightAt]
      exact wa_mem b.1 b.2 _ (canon_keys_increasing ws) (by simpa using hbc.1)
    rw [this]; exact hbc.2
  · intro hpos
    have hne : weightAt k (canon ws) ≠ 0 := by
      rw [canon_weightAt]; intro h; rw [h] at hpos; exact Rat.lt_irrefl hpos
    have hin : k ∈ (canon ws).map (·.1) := Classical.byContradiction fun hh => hne (wa_not k _ hh)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hin
    have : weightAt b.1 ws = b.2 := by
      rw [← canon_weightAt]; exact wa_mem b.1 b.2 _ (canon_keys_increasing ws) (by simpa using hb)
    rw [this] at hpos
    exact List.mem_map.mpr ⟨b, mem_normWeights.mpr ⟨hb, hpos⟩, rfl⟩

/-! ## Agreement with `make` -/

/-- A list with strictly increasing keys is its own canonical form. -/
theorem canon_of_increasing (ws : List (α × Rat)) (h : (ws.map (·.1)).Pairwise (· < ·)) : canon ws = ws := by
  have hsorted : ws.Pairwise (fun a b => keyLe a.1 b.1 = true) := by
    refine List.Pairwise.imp ?_ (List.pairwise_map.mp h)
    intro a b hab
    simp only [keyLe, Bool.not_eq_true', decide_eq_false_iff_not]
    exact Key.lt_asymm hab
  have e : ws.mergeSort (fun a b => keyLe a.1 b.1) = ws := List.mergeSort_of_pairwise hsorted
  show canonMergeAll (ws.mergeSort (fun a b => keyLe a.1 b.1)) = ws
  rw [e]
  cases ws with
  | nil => rfl
  | cons x xs => exact canonMerge_id x xs h

/-- DS5, agreement with `make`: atoms that `make` accepts, read as weights, are returned unchanged. -/
theorem normalize_of_make {lim : Limits} {atoms : List (α × Prob)} {d : Dist α}
    (h : make lim atoms = .ok d) :
    normalize lim (atoms.map (fun a => (a.1, a.2.val))) = .ok d := by
  have hd := make_atoms h
  have hn : ¬ lim.maxAtoms < atoms.length := fun hh => by
    rw [make_tooManyAtoms hh] at h; cases h
  have hb := ((make_ok_iff lim atoms).mp ⟨d, h⟩).2.1
  obtain ⟨ws, hws⟩ : ∃ ws, ws = atoms.map (fun a => (a.1, a.2.val)) := ⟨_, rfl⟩
  rw [← hws]
  have hmem : ∀ a ∈ ws, ∃ p ∈ atoms, a = (p.1, p.2.val) := fun a ha => by
    rw [hws] at ha
    obtain ⟨p, hp, e⟩ := List.mem_map.mp ha
    exact ⟨p, hp, e.symm⟩
  have hlen : ws.length = atoms.length := by rw [hws]; simp
  have hnn : ∀ a ∈ ws, 0 ≤ a.2 := fun a ha => by
    obtain ⟨p, _, rfl⟩ := hmem a ha; exact p.2.nonneg
  have hpos : ∀ a ∈ ws, 0 < a.2 := fun a ha => by
    obtain ⟨p, hp, rfl⟩ := hmem a ha; exact d.positive p (hd ▸ hp)
  have hkeys : (ws.map (·.1)).Pairwise (· < ·) := by
    have : ws.map (·.1) = atoms.map (·.1) := by simp [hws, List.map_map, Function.comp_def]
    rw [this, ← hd]; exact d.sorted
  have hsum : (ws.map (·.2)).sum = 1 := by
    have : ws.map (·.2) = atoms.map (·.2.val) := by simp [hws, List.map_map, Function.comp_def]
    rw [this, ← hd]; exact d.total
  have hcan : normWeights ws = ws := by
    unfold normWeights; rw [canon_of_increasing ws hkeys, List.filter_eq_self]
    intro a ha; simpa using hpos a ha
  have hne : ws ≠ [] := fun e => by
    have h2 : atoms = [] := by rw [hws] at e; simpa using e
    have := d.total; rw [hd, h2] at this; simp at this
  obtain ⟨x, xs, hx⟩ : ∃ x xs, ws = x :: xs := by
    cases ws with
    | nil => exact absurd rfl hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  obtain ⟨d', hd', hat⟩ := normalize_ok (lim := lim) (ws := ws) (by rw [hlen]; exact hn)
    (fun a ha => by obtain ⟨p, hp, rfl⟩ := hmem a ha; exact hb p hp) hnn
    ⟨x, by simp [hx], hpos x (by simp [hx])⟩
  rw [hd']
  congr 1
  apply Dist.ext
  rw [hat, hd, hcan]
  unfold normAtoms
  rw [hsum, hws, List.map_map]
  conv => rhs; rw [← List.map_id atoms]
  apply List.map_congr_left
  intro a ha
  have : a.2.val / 1 = a.2.val := by
    have e : (1 : Rat)⁻¹ = 1 := by decide +kernel
    rw [Rat.div_def, e, Rat.mul_one]
  simp only [Function.comp_apply, this, id]
  congr 1
  exact Prob.ext (probOf_val a.2.nonneg a.2.le_one)

/-! ## Scaling the weights -/

/-- Every weight multiplied by `c`. -/
def scaleW (c : Rat) (ws : List (α × Rat)) : List (α × Rat) := ws.map (fun a => (a.1, c * a.2))

theorem canonMerge_scale (c : Rat) (cur : α × Rat) (ys : List (α × Rat)) :
    canonMerge (cur.1, c * cur.2) (scaleW c ys) = scaleW c (canonMerge cur ys) := by
  induction ys generalizing cur with
  | nil => simp [canonMerge, scaleW]
  | cons y ys ih =>
    unfold scaleW at ih ⊢
    simp only [List.map_cons, canonMerge]
    by_cases h : cur.1 < y.1
    · simp only [h, ↓reduceIte, List.map_cons]
      rw [ih y]
    · simp only [h, ↓reduceIte]
      have := ih (cur.1, cur.2 + y.2)
      simp only [Rat.mul_add] at this
      exact this

theorem canon_scale (c : Rat) (ws : List (α × Rat)) : canon (scaleW c ws) = scaleW c (canon ws) := by
  unfold canon scaleW
  have e : (ws.map (fun a => (a.1, c * a.2))).mergeSort (fun a b : α × Rat => keyLe a.1 b.1)
      = (ws.mergeSort (fun a b : α × Rat => keyLe a.1 b.1)).map (fun a => (a.1, c * a.2)) :=
    (List.map_mergeSort (r := fun a b : α × Rat => keyLe a.1 b.1) (s := fun a b : α × Rat => keyLe a.1 b.1)
      (f := fun a => (a.1, c * a.2)) (fun _ _ _ _ => rfl)).symm
  rw [e]
  generalize ws.mergeSort (fun a b : α × Rat => keyLe a.1 b.1) = l
  cases l with
  | nil => rfl
  | cons x xs =>
    have := canonMerge_scale c x xs
    simpa [canonMergeAll, scaleW] using this

theorem normWeights_scale {c : Rat} (hc : 0 < c) (ws : List (α × Rat)) :
    normWeights (scaleW c ws) = scaleW c (normWeights ws) := by
  unfold normWeights
  rw [canon_scale]
  unfold scaleW
  rw [List.filter_map]
  have : ∀ (l : List (α × Rat)), List.filter ((fun a : α × Rat => decide (0 < a.2)) ∘ fun a => (a.1, c * a.2)) l
      = List.filter (fun a : α × Rat => decide (0 < a.2)) l := by
    intro l
    apply List.filter_congr
    intro a _
    simp only [Function.comp_apply, decide_eq_decide]
    constructor
    · intro h
      by_cases h0 : 0 < a.2
      · exact h0
      · have : a.2 ≤ 0 := Rat.not_lt.mp h0
        have := Rat.mul_le_mul_of_nonneg_left this (Rat.le_of_lt hc)
        rw [Rat.mul_zero] at this
        exact absurd h (Rat.not_lt.mpr this)
    · intro h; exact Rat.mul_pos hc h
  rw [this]

omit [Key α] in
theorem weightSum_scale (c : Rat) : ∀ L : List (α × Rat), ((scaleW c L).map (·.2)).sum = c * (L.map (·.2)).sum
  | [] => by simp [scaleW, Rat.mul_zero]
  | a :: L => by
    have ih := weightSum_scale c L
    simp only [scaleW, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Rat.mul_add]

omit [Key α] in
theorem normAtoms_scale {c : Rat} (hc : c ≠ 0) (L : List (α × Rat)) : normAtoms (scaleW c L) = normAtoms L := by
  unfold normAtoms
  rw [weightSum_scale]
  simp only [scaleW, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply]
  congr 2
  rw [Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  have hcc : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
  calc c * a.2 * ((L.map (·.2)).sum⁻¹ * c⁻¹) = a.2 * (L.map (·.2)).sum⁻¹ * (c * c⁻¹) := by
        grind
    _ = _ := by rw [hcc, Rat.mul_one]

/-- DS5, scale invariance (after the limits): scaling every weight by `c > 0` does not change the result. -/
theorem normCore_scale {c : Rat} (hc : 0 < c) (ws : List (α × Rat)) :
    normCore (scaleW c ws) = normCore ws := by
  unfold normCore
  rw [normWeights_scale hc]
  have hne : scaleW c (normWeights ws) = [] ↔ normWeights ws = [] := by
    unfold scaleW; simp
  by_cases he : normWeights ws = []
  · simp [he, scaleW]
  · have : scaleW c (normWeights ws) ≠ [] := fun h => he (hne.mp h)
    simp only [he, this, ↓reduceIte]
    rw [normAtoms_scale (by grind)]

/-- Under the limits and with no negative weight, `normalize` is the division step `normCore`. -/
theorem normalize_eq_core {lim : Limits} {ws : List (α × Rat)}
    (hn : ¬ lim.maxAtoms < ws.length) (hb : ∀ a ∈ ws, a.2.bits ≤ lim.maxBits) (hnn : ∀ a ∈ ws, 0 ≤ a.2) :
    normalize lim ws = normCore ws := by
  have h1 : firstWhere (fun a : α × Rat => decide (lim.maxBits < a.2.bits)) ws 0 = none :=
    (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simpa using hb a ha
  have h2 : firstWhere (fun a : α × Rat => decide (a.2 < 0)) ws 0 = none :=
    (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simpa using Rat.not_lt.mpr (hnn a ha)
  simp [normalize, hn, h1, h2]

/-- DS5, scale invariance: when both inputs pass the limits and no weight is negative, scaling every weight
by `c > 0` does not change the result. -/
theorem normalize_scale {lim : Limits} {c : Rat} (hc : 0 < c) {ws : List (α × Rat)}
    (hn : ¬ lim.maxAtoms < ws.length) (hb : ∀ a ∈ ws, a.2.bits ≤ lim.maxBits)
    (hb' : ∀ a ∈ scaleW c ws, a.2.bits ≤ lim.maxBits) (hnn : ∀ a ∈ ws, 0 ≤ a.2) :
    normalize lim (scaleW c ws) = normalize lim ws := by
  have hlen : (scaleW c ws).length = ws.length := by simp [scaleW]
  have hnn' : ∀ a ∈ scaleW c ws, 0 ≤ a.2 := fun a ha => by
    obtain ⟨b, hb2, rfl⟩ := List.mem_map.mp ha
    exact Rat.mul_nonneg (Rat.le_of_lt hc) (hnn b hb2)
  rw [normalize_eq_core (by rw [hlen]; exact hn) hb' hnn', normalize_eq_core hn hb hnn, normCore_scale hc]

/-! ## Witnesses -/

/-- The kept weights over their total, as plain pairs. -/
theorem normalize_vals {lim : Limits} {ws : List (α × Rat)}
    (hn : ¬ lim.maxAtoms < ws.length) (hb : ∀ a ∈ ws, a.2.bits ≤ lim.maxBits) (hnn : ∀ a ∈ ws, 0 ≤ a.2)
    (hpos : ∃ a ∈ ws, 0 < a.2) :
    ∃ d : Dist α, normalize lim ws = .ok d ∧
      d.atoms.map (fun a => (a.1, a.2.val)) =
        (normWeights ws).map (fun a => (a.1, a.2 / ((normWeights ws).map (·.2)).sum)) := by
  obtain ⟨d, hd, hat⟩ := normalize_ok hn hb hnn hpos
  refine ⟨d, hd, ?_⟩
  rw [hat]
  unfold normAtoms
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  have hbd := div_bounds (normWeights_pos ws) ha
  simp only [Function.comp_apply]
  rw [probOf_val (Rat.le_of_lt hbd.1) hbd.2]

/-- W: weights 1, 2, 1 at keys 100, 200, 300 give 1/4, 1/2, 1/4. -/
example : ∃ d : Dist Int, normalize Limits.default [((100 : Int), (1 : Rat)), (200, 2), (300, 1)] = .ok d ∧
    d.atoms.map (fun a => (a.1, a.2.val)) = [(100, 1/4), (200, 1/2), (300, 1/4)] := by
  have hk : ([((100 : Int), (1 : Rat)), (200, 2), (300, 1)].map (·.1)).Pairwise (· < ·) := by decide +kernel
  obtain ⟨d, hd, hv⟩ := normalize_vals (lim := Limits.default) (ws := [((100 : Int), (1 : Rat)), (200, 2), (300, 1)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨d, hd, ?_⟩
  rw [hv]
  unfold normWeights
  rw [canon_of_increasing _ hk]
  decide +kernel

/-- W: weights 1, 1, 1 give 1/3 each. -/
example : ∃ d : Dist Int, normalize Limits.default [((1 : Int), (1 : Rat)), (2, 1), (3, 1)] = .ok d ∧
    d.atoms.map (fun a => (a.1, a.2.val)) = [(1, 1/3), (2, 1/3), (3, 1/3)] := by
  have hk : ([((1 : Int), (1 : Rat)), (2, 1), (3, 1)].map (·.1)).Pairwise (· < ·) := by decide +kernel
  obtain ⟨d, hd, hv⟩ := normalize_vals (lim := Limits.default) (ws := [((1 : Int), (1 : Rat)), (2, 1), (3, 1)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨d, hd, ?_⟩
  rw [hv]
  unfold normWeights
  rw [canon_of_increasing _ hk]
  decide +kernel

/-- W: the zero weight is dropped: `[(1,0),(2,3)]` is the point at 2. -/
example : ∃ d : Dist Int, normalize Limits.default [((1 : Int), (0 : Rat)), (2, 3)] = .ok d ∧
    d.atoms.map (fun a => (a.1, a.2.val)) = [(2, 1)] := by
  have hk : ([((1 : Int), (0 : Rat)), (2, 3)].map (·.1)).Pairwise (· < ·) := by decide +kernel
  obtain ⟨d, hd, hv⟩ := normalize_vals (lim := Limits.default) (ws := [((1 : Int), (0 : Rat)), (2, 3)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨d, hd, ?_⟩
  rw [hv]
  unfold normWeights
  rw [canon_of_increasing _ hk]
  decide +kernel

/-- W: unsorted input with a repeated key: `[(3,1),(1,1),(3,1),(2,1)]` gives 1 ↦ 1/4, 2 ↦ 1/4, 3 ↦ 1/2. -/
example : ∃ d : Dist Nat, normalize Limits.default [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)] = .ok d ∧
    d.atoms.map (fun a => (a.1, a.2.val)) = [(1, 1/4), (2, 1/4), (3, 1/2)] := by
  obtain ⟨d, hd, hv⟩ := normalize_vals (lim := Limits.default)
    (ws := [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨d, hd, ?_⟩
  rw [hv]
  unfold normWeights canon
  rw [sort_example]
  decide +kernel

/-- W: a negative weight refuses with the position of the first: `[(1,1),(2,-1)]` gives `negativeWeight 1`. -/
example : normalize Limits.default [((1 : Int), (1 : Rat)), (2, -1)] = .error (.negativeWeight 1) :=
  normalize_negativeWeight (a := ((2 : Int), (-1 : Rat))) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- W: all weights 0 refuse `zeroTotalWeight`; and `[(1,0),(2,0)]` satisfies the hypothesis of the iff. -/
example : normalize Limits.default [((1 : Int), (0 : Rat)), (2, 0)] = .error .zeroTotalWeight :=
  (normalize_zeroTotalWeight_iff (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr
    (by decide +kernel)

/-- W: the limit refusals come first. -/
example : normalize { Limits.default with maxAtoms := 1 } [((1 : Int), (1 : Rat)), (2, 1)] =
    .error (.tooManyAtoms 2 1) := normalize_tooManyAtoms (by decide +kernel)

/-- W: scaling by 3 changes nothing (the hypotheses hold on the literals). -/
example : normalize Limits.default (scaleW 3 [((1 : Int), (1 : Rat)), (2, 2)]) =
    normalize Limits.default [((1 : Int), (1 : Rat)), (2, 2)] :=
  normalize_scale (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by unfold scaleW; decide +kernel) (by decide +kernel)

/-- W: `make` accepts 1/4, 1/2, 1/4 and `normalize` of the same weights returns that distribution. -/
example (d : Dist Int)
    (h : make Limits.default [((100 : Int), pr (1/4)), (200, pr (1/2)), (300, pr (1/4))] = .ok d) :
    normalize Limits.default [((100 : Int), (1/4 : Rat)), (200, 1/2), (300, 1/4)] = .ok d := by
  have := normalize_of_make h
  simpa [pr] using this

end Dist
end VbmProb
