import VbmProb.Dist.Map
import VbmProbProofs.Dist.Canon
import VbmProbProofs.Dist.Normalize
import VbmProbProofs.Dist.Query
/-! # `map`, `mapMono`, `shift`: the properties DS15 and DS16, each with its witness

`map f d` is `normCore` of the pushed weights; `map_vals` shows its atoms (as plain pairs) are exactly `canon` of them, and `canon` keeps every weighted sum `Σ g(k)·w` (`canon_gsum`) and every weight positive. Two lists with strictly increasing keys, positive weights and the same weighted sums are equal (`inc_pos_unique`), which gives `map_map` and the constant case. -/
namespace VbmProb
namespace Dist

/-- The weighted sum `Σ g(k)·w` over keyed weights. -/
def gsum {γ : Type} (g : γ → Rat) (l : List (γ × Rat)) : Rat := (l.map (fun a => g a.1 * a.2)).sum

/-- The 0/1 indicator of an event, as a rational. -/
def ev {γ : Type} (e : γ → Bool) (x : γ) : Rat := if e x then 1 else 0

/-- An atom as a plain (key, value) pair. -/
def vals {γ : Type} (a : γ × Prob) : γ × Rat := (a.1, a.2.val)

theorem gsum_cons {γ : Type} (g : γ → Rat) (a : γ × Rat) (l : List (γ × Rat)) :
    gsum g (a :: l) = g a.1 * a.2 + gsum g l := by simp [gsum]

theorem gsum_perm {γ : Type} (g : γ → Rat) {l l' : List (γ × Rat)} (h : l.Perm l') : gsum g l = gsum g l' :=
  sum_perm_rat (h.map _)

/-! ## `canon` keeps weighted sums and positivity -/

theorem canonMerge_gsum {γ : Type} [Key γ] (g : γ → Rat) (cur : γ × Rat) (ys : List (γ × Rat))
    (h : KeySorted (cur :: ys)) : gsum g (canonMerge cur ys) = gsum g (cur :: ys) := by
  induction ys generalizing cur with
  | nil => simp [canonMerge]
  | cons y ys ih =>
    have hp := List.pairwise_cons.mp h
    have hy := List.pairwise_cons.mp hp.2
    unfold canonMerge
    by_cases hlt : cur.1 < y.1
    · simp only [hlt, ↓reduceIte]
      have := ih y (List.pairwise_cons.mpr ⟨hy.1, hy.2⟩)
      rw [gsum_cons, this, gsum_cons g cur (y :: ys)]
    · simp only [hlt, ↓reduceIte]
      have hyc : y.1 = cur.1 := by
        rcases Key.lt_trichotomy cur.1 y.1 with h1 | h1 | h1
        · exact absurd h1 hlt
        · exact h1.symm
        · exact absurd h1 (hp.1 y (List.mem_cons_self ..))
      have hs : KeySorted ((cur.1, cur.2 + y.2) :: ys) :=
        List.pairwise_cons.mpr ⟨fun b hb => hp.1 b (List.mem_cons_of_mem _ hb), hy.2⟩
      rw [ih _ hs, gsum_cons, gsum_cons g cur (y :: ys), gsum_cons g y ys, hyc, Rat.mul_add, Rat.add_assoc]

/-- `canon` keeps every weighted sum. -/
theorem canon_gsum {γ : Type} [Key γ] (g : γ → Rat) (ws : List (γ × Rat)) :
    gsum g (canon ws) = gsum g ws := by
  have hs := canon_sorted ws
  unfold canon
  rw [← gsum_perm g (List.mergeSort_perm ws (fun a b => keyLe a.1 b.1))]
  generalize ws.mergeSort (fun a b => keyLe a.1 b.1) = l at hs ⊢
  cases l with
  | nil => rfl
  | cons x xs => exact canonMerge_gsum g x xs hs

theorem canonMerge_pos {γ : Type} [Key γ] (cur : γ × Rat) (ys : List (γ × Rat)) (hc : 0 < cur.2)
    (hy : ∀ y ∈ ys, 0 < y.2) : ∀ a ∈ canonMerge cur ys, 0 < a.2 := by
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
      exact ih (cur.1, cur.2 + y.2) (by show 0 < cur.2 + y.2; grind) (fun z hz => hy z (by simp [hz])) a ha

/-- `canon` of positive weights has positive weights. -/
theorem canon_pos {γ : Type} [Key γ] (ws : List (γ × Rat)) (h : ∀ a ∈ ws, 0 < a.2) : ∀ a ∈ canon ws, 0 < a.2 := by
  unfold canon
  have hp := List.mergeSort_perm ws (fun a b => keyLe a.1 b.1)
  generalize ws.mergeSort (fun a b => keyLe a.1 b.1) = l at hp
  have hl : ∀ a ∈ l, 0 < a.2 := fun a ha => h a (hp.mem_iff.mp ha)
  cases l with
  | nil => simp [canonMergeAll]
  | cons x xs => exact canonMerge_pos x xs (hl x (by simp)) (fun z hz => hl z (by simp [hz]))

/-! ## Uniqueness of the canonical form -/

/-- The indicator of a key. -/
def ind {γ : Type} [DecidableEq γ] (k : γ) (x : γ) : Rat := if x = k then 1 else 0

theorem gsum_ind_zero {γ : Type} [DecidableEq γ] (k : γ) :
    ∀ l : List (γ × Rat), k ∉ l.map (·.1) → gsum (ind k) l = 0
  | [], _ => by simp [gsum]
  | a :: l, h => by
    have hne : a.1 ≠ k := fun e => h (by simp [e])
    have ih := gsum_ind_zero k l (fun hh => h (by simp [hh]))
    rw [gsum_cons, ih]
    simp [ind, hne]
    decide +kernel

/-- The head key of an increasing list is not among the later keys. -/
theorem head_notin {γ : Type} [Key γ] (a : γ × Rat) (t : List (γ × Rat))
    (h : ((a :: t).map (·.1)).Pairwise (· < ·)) : a.1 ∉ t.map (·.1) := fun hh => by
  obtain ⟨c, hc, e⟩ := List.mem_map.mp hh
  have := (List.pairwise_cons.mp h).1 c.1 (List.mem_map_of_mem hc)
  rw [e] at this
  exact Key.lt_irrefl _ this

/-- A key below the head of an increasing list is not in it. -/
theorem lt_head_notin {γ : Type} [Key γ] (x : γ) (b : γ × Rat) (t : List (γ × Rat))
    (h : ((b :: t).map (·.1)).Pairwise (· < ·)) (hx : x < b.1) : x ∉ (b :: t).map (·.1) := fun hh => by
  rcases List.mem_cons.mp hh with e | e
  · rw [e] at hx; exact Key.lt_irrefl _ hx
  · obtain ⟨c, hc, ec⟩ := List.mem_map.mp e
    have := Key.lt_trans hx ((List.pairwise_cons.mp h).1 c.1 (List.mem_map_of_mem hc))
    rw [ec] at this
    exact Key.lt_irrefl _ this

theorem gsum_ind_head {γ : Type} [Key γ] [DecidableEq γ] (a : γ × Rat) (t : List (γ × Rat))
    (h : ((a :: t).map (·.1)).Pairwise (· < ·)) : gsum (ind a.1) (a :: t) = a.2 := by
  rw [gsum_cons, gsum_ind_zero _ _ (head_notin a t h)]
  simp [ind]
  exact Rat.add_zero _

/-- Two lists with strictly increasing keys and positive weights, with the same weighted sums, are equal. -/
theorem inc_pos_unique {γ : Type} [Key γ] [DecidableEq γ] : ∀ l1 l2 : List (γ × Rat),
    (l1.map (·.1)).Pairwise (· < ·) → (l2.map (·.1)).Pairwise (· < ·) →
    (∀ a ∈ l1, 0 < a.2) → (∀ a ∈ l2, 0 < a.2) → (∀ g : γ → Rat, gsum g l1 = gsum g l2) → l1 = l2
  | [], [], _, _, _, _, _ => rfl
  | [], b :: t2, _, k2, _, p2, hg => by
    have h := hg (ind b.1)
    rw [gsum_ind_head b t2 k2] at h
    have := p2 b (by simp)
    have h0 : gsum (ind b.1) ([] : List (γ × Rat)) = 0 := rfl
    rw [h0] at h
    rw [← h] at this; exact absurd this Rat.lt_irrefl
  | a :: t1, [], k1, _, p1, _, hg => by
    have h := hg (ind a.1)
    rw [gsum_ind_head a t1 k1] at h
    have := p1 a (by simp)
    have h0 : gsum (ind a.1) ([] : List (γ × Rat)) = 0 := rfl
    rw [h0] at h
    rw [h] at this; exact absurd this Rat.lt_irrefl
  | a :: t1, b :: t2, k1, k2, p1, p2, hg => by
    have hk1 := List.pairwise_cons.mp k1
    have hk2 := List.pairwise_cons.mp k2
    have hab : a.1 = b.1 := by
      rcases Key.lt_trichotomy a.1 b.1 with h | h | h
      · exfalso
        have h1 := hg (ind a.1)
        rw [gsum_ind_head a t1 k1, gsum_ind_zero _ _ (lt_head_notin _ b t2 k2 h)] at h1
        have := p1 a (by simp)
        rw [h1] at this; exact absurd this Rat.lt_irrefl
      · exact h
      · exfalso
        have h1 := hg (ind b.1)
        rw [gsum_ind_head b t2 k2, gsum_ind_zero _ _ (lt_head_notin _ a t1 k1 h)] at h1
        have := p2 b (by simp)
        rw [← h1] at this; exact absurd this Rat.lt_irrefl
    have hw : a.2 = b.2 := by
      have h1 := hg (ind a.1)
      rw [gsum_ind_head a t1 k1, hab, gsum_ind_head b t2 k2] at h1
      exact h1
    have hh : a = b := Prod.ext hab hw
    have ht : ∀ g : γ → Rat, gsum g t1 = gsum g t2 := fun g => by
      have := hg g
      rw [gsum_cons, gsum_cons, hh] at this
      exact Rat.add_left_cancel _ this
    rw [hh, inc_pos_unique t1 t2 hk1.2 hk2.2 (fun x hx => p1 x (by simp [hx])) (fun x hx => p2 x (by simp [hx])) ht]


/-! ## The atoms of `map` -/

theorem vals_inj {γ : Type} [Key γ] : ∀ l l' : List (γ × Prob), l.map vals = l'.map vals → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have h1 : a = b := by
      have e := h.1
      simp only [vals, Prod.mk.injEq] at e
      have h2 : a.1 = b.1 := e.1
      have h3 : a.2.val = b.2.val := e.2
      exact Prod.ext h2 (Prob.ext h3)
    rw [h1, vals_inj l l' h.2]

theorem expect_eq_gsum {γ : Type} [Key γ] (d : Dist γ) (g : γ → Rat) : d.expect g = gsum g (d.atoms.map vals) := by
  unfold expect gsum
  rw [List.map_map]
  rfl

theorem vals_keys {γ : Type} [Key γ] (d : Dist γ) : ((d.atoms.map vals).map (·.1)).Pairwise (· < ·) := by
  have := d.sorted
  rw [List.map_map]
  exact this

theorem vals_pos {γ : Type} [Key γ] (d : Dist γ) : ∀ a ∈ d.atoms.map vals, 0 < a.2 := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact d.positive b hb

/-- Two distributions with the same expectation of every function are equal. -/
theorem eq_of_expect {γ : Type} [Key γ] {d1 d2 : Dist γ} (h : ∀ g : γ → Rat, d1.expect g = d2.expect g) :
    d1 = d2 := by
  classical
  apply Dist.ext
  apply vals_inj
  exact inc_pos_unique _ _ (vals_keys d1) (vals_keys d2) (vals_pos d1) (vals_pos d2)
    (fun g => by rw [← expect_eq_gsum, ← expect_eq_gsum]; exact h g)

variable {α β : Type} [Key α] [Key β]

omit [Key β] in
theorem pushW_pos (f : α → β) (d : Dist α) : ∀ a ∈ pushW f d, 0 < a.2 := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact d.positive b hb

omit [Key β] in
theorem pushW_sum (f : α → β) (d : Dist α) : ((pushW f d).map (·.2)).sum = 1 := by
  have := d.total
  unfold pushW
  rw [List.map_map]
  exact this

omit [Key β] in
theorem pushW_ne (f : α → β) (d : Dist α) : pushW f d ≠ [] := by
  intro h
  apply atoms_ne_nil d
  unfold pushW at h
  simpa using h

theorem normWeights_push (f : α → β) (d : Dist α) : normWeights (pushW f d) = canon (pushW f d) := by
  unfold normWeights
  rw [List.filter_eq_self]
  intro a ha
  simpa using canon_pos _ (pushW_pos f d) a ha

theorem normWeights_push_ne (f : α → β) (d : Dist α) : normWeights (pushW f d) ≠ [] := by
  rw [normWeights_push]
  intro h
  have hs := canon_weightSum (pushW f d)
  rw [h] at hs
  have h1 := pushW_sum f d
  unfold weightSum at hs
  simp only [List.map_nil, List.sum_nil] at hs
  rw [h1] at hs
  revert hs
  decide +kernel

/-- The division step succeeds on the pushed weights, and its atoms are the kept weights over their total. -/
theorem map_core (f : α → β) (d : Dist α) :
    ∃ r : Dist β, normCore (pushW f d) = .ok r ∧ r.atoms = normAtoms (normWeights (pushW f d)) := by
  obtain ⟨r, hr, hat⟩ := ofAtoms_normAtoms (normWeights_push_ne f d) (normWeights_pos _) (normWeights_keys _)
  exact ⟨r, by unfold normCore; simp [normWeights_push_ne f d, hr], hat⟩

theorem map_atoms (f : α → β) (d : Dist α) : (map f d).atoms = normAtoms (normWeights (pushW f d)) := by
  obtain ⟨r, hr, hat⟩ := map_core f d
  unfold map
  rw [hr]
  exact hat

/-- The atoms of `map f d`, as plain pairs, are `canon` of the pushed weights. -/
theorem map_vals (f : α → β) (d : Dist α) : (map f d).atoms.map vals = canon (pushW f d) := by
  rw [map_atoms]
  unfold normAtoms
  rw [List.map_map, ← normWeights_push]
  have hnn : ∀ a ∈ pushW f d, 0 ≤ a.2 := fun a ha => Rat.le_of_lt (pushW_pos f d a ha)
  have ht : ((normWeights (pushW f d)).map (·.2)).sum = 1 := by
    rw [weightTotal_normWeights _ hnn]; exact pushW_sum f d
  rw [ht]
  conv => rhs; rw [← List.map_id (normWeights (pushW f d))]
  apply List.map_congr_left
  intro a ha
  have hb := div_bounds (normWeights_pos _) ha
  rw [ht] at hb
  have : a.2 / 1 = a.2 := by
    have e : (1 : Rat)⁻¹ = 1 := by decide +kernel
    rw [Rat.div_def, e, Rat.mul_one]
  simp only [Function.comp_apply, vals, id]
  rw [probOf_val (Rat.le_of_lt hb.1) hb.2, this]

/-! ## DS15 -/

/-- The expectation over `map f d` is the expectation over `d` of the composite. -/
theorem expect_map (f : α → β) (d : Dist α) (g : β → Rat) : (map f d).expect g = d.expect (g ∘ f) := by
  rw [expect_eq_gsum, map_vals, canon_gsum]
  unfold gsum pushW expect
  rw [List.map_map]
  rfl

theorem massVal_eq {γ : Type} (e : γ → Bool) : ∀ l : List (γ × Prob),
    massVal e l = (l.map (fun a => ev e a.1 * a.2.val)).sum
  | [] => rfl
  | a :: l => by
    simp only [massVal, List.map_cons, List.sum_cons, ev, massVal_eq e l]
    by_cases h : e a.1 = true <;> simp [h]
    · exact (Rat.zero_add _).symm

theorem mass_val_expect {γ : Type} [Key γ] (d : Dist γ) (e : γ → Bool) : (d.mass e).val = d.expect (ev e) :=
  massVal_eq e d.atoms

/-- DS15: `mass (map f d) e = mass d (e ∘ f)`. -/
theorem mass_map (f : α → β) (d : Dist α) (e : β → Bool) : (map f d).mass e = d.mass (e ∘ f) := by
  apply Prob.ext
  rw [mass_val_expect, mass_val_expect, expect_map]
  rfl

/-- DS15: `map id d = d`. -/
theorem map_id (d : Dist α) : map id d = d :=
  eq_of_expect (fun g => by rw [expect_map]; rfl)

/-- DS15: `map g (map f d) = map (g ∘ f) d`. -/
theorem map_map {γ : Type} [Key γ] (f : α → β) (g : β → γ) (d : Dist α) :
    map g (map f d) = map (g ∘ f) d :=
  eq_of_expect (fun h => by rw [expect_map, expect_map, expect_map]; rfl)

/-- DS15: a constant `f` gives a point. -/
theorem map_const (c : β) (d : Dist α) : map (fun _ => c) d = point c :=
  eq_of_expect (fun g => by rw [expect_map, expect_point]; exact expect_const d (g c))

theorem expect_mapMono (f : α → β) (h : ∀ a b : α, a < b → f a < f b) (d : Dist α) (g : β → Rat) :
    (mapMono f h d).expect g = d.expect (g ∘ f) := by
  unfold expect mapMono
  simp only [List.map_map]
  rfl

/-- DS15: for a strictly increasing `f`, `map f d = mapMono f d`. -/
theorem map_eq_mapMono (f : α → β) (h : ∀ a b : α, a < b → f a < f b) (d : Dist α) : map f d = mapMono f h d :=
  eq_of_expect (fun g => by rw [expect_map, expect_mapMono])

/-- DS15: for a strictly increasing `f`, `map` does not change the number of atoms. -/
theorem size_map (f : α → β) (h : ∀ a b : α, a < b → f a < f b) (d : Dist α) : (map f d).size = d.size := by
  rw [map_eq_mapMono f h]
  unfold size mapMono
  simp

theorem mass_mapMono (f : α → β) (h : ∀ a b : α, a < b → f a < f b) (d : Dist α) (e : β → Bool) :
    (mapMono f h d).mass e = d.mass (e ∘ f) := by
  rw [← map_eq_mapMono f h]; exact mass_map f d e

/-! ## DS16 -/

section Shift

variable {γ : Type} [Key γ] [AddKey γ]

/-- DS16: `shift c d` has the atoms `(a + c, p)`, in the same order. -/
theorem shift_atoms (c : γ) (d : Dist γ) : (shift c d).atoms = d.atoms.map (fun a => (a.1 + c, a.2)) := rfl

theorem lt_add_iff (x a c : γ) : x + c < a + c ↔ x < a := by
  constructor
  · intro h
    rcases Key.lt_trichotomy x a with h1 | h1 | h1
    · exact h1
    · subst h1; exact (Key.lt_irrefl _ h).elim
    · exact (Key.lt_irrefl _ (Key.lt_trans h (AddKey.add_lt_add_right h1 c))).elim
  · exact fun h => AddKey.add_lt_add_right h c

/-- DS16: `cdf (shift c d) (x + c) = cdf d x`. -/
theorem cdf_shift (c : γ) (d : Dist γ) (x : γ) : (shift c d).cdf (x + c) = d.cdf x := by
  unfold cdf shift
  rw [mass_mapMono]
  congr 1
  funext a
  simp [Function.comp, lt_add_iff]

/-- DS16: `mean (shift c d) = mean d + c` (over rational keys). -/
theorem mean_shift (c : Rat) (d : Dist Rat) : (shift c d).mean = d.mean + c := by
  unfold mean shift
  rw [expect_mapMono]
  have := expect_add d id (fun _ => c)
  rw [expect_const] at this
  exact this

/-- DS16: `shift 0 d = d`. -/
theorem shift_zero (d : Dist γ) : shift (0 : γ) d = d := by
  apply Dist.ext
  rw [shift_atoms]
  conv => rhs; rw [← List.map_id d.atoms]
  apply List.map_congr_left
  intro a _
  simp [AddKey.add_zero]

/-- DS16: `shift c (shift c' d) = shift (c + c') d`. -/
theorem shift_shift (c c' : γ) (d : Dist γ) : shift c (shift c' d) = shift (c + c') d := by
  apply Dist.ext
  simp only [shift_atoms, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply]
  rw [AddKey.add_assoc, AddKey.add_comm c' c]

end Shift

/-! ## Witnesses -/

/-- W (DS15): `A` mapped by `k ↦ k / 200` gives 0 with 1/4 and 1 with 3/4 (two keys merged, the sum kept). -/
example : (map (fun k : Int => k / 200) distA).atoms.map vals = [(0, 1/4), (1, 3/4)] := by
  rw [map_vals]
  have e : (pushW (fun k : Int => k / 200) distA).mergeSort (fun a b => keyLe a.1 b.1) =
      pushW (fun k : Int => k / 200) distA :=
    List.mergeSort_of_pairwise (by decide +kernel)
  unfold canon
  rw [e]
  decide +kernel

/-- W (DS15): the mass of the image event, `e = (≥ 1)`: 3/4. -/
example : ((map (fun k : Int => k / 200) distA).mass (fun k => decide (1 ≤ k))).val = 3/4 := by
  rw [mass_map]; decide +kernel

/-- W (DS15): `map id` and a constant map. -/
example : map id distA = distA := map_id _
example : map (fun _ => (7 : Int)) distA = point 7 := map_const _ _

/-- W (DS15): the hypothesis of the monotone case holds for `k ↦ k + 1` on `Int`, and the sizes agree. -/
example : (map (fun k : Int => k + 1) distA).size = distA.size :=
  size_map _ (fun _ _ h => by omega) _
example : map (fun k : Int => k + 1) distA = mapMono (fun k : Int => k + 1) (fun _ _ h => by omega) distA :=
  map_eq_mapMono _ _ _
/-- The hypothesis fails for `k ↦ k / 200` (it is not strictly increasing on `A`'s keys), so the merge happens. -/
example : ¬ (∀ a b : Int, a < b → a / 200 < b / 200) := fun h => by
  have := h 200 300 (by decide +kernel)
  revert this; decide +kernel

/-- W (DS16): `A` shifted by 5 has keys 105, 205, 305 with the same probabilities. -/
example : (shift (5 : Int) distA).atoms.map vals = [(105, 1/4), (205, 1/2), (305, 1/4)] := by
  decide +kernel
/-- W (DS16): the law holds for `Int` and `Rat`; the clauses on a literal. -/
example : (shift (5 : Rat) distThirds).mean = 2 + 5 := by rw [mean_shift]; congr 1; decide +kernel
example : (shift (5 : Int) distA).cdf (150 + 5) = distA.cdf 150 := cdf_shift _ _ _
example : shift (0 : Int) distA = distA := shift_zero _
example : shift (2 : Int) (shift 3 distA) = shift (2 + 3) distA := shift_shift _ _ _
example : (5 : Int) + 1 < 7 + 1 := AddKey.add_lt_add_right (by decide +kernel) 1
example : (5 : Rat) + 1 < 7 + 1 := AddKey.add_lt_add_right (by decide +kernel) 1

end Dist
end VbmProb
