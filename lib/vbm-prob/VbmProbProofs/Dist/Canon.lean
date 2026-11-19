import VbmProb.Dist.Canon
import VbmProbProofs.Limits
/-! # `canon`: the property DS4, with its witnesses

For every input list the output keys are strictly increasing, the total weight is unchanged, the weight at every key is the sum of the input weights at that key, and the output is a fixed point. Proved from `List.mergeSort_perm` and `List.pairwise_mergeSort`, never by evaluation; only the witnesses evaluate. -/
namespace VbmProb

/-- The total weight of a keyed list. -/
def weightSum {α : Type} (l : List (α × Rat)) : Rat := (l.map (·.2)).sum

/-- The weight at one key: the sum of the weights of the atoms with that key. -/
def weightAt {α : Type} [DecidableEq α] (k : α) (l : List (α × Rat)) : Rat :=
  ((l.filter (fun a => decide (a.1 = k))).map (·.2)).sum

/-- The sorted-by-key shape: no later key is below an earlier one. -/
def KeySorted {α : Type} [Key α] (l : List (α × Rat)) : Prop :=
  l.Pairwise (fun a b => ¬ b.1 < a.1)

theorem lt_of_lt_of_le' {α : Type} [Key α] {a b c : α} (h1 : a < b) (h2 : ¬ c < b) : a < c := by
  rcases Key.lt_trichotomy a c with h | h | h
  · exact h
  · subst h; exact (h2 h1).elim
  · exact (h2 (Key.lt_trans h h1)).elim

/-! ## The merge of a sorted list -/

theorem canonMerge_keys_mem {α : Type} [Key α] (cur : α × Rat) (ys : List (α × Rat)) :
    ∀ k ∈ (canonMerge cur ys).map (·.1), k = cur.1 ∨ k ∈ ys.map (·.1) := by
  induction ys generalizing cur with
  | nil => intro k hk; simp [canonMerge] at hk; exact .inl hk
  | cons y ys ih =>
    intro k hk
    unfold canonMerge at hk
    by_cases h : cur.1 < y.1
    · simp only [h, ↓reduceIte] at hk
      simp only [List.map_cons, List.mem_cons] at hk
      rcases hk with hk | hk
      · exact .inl hk
      · rcases ih y k hk with h | h
        · exact .inr (by simp [h])
        · exact .inr (by simp [h])
    · simp only [h, ↓reduceIte] at hk
      rcases ih _ k hk with h | h
      · exact .inl h
      · exact .inr (by simp [h])

theorem canonMerge_keys {α : Type} [Key α] (cur : α × Rat) (ys : List (α × Rat))
    (h : KeySorted (cur :: ys)) : ((canonMerge cur ys).map (·.1)).Pairwise (· < ·) := by
  induction ys generalizing cur with
  | nil => simp [canonMerge]
  | cons y ys ih =>
    have hp := List.pairwise_cons.mp h
    have hy := List.pairwise_cons.mp hp.2
    unfold canonMerge
    by_cases hlt : cur.1 < y.1
    · simp only [hlt, ↓reduceIte]
      simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih y (List.pairwise_cons.mpr ⟨hy.1, hy.2⟩ |> fun h' => h')⟩
      intro k hk
      rcases canonMerge_keys_mem y ys k hk with e | e
      · rw [e]; exact hlt
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp e
        exact lt_of_lt_of_le' hlt (hy.1 b hb)
    · simp only [hlt, ↓reduceIte]
      apply ih
      refine List.pairwise_cons.mpr ⟨?_, hy.2⟩
      intro b hb
      exact hp.1 b (List.mem_cons_of_mem _ hb)

theorem canonMerge_weightSum {α : Type} [Key α] (cur : α × Rat) (ys : List (α × Rat)) :
    weightSum (canonMerge cur ys) = weightSum (cur :: ys) := by
  induction ys generalizing cur with
  | nil => simp [canonMerge]
  | cons y ys ih =>
    unfold canonMerge
    by_cases hlt : cur.1 < y.1
    · simp only [hlt, ↓reduceIte]
      have := ih y
      simp only [weightSum, List.map_cons, List.sum_cons] at this ⊢
      rw [this]
    · simp only [hlt, ↓reduceIte]; rw [ih]
      simp only [weightSum, List.map_cons, List.sum_cons]
      rw [Rat.add_assoc]

theorem canonMerge_weightAt {α : Type} [Key α] [DecidableEq α] (k : α) (cur : α × Rat) (ys : List (α × Rat))
    (h : KeySorted (cur :: ys)) : weightAt k (canonMerge cur ys) = weightAt k (cur :: ys) := by
  induction ys generalizing cur with
  | nil => simp [canonMerge]
  | cons y ys ih =>
    have hp := List.pairwise_cons.mp h
    have hy := List.pairwise_cons.mp hp.2
    unfold canonMerge
    by_cases hlt : cur.1 < y.1
    · simp only [hlt, ↓reduceIte]
      have := ih y (List.pairwise_cons.mpr ⟨hy.1, hy.2⟩)
      simp only [weightAt, List.filter_cons] at this ⊢
      by_cases hc : cur.1 = k <;> simp [hc, this]
    · simp only [hlt, ↓reduceIte]
      have hyc : y.1 = cur.1 := by
        rcases Key.lt_trichotomy cur.1 y.1 with h1 | h1 | h1
        · exact absurd h1 hlt
        · exact h1.symm
        · exact absurd h1 (hp.1 y (List.mem_cons_self ..))
      have hs : KeySorted ((cur.1, cur.2 + y.2) :: ys) :=
        List.pairwise_cons.mpr ⟨fun b hb => hp.1 b (List.mem_cons_of_mem _ hb), hy.2⟩
      rw [ih _ hs]
      simp only [weightAt, List.filter_cons, hyc]
      by_cases hc : cur.1 = k
      · simp [hc, Rat.add_assoc]
      · simp [hc]

theorem canonMerge_id {α : Type} [Key α] (cur : α × Rat) (ys : List (α × Rat))
    (h : ((cur :: ys).map (·.1)).Pairwise (· < ·)) : canonMerge cur ys = cur :: ys := by
  induction ys generalizing cur with
  | nil => simp [canonMerge]
  | cons y ys ih =>
    have hp := List.pairwise_cons.mp h
    have hlt : cur.1 < y.1 := hp.1 y.1 (by simp)
    unfold canonMerge
    simp only [hlt, ↓reduceIte]
    rw [ih y hp.2]

/-! ## The sort -/

theorem keyLe_total {α : Type} [Key α] (a b : α) : (keyLe a b || keyLe b a) = true := by
  rcases Key.le_total a b with h | h <;> simp [keyLe, Key.le] at h ⊢ <;> simp [h]

theorem keyLe_trans {α : Type} [Key α] {a b c : α} (h1 : keyLe a b = true) (h2 : keyLe b c = true) :
    keyLe a c = true := by
  simp only [keyLe, Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2 ⊢
  exact Key.le_trans h1 h2

theorem canon_sorted {α : Type} [Key α] (ws : List (α × Rat)) :
    KeySorted (ws.mergeSort (fun a b => keyLe a.1 b.1)) := by
  have := List.pairwise_mergeSort (le := fun a b => keyLe a.1 b.1)
    (fun a b c h1 h2 => keyLe_trans (a := a.1) (b := b.1) (c := c.1) h1 h2) (fun a b => keyLe_total a.1 b.1) ws
  refine List.Pairwise.imp ?_ this
  intro a b h
  simpa [keyLe] using h

/-! ## DS4 -/

/-- DS4, order: the output keys are strictly increasing. -/
theorem canon_keys_increasing {α : Type} [Key α] (ws : List (α × Rat)) :
    ((canon ws).map (·.1)).Pairwise (· < ·) := by
  have hs := canon_sorted ws
  unfold canon
  generalize ws.mergeSort (fun a b => keyLe a.1 b.1) = l at hs
  cases l with
  | nil => simp [canonMergeAll]
  | cons x xs => exact canonMerge_keys x xs hs

theorem sum_perm_rat {l l' : List Rat} (h : l.Perm l') : l.sum = l'.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.sum_cons, ih]
  | swap a b l => simp only [List.sum_cons]; rw [← Rat.add_assoc, ← Rat.add_assoc, Rat.add_comm a b]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem weightSum_perm {α : Type} {l l' : List (α × Rat)} (h : l.Perm l') : weightSum l = weightSum l' :=
  sum_perm_rat (h.map _)

/-- DS4, total: the total weight is unchanged. -/
theorem canon_weightSum {α : Type} [Key α] (ws : List (α × Rat)) : weightSum (canon ws) = weightSum ws := by
  unfold canon
  have hp := List.mergeSort_perm ws (fun a b => keyLe a.1 b.1)
  rw [← weightSum_perm hp]
  generalize ws.mergeSort (fun a b => keyLe a.1 b.1) = l
  cases l with
  | nil => rfl
  | cons x xs => exact canonMerge_weightSum x xs

/-- DS4, per key: the weight at every key is the sum of the input weights at that key. -/
theorem canon_weightAt {α : Type} [Key α] [DecidableEq α] (k : α) (ws : List (α × Rat)) :
    weightAt k (canon ws) = weightAt k ws := by
  have hs := canon_sorted ws
  unfold canon
  have hp := List.mergeSort_perm ws (fun a b => keyLe a.1 b.1)
  have : weightAt k (ws.mergeSort (fun a b => keyLe a.1 b.1)) = weightAt k ws :=
    sum_perm_rat ((hp.filter _).map _)
  rw [← this]
  generalize ws.mergeSort (fun a b => keyLe a.1 b.1) = l at hs ⊢
  cases l with
  | nil => rfl
  | cons x xs => exact canonMerge_weightAt k x xs hs

/-- DS4, fixed point: `canon (canon ws) = canon ws`. -/
theorem canon_idem {α : Type} [Key α] (ws : List (α × Rat)) : canon (canon ws) = canon ws := by
  have hk := canon_keys_increasing ws
  have hsorted : (canon ws).Pairwise (fun a b => keyLe a.1 b.1 = true) := by
    have := (List.pairwise_map.mp hk)
    refine List.Pairwise.imp ?_ this
    intro a b h
    simp only [keyLe, Bool.not_eq_true', decide_eq_false_iff_not]
    exact Key.lt_asymm h
  have e : (canon ws).mergeSort (fun a b => keyLe a.1 b.1) = canon ws := List.mergeSort_of_pairwise hsorted
  show canonMergeAll ((canon ws).mergeSort (fun a b => keyLe a.1 b.1)) = canon ws
  rw [e]
  generalize canon ws = l at hk ⊢
  cases l with
  | nil => rfl
  | cons x xs => exact canonMerge_id x xs hk

/-! ## Witnesses -/

/-- The sorted prefix of the spec's example, by `simp` through `List.mergeSort`. -/
theorem sort_example : [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)].mergeSort (fun a b => keyLe a.1 b.1)
    = [(1, 1), (2, 1), (3, 1), (3, 1)] := by
  simp [List.mergeSort, keyLe]

/-- W: `[(3,1),(1,1),(3,1),(2,1)]` gives `[(1,1),(2,1),(3,2)]`. -/
example : canon [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)] = [(1, 1), (2, 1), (3, 2)] := by
  unfold canon; rw [sort_example]; decide +kernel

/-- W: an already sorted input (strictly increasing keys) is unchanged, by `mergeSort_of_pairwise`. -/
example : canon [((1 : Nat), (1 : Rat)), (2, 3), (5, 1)] = [(1, 1), (2, 3), (5, 1)] := by
  have : [((1 : Nat), (1 : Rat)), (2, 3), (5, 1)].mergeSort (fun a b => keyLe a.1 b.1) = [(1, 1), (2, 3), (5, 1)] :=
    List.mergeSort_of_pairwise (by decide +kernel)
  unfold canon; rw [this]; decide +kernel

/-- W: the empty list and a weight at a key: the claims hold on literals (the hypotheses are only the key laws). -/
example : canon ([] : List (Nat × Rat)) = [] := by simp [canon, canonMergeAll]
example : weightAt (3 : Nat) (canon [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)]) = 2 := by
  rw [canon_weightAt]; decide +kernel
example : weightSum (canon [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)]) = 4 := by
  rw [canon_weightSum]; decide +kernel

end VbmProb
