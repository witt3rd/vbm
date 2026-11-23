import VbmProb.Dist.Mixture
import VbmProbProofs.Dist.Normalize
import VbmProbProofs.Dist.Query
import VbmProbProofs.Prob
/-! # `mixture`: the properties DS11 to DS14, with their witnesses

The sorted merge of two atom lists gives rows `(key, (pa, pb))`; the proofs are about that merge (its keys are the union of the supports, strictly increasing; its first components are `a`'s atoms and its second `b`'s, by symmetry), and then about the weights `(1 - lam)·pa + lam·pb`. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

omit [Key α] in
theorem weightAt_nil [DecidableEq α] (k : α) : weightAt k ([] : List (α × Rat)) = 0 := rfl

omit [Key α] in
theorem weightAt_cons [DecidableEq α] (k : α) (x : α × Rat) (L : List (α × Rat)) :
    weightAt k (x :: L) = (if x.1 = k then x.2 else 0) + weightAt k L := by
  unfold weightAt
  by_cases h : x.1 = k <;> simp [h, Rat.zero_add]

/-! ## The merge -/

/-- The merge swaps its two sides when its arguments are swapped. -/
theorem mergeRows_swap : ∀ (n : Nat) (as bs : List (α × Prob)),
    mergeRows n bs as = (mergeRows n as bs).map (fun r => (r.1, (r.2.2, r.2.1)))
  | 0, _, _ => rfl
  | _ + 1, [], [] => by simp [mergeRows]
  | _ + 1, [], b :: bs => by simp [mergeRows]
  | _ + 1, a :: as, [] => by simp [mergeRows]
  | n + 1, a :: as, b :: bs => by
    simp only [mergeRows]
    by_cases h1 : a.1 < b.1
    · have h2 : ¬ b.1 < a.1 := Key.lt_asymm h1
      simp only [h1, h2, ↓reduceIte, List.map_cons]
      rw [mergeRows_swap n (as) (b :: bs)]
    · by_cases h2 : b.1 < a.1
      · simp only [h1, h2, ↓reduceIte, List.map_cons]
        rw [mergeRows_swap n (a :: as) bs]
      · have he : a.1 = b.1 := by
          rcases Key.lt_trichotomy a.1 b.1 with h | h | h
          · exact absurd h h1
          · exact h
          · exact absurd h h2
        simp only [h1, h2, ↓reduceIte, List.map_cons]
        rw [mergeRows_swap n as bs, he]

/-- The keys of the rows are the keys of the two lists. -/
theorem mergeRows_keys_mem : ∀ (n : Nat) (as bs : List (α × Prob)), as.length + bs.length ≤ n → ∀ k : α,
    (k ∈ (mergeRows n as bs).map (·.1) ↔ k ∈ as.map (·.1) ∨ k ∈ bs.map (·.1))
  | 0, as, bs, h, k => by
    have h1 : as = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; subst h2; simp [mergeRows]
  | _ + 1, [], bs, _, k => by simp [mergeRows, List.map_map, Function.comp_def]
  | _ + 1, a :: as, [], _, k => by simp [mergeRows, List.map_map, Function.comp_def]
  | n + 1, a :: as, b :: bs, h, k => by
    simp only [mergeRows]
    by_cases h1 : a.1 < b.1
    · simp only [h1, ↓reduceIte, List.map_cons, List.mem_cons]
      have := mergeRows_keys_mem n as (b :: bs) (by simp at h ⊢; omega) k
      simp only [List.map_cons, List.mem_cons] at this
      rw [this]; grind
    · by_cases h2 : b.1 < a.1
      · simp only [h1, h2, ↓reduceIte, List.map_cons, List.mem_cons]
        have := mergeRows_keys_mem n (a :: as) bs (by simp at h ⊢; omega) k
        simp only [List.map_cons, List.mem_cons] at this
        rw [this]; grind
      · have he : a.1 = b.1 := by
          rcases Key.lt_trichotomy a.1 b.1 with h | h | h
          · exact absurd h h1
          · exact h
          · exact absurd h h2
        simp only [h1, h2, ↓reduceIte, List.map_cons, List.mem_cons]
        have := mergeRows_keys_mem n as bs (by simp at h ⊢; omega) k
        rw [this, he]; grind

/-- The keys of the rows are strictly increasing. -/
theorem mergeRows_keys_inc : ∀ (n : Nat) (as bs : List (α × Prob)), as.length + bs.length ≤ n →
    (as.map (·.1)).Pairwise (· < ·) → (bs.map (·.1)).Pairwise (· < ·) →
    ((mergeRows n as bs).map (·.1)).Pairwise (· < ·)
  | 0, as, bs, h, _, _ => by
    have h1 : as = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; subst h2; simp [mergeRows]
  | _ + 1, [], bs, _, _, hb => by simpa [mergeRows, List.map_map, Function.comp_def] using hb
  | _ + 1, a :: as, [], _, ha, _ => by simpa [mergeRows, List.map_map, Function.comp_def] using ha
  | n + 1, a :: as, b :: bs, h, ha, hb => by
    have hpa := List.pairwise_cons.mp ha
    have hpb := List.pairwise_cons.mp hb
    simp only [mergeRows]
    by_cases h1 : a.1 < b.1
    · simp only [h1, ↓reduceIte, List.map_cons, List.pairwise_cons]
      have hlen : as.length + (b :: bs).length ≤ n := by simp at h ⊢; omega
      refine ⟨?_, mergeRows_keys_inc n as (b :: bs) hlen hpa.2 hb⟩
      intro k hk
      rcases (mergeRows_keys_mem n as (b :: bs) hlen k).mp hk with h3 | h3
      · exact hpa.1 k h3
      · have h3' : k ∈ b.1 :: bs.map (·.1) := h3
        rcases List.mem_cons.mp h3' with e | e
        · rw [e]; exact h1
        · exact Key.lt_trans h1 (hpb.1 k e)
    · by_cases h2 : b.1 < a.1
      · simp only [h1, h2, ↓reduceIte, List.map_cons, List.pairwise_cons]
        have hlen : (a :: as).length + bs.length ≤ n := by simp at h ⊢; omega
        refine ⟨?_, mergeRows_keys_inc n (a :: as) bs hlen ha hpb.2⟩
        intro k hk
        rcases (mergeRows_keys_mem n (a :: as) bs hlen k).mp hk with h3 | h3
        · have h3' : k ∈ a.1 :: as.map (·.1) := h3
          rcases List.mem_cons.mp h3' with e | e
          · rw [e]; exact h2
          · exact Key.lt_trans h2 (hpa.1 k e)
        · exact hpb.1 k h3
      · have he : a.1 = b.1 := by
          rcases Key.lt_trichotomy a.1 b.1 with h | h | h
          · exact absurd h h1
          · exact h
          · exact absurd h h2
        simp only [h1, h2, ↓reduceIte, List.map_cons, List.pairwise_cons]
        have hlen : as.length + bs.length ≤ n := by simp at h ⊢; omega
        refine ⟨?_, mergeRows_keys_inc n as bs hlen hpa.2 hpb.2⟩
        intro k hk
        rcases (mergeRows_keys_mem n as bs hlen k).mp hk with h3 | h3
        · exact hpa.1 k h3
        · rw [he]; exact hpb.1 k h3

/-- The first components of the rows put the weight of `a` at each key. -/
theorem mergeRows_weightAt [DecidableEq α] (k : α) : ∀ (n : Nat) (as bs : List (α × Prob)),
    as.length + bs.length ≤ n →
    weightAt k ((mergeRows n as bs).map (fun r => (r.1, r.2.1))) = weightAt k (as.map (fun a => (a.1, a.2.val)))
  | 0, as, bs, h => by
    have h1 : as = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; subst h2; simp [mergeRows]
  | _ + 1, [], bs, _ => by
    simp only [mergeRows, List.map_map, List.map_nil]
    have : ∀ L : List (α × Prob), weightAt k (L.map (fun b => (b.1, (0 : Rat)))) = 0 := by
      intro L
      induction L with
      | nil => rfl
      | cons x L ih =>
        simp only [List.map_cons, weightAt_cons, ih]
        split <;> simp [Rat.zero_add]
    rw [weightAt_nil]
    simpa [Function.comp_def] using this bs
  | _ + 1, a :: as, [], _ => by
    simp only [mergeRows, List.map_map]
    rfl
  | n + 1, a :: as, b :: bs, h => by
    simp only [mergeRows]
    by_cases h1 : a.1 < b.1
    · simp only [h1, ↓reduceIte, List.map_cons, weightAt_cons]
      rw [mergeRows_weightAt k n as (b :: bs) (by simp at h ⊢; omega)]
    · by_cases h2 : b.1 < a.1
      · simp only [h1, h2, ↓reduceIte, List.map_cons, weightAt_cons]
        rw [mergeRows_weightAt k n (a :: as) bs (by simp at h ⊢; omega)]
        simp only [List.map_cons, weightAt_cons]
        split <;> simp [Rat.zero_add]
      · simp only [h1, h2, ↓reduceIte, List.map_cons, weightAt_cons]
        rw [mergeRows_weightAt k n as bs (by simp at h ⊢; omega)]

/-- The sum over the rows of a function of the key times the first component is the sum over `a`. -/
theorem mergeRows_sum1 (f : α → Rat) : ∀ (n : Nat) (as bs : List (α × Prob)), as.length + bs.length ≤ n →
    ((mergeRows n as bs).map (fun r => f r.1 * r.2.1)).sum = (as.map (fun a => f a.1 * a.2.val)).sum
  | 0, as, bs, h => by
    have h1 : as = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; subst h2; simp [mergeRows]
  | _ + 1, [], bs, _ => by
    simp only [mergeRows, List.map_nil, List.sum_nil]
    have : ∀ L : List (α × Prob), (L.map (fun r => f r.1 * (0 : Rat))).sum = 0 := by
      intro L
      induction L with
      | nil => rfl
      | cons x L ih => simp only [List.map_cons, List.sum_cons, Rat.mul_zero, Rat.zero_add] at ih ⊢; exact ih
    simpa [List.map_map, Function.comp_def] using this bs
  | _ + 1, a :: as, [], _ => by
    simp only [mergeRows, List.map_map]
    rfl
  | n + 1, a :: as, b :: bs, h => by
    simp only [mergeRows]
    by_cases h1 : a.1 < b.1
    · simp only [h1, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [mergeRows_sum1 f n as (b :: bs) (by simp at h ⊢; omega)]
    · by_cases h2 : b.1 < a.1
      · simp only [h1, h2, ↓reduceIte, List.map_cons, List.sum_cons, Rat.mul_zero, Rat.zero_add]
        rw [mergeRows_sum1 f n (a :: as) bs (by simp at h ⊢; omega)]
        simp
      · simp only [h1, h2, ↓reduceIte, List.map_cons, List.sum_cons]
        rw [mergeRows_sum1 f n as bs (by simp at h ⊢; omega)]

/-- Both components of every row are non-negative. -/
theorem mergeRows_nonneg : ∀ (n : Nat) (as bs : List (α × Prob)), ∀ r ∈ mergeRows n as bs,
    0 ≤ r.2.1 ∧ 0 ≤ r.2.2
  | 0, _, _, r, hr => by simp [mergeRows] at hr
  | _ + 1, [], bs, r, hr => by
    simp only [mergeRows, List.mem_map] at hr
    obtain ⟨b, _, rfl⟩ := hr
    exact ⟨Rat.le_refl, b.2.nonneg⟩
  | _ + 1, a :: as, [], r, hr => by
    simp only [mergeRows, List.mem_map] at hr
    obtain ⟨b, _, rfl⟩ := hr
    exact ⟨b.2.nonneg, Rat.le_refl⟩
  | n + 1, a :: as, b :: bs, r, hr => by
    simp only [mergeRows] at hr
    by_cases h1 : a.1 < b.1
    · simp only [h1, ↓reduceIte, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨a.2.nonneg, Rat.le_refl⟩
      · exact mergeRows_nonneg n as (b :: bs) r hr
    · by_cases h2 : b.1 < a.1
      · simp only [h1, h2, ↓reduceIte, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨Rat.le_refl, b.2.nonneg⟩
        · exact mergeRows_nonneg n (a :: as) bs r hr
      · simp only [h1, h2, ↓reduceIte, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨a.2.nonneg, b.2.nonneg⟩
        · exact mergeRows_nonneg n as bs r hr

/-- The positive first components are exactly `a`'s atoms (when they are positive). -/
theorem mergeRows_pos1 : ∀ (n : Nat) (as bs : List (α × Prob)), as.length + bs.length ≤ n →
    (∀ a ∈ as, 0 < a.2.val) →
    (((mergeRows n as bs).map (fun r => (r.1, r.2.1))).filter (fun a => decide (0 < a.2)))
      = as.map (fun a => (a.1, a.2.val))
  | 0, as, bs, h, _ => by
    have h1 : as = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : bs = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; subst h2; simp [mergeRows]
  | _ + 1, [], bs, _, _ => by
    simp only [mergeRows, List.map_nil, List.map_map]
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    simp [Rat.lt_irrefl]
  | _ + 1, a :: as, [], _, hp => by
    have e : List.map (fun r : α × (Rat × Rat) => (r.1, r.2.1)) ((a :: as).map (fun a => (a.1, (a.2.val, (0 : Rat)))))
        = (a :: as).map (fun a => (a.1, a.2.val)) := by simp [List.map_map, Function.comp_def]
    simp only [mergeRows]
    rw [e, List.filter_eq_self]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    simpa using hp b hb
  | n + 1, a :: as, b :: bs, h, hp => by
    have ha := hp a (by simp)
    have hps : ∀ x ∈ as, 0 < x.2.val := fun x hx => hp x (by simp [hx])
    simp only [mergeRows]
    by_cases h1 : a.1 < b.1
    · simp only [h1, ↓reduceIte, List.map_cons, List.filter_cons, ha, decide_true]
      rw [mergeRows_pos1 n as (b :: bs) (by simp at h ⊢; omega) hps]
    · by_cases h2 : b.1 < a.1
      · simp only [h1, h2, ↓reduceIte, List.map_cons, List.filter_cons]
        simp only [Rat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact mergeRows_pos1 n (a :: as) bs (by simp at h ⊢; omega) hp
      · simp only [h1, h2, ↓reduceIte, List.map_cons, List.filter_cons, ha, decide_true]
        rw [mergeRows_pos1 n as bs (by simp at h ⊢; omega) hps]

/-- Merging a list with itself pairs each atom with itself. -/
theorem mergeRows_self : ∀ (n : Nat) (as : List (α × Prob)), as.length ≤ n →
    mergeRows n as as = as.map (fun a => (a.1, (a.2.val, a.2.val)))
  | 0, as, h => by
    have h1 : as = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; simp [mergeRows]
  | _ + 1, [], _ => by simp [mergeRows]
  | n + 1, a :: as, h => by
    simp only [mergeRows, Key.lt_irrefl, ↓reduceIte, List.map_cons]
    rw [mergeRows_self n as (by simp at h; omega)]

/-! ## Sums over the rows -/

/-- Swapping the two sides of a row. -/
def swapRow (r : α × (Rat × Rat)) : α × (Rat × Rat) := (r.1, (r.2.2, r.2.1))

theorem mergeRows_swap' (n : Nat) (as bs : List (α × Prob)) :
    mergeRows n as bs = (mergeRows n bs as).map swapRow := by
  rw [mergeRows_swap n bs as]
  simp [swapRow]

theorem rows_swap (a b : Dist α) : rows b a = (rows a b).map swapRow := by
  unfold rows
  rw [Nat.add_comm b.atoms.length]
  exact mergeRows_swap' _ _ _

/-- The sum over the rows of a function of the key times the second component is the sum over `b`. -/
theorem mergeRows_sum2 (f : α → Rat) (n : Nat) (as bs : List (α × Prob)) (h : as.length + bs.length ≤ n) :
    ((mergeRows n as bs).map (fun r => f r.1 * r.2.2)).sum = (bs.map (fun a => f a.1 * a.2.val)).sum := by
  rw [mergeRows_swap' n as bs, List.map_map]
  exact mergeRows_sum1 f n bs as (by omega)

/-- The second components put the weight of `b` at each key. -/
theorem mergeRows_weightAt2 [DecidableEq α] (k : α) (n : Nat) (as bs : List (α × Prob))
    (h : as.length + bs.length ≤ n) :
    weightAt k ((mergeRows n as bs).map (fun r => (r.1, r.2.2))) = weightAt k (bs.map (fun a => (a.1, a.2.val))) := by
  rw [mergeRows_swap' n as bs, List.map_map]
  exact mergeRows_weightAt k n bs as (by omega)

omit [Key α] in
/-- The sum of a weighted function over the rows splits over the two sides. -/
theorem sum_mixWeight (lam : Prob) (g : α → Rat) : ∀ rs : List (α × (Rat × Rat)),
    (rs.map (fun r => g r.1 * mixWeight lam r.2)).sum
      = (1 - lam.val) * (rs.map (fun r => g r.1 * r.2.1)).sum + lam.val * (rs.map (fun r => g r.1 * r.2.2)).sum
  | [] => by simp only [List.map_nil, List.sum_nil, Rat.mul_zero, Rat.add_zero]
  | r :: rs => by
    have ih := sum_mixWeight lam g rs
    simp only [List.map_cons, List.sum_cons, mixWeight] at ih ⊢
    rw [ih]
    grind

omit [Key α] in
/-- The weight at a key splits over the two sides. -/
theorem weightAt_mixWeight [DecidableEq α] (lam : Prob) (k : α) : ∀ rs : List (α × (Rat × Rat)),
    weightAt k (rs.map (fun r => (r.1, mixWeight lam r.2)))
      = (1 - lam.val) * weightAt k (rs.map (fun r => (r.1, r.2.1))) + lam.val * weightAt k (rs.map (fun r => (r.1, r.2.2)))
  | [] => by simp [weightAt_nil, Rat.mul_zero, Rat.add_zero]
  | r :: rs => by
    have ih := weightAt_mixWeight lam k rs
    simp only [List.map_cons, weightAt_cons] at ih ⊢
    rw [ih]
    by_cases h : r.1 = k
    · simp only [h, ↓reduceIte, mixWeight]
      grind
    · simp only [h, ↓reduceIte]
      grind

/-! ## The weights of the mixture -/

omit [Key α] in
theorem mixWeight_nonneg (lam : Prob) {r : Rat × Rat} (h0 : 0 ≤ r.1) (h1 : 0 ≤ r.2) : 0 ≤ mixWeight lam r :=
  Rat.add_nonneg (Rat.mul_nonneg (Prob.complement lam).nonneg h0) (Rat.mul_nonneg lam.nonneg h1)

/-- The weights of the rows, before the zero ones are dropped. -/
def mixW (lam : Prob) (a b : Dist α) : List (α × Rat) := (rows a b).map (fun r => (r.1, mixWeight lam r.2))

theorem mixW_nonneg (lam : Prob) (a b : Dist α) : ∀ x ∈ mixW lam a b, 0 ≤ x.2 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have := mergeRows_nonneg _ _ _ r hr
  exact mixWeight_nonneg lam this.1 this.2

theorem rows_sum1 (a b : Dist α) : ((rows a b).map (fun r => r.2.1)).sum = 1 := by
  have := mergeRows_sum1 (fun _ => (1 : Rat)) (a.atoms.length + b.atoms.length) a.atoms b.atoms (Nat.le_refl _)
  simp only [Rat.one_mul] at this
  unfold rows
  rw [this]
  exact a.total

theorem rows_sum2 (a b : Dist α) : ((rows a b).map (fun r => r.2.2)).sum = 1 := by
  have := mergeRows_sum2 (fun _ => (1 : Rat)) (a.atoms.length + b.atoms.length) a.atoms b.atoms (Nat.le_refl _)
  simp only [Rat.one_mul] at this
  unfold rows
  rw [this]
  exact b.total

/-- The weights of the rows sum to 1. -/
theorem mixW_sum (lam : Prob) (a b : Dist α) : ((mixW lam a b).map (·.2)).sum = 1 := by
  have h := sum_mixWeight lam (fun _ => (1 : Rat)) (rows a b)
  simp only [Rat.one_mul] at h
  have e : ((mixW lam a b).map (·.2)).sum = ((rows a b).map (fun r => mixWeight lam r.2)).sum := by
    simp [mixW, List.map_map, Function.comp_def]
  rw [e, h, rows_sum1, rows_sum2, Rat.mul_one, Rat.mul_one, Rat.sub_eq_add_neg, Rat.add_assoc,
    Rat.add_comm (-lam.val) lam.val, Rat.add_neg_cancel, Rat.add_zero]

/-! ## The mixture is a distribution -/

theorem rows_keys_inc (a b : Dist α) : ((rows a b).map (·.1)).Pairwise (· < ·) :=
  mergeRows_keys_inc _ a.atoms b.atoms (Nat.le_refl _) a.sorted b.sorted

/-- DS14: the keys of the rows are exactly the union of the supports. -/
theorem rows_keys_mem (a b : Dist α) (k : α) : k ∈ (rows a b).map (·.1) ↔ k ∈ a.support ∨ k ∈ b.support :=
  mergeRows_keys_mem _ a.atoms b.atoms (Nat.le_refl _) k

/-- DS14: `unionSize` is the number of keys of the union of the supports (the keys of the rows are distinct). -/
theorem unionSize_eq (a b : Dist α) : unionSize a b = ((rows a b).map (·.1)).length := by
  unfold unionSize; simp

theorem mixKept_mem {lam : Prob} {a b : Dist α} {x : α × Rat} (h : x ∈ mixKept lam (rows a b)) :
    x ∈ mixW lam a b ∧ 0 < x.2 := by
  have : x ∈ (mixW lam a b).filter (fun x => decide (0 < x.2)) := h
  simpa using this

theorem mixKept_bounds (lam : Prob) (a b : Dist α) : ∀ x ∈ mixKept lam (rows a b), 0 < x.2 ∧ x.2 ≤ 1 := by
  intro x hx
  obtain ⟨h1, h2⟩ := mixKept_mem hx
  refine ⟨h2, ?_⟩
  have hnn : ∀ y ∈ (mixW lam a b).map (·.2), 0 ≤ y := fun y hy => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy; exact mixW_nonneg lam a b c hc
  have := le_sum _ hnn x.2 (List.mem_map_of_mem h1)
  rwa [mixW_sum] at this

omit [Key α] in
theorem mixAtoms_vals : ∀ L : List (α × Rat), (∀ x ∈ L, 0 ≤ x.2 ∧ x.2 ≤ 1) →
    (mixAtoms L).map (fun a => (a.1, a.2.val)) = L
  | [], _ => rfl
  | x :: L, h => by
    have ih := mixAtoms_vals L (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [mixAtoms, List.map_cons] at ih ⊢
    rw [probOf_val hx.1 hx.2, ih]

omit [Key α] in
theorem mixAtoms_of_atoms (l : List (α × Prob)) : mixAtoms (l.map (fun x => (x.1, x.2.val))) = l := by
  simp only [mixAtoms, List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x _
  exact Prod.ext rfl (Prob.ext (probOf_val x.2.nonneg x.2.le_one))

/-- The mixture's core always builds a distribution, whose atoms are the kept weights. -/
theorem mixCore_ok (lam : Prob) (a b : Dist α) :
    ∃ d : Dist α, mixCore lam a b = .ok d ∧ d.atoms = mixAtoms (mixKept lam (rows a b)) := by
  have hb := mixKept_bounds lam a b
  have hvals := mixAtoms_vals _ (fun x hx => ⟨Rat.le_of_lt (hb x hx).1, (hb x hx).2⟩)
  have hkeys : ((mixAtoms (mixKept lam (rows a b))).map (·.1)).Pairwise (· < ·) := by
    have e : (mixAtoms (mixKept lam (rows a b))).map (·.1) = (mixKept lam (rows a b)).map (·.1) := by
      simp [mixAtoms, List.map_map, Function.comp_def]
    rw [e]
    have e2 : (mixW lam a b).map (·.1) = (rows a b).map (·.1) := by
      simp [mixW, List.map_map, Function.comp_def]
    refine (rows_keys_inc a b).sublist ?_
    rw [← e2]
    exact (List.filter_sublist).map _
  have hpos : ∀ x ∈ mixAtoms (mixKept lam (rows a b)), 0 < x.2.val := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    show 0 < (probOf y.2).val
    rw [probOf_val (Rat.le_of_lt (hb y hy).1) (hb y hy).2]
    exact (hb y hy).1
  have hsum : ((mixAtoms (mixKept lam (rows a b))).map (·.2.val)).sum = 1 := by
    have := congrArg (List.map (·.2)) hvals
    simp only [List.map_map, Function.comp_def] at this
    rw [this]
    have h2 := sum_filter_pos (mixW lam a b) (mixW_nonneg lam a b)
    rw [mixW_sum] at h2
    exact h2
  refine ⟨⟨_, hkeys, hpos, hsum⟩, ?_, rfl⟩
  unfold mixCore ofAtoms
  split
  · rfl
  · next hh => exact absurd ⟨hkeys, hpos, hsum⟩ hh

theorem mixture_eq_core {lim : Limits} {lam : Prob} {a b : Dist α}
    (h1 : ¬ lim.maxBits < lam.val.bits) (h2 : ¬ lim.maxAtoms < unionSize a b) :
    mixture lim lam a b = mixCore lam a b := by
  simp [mixture, h1, h2]

/-- With the limits holding, `mixture` builds a distribution whose atoms are the kept weights. -/
theorem mixture_vals {lim : Limits} {lam : Prob} {a b : Dist α}
    (h1 : ¬ lim.maxBits < lam.val.bits) (h2 : ¬ lim.maxAtoms < unionSize a b) :
    ∃ d : Dist α, mixture lim lam a b = .ok d ∧ d.atoms = mixAtoms (mixKept lam (rows a b)) := by
  rw [mixture_eq_core h1 h2]; exact mixCore_ok lam a b

theorem mixture_atoms {lim : Limits} {lam : Prob} {a b d : Dist α} (h : mixture lim lam a b = .ok d) :
    d.atoms = mixAtoms (mixKept lam (rows a b)) := by
  by_cases h1 : lim.maxBits < lam.val.bits
  · simp [mixture, h1] at h
  · by_cases h2 : lim.maxAtoms < unionSize a b
    · simp [mixture, h1, h2] at h
    · obtain ⟨d', hd', hat⟩ := mixture_vals h1 h2
      rw [hd'] at h
      cases h
      exact hat

/-! ## DS14: the refusals -/

/-- DS14: a weight above the bit limit is refused first. -/
theorem mixture_numberTooLarge {lim : Limits} {lam : Prob} {a b : Dist α} (h : lim.maxBits < lam.val.bits) :
    mixture lim lam a b = .error (.numberTooLarge 0 lam.val.bits lim.maxBits) := by
  simp [mixture, h]

/-- DS14: given the weight passes the bit limit, `mixture` refuses `tooManyAtoms` exactly when the union of the
supports has more keys than the limit. -/
theorem mixture_tooManyAtoms_iff {lim : Limits} {lam : Prob} {a b : Dist α} (h1 : ¬ lim.maxBits < lam.val.bits) :
    mixture lim lam a b = .error (.tooManyAtoms (unionSize a b) lim.maxAtoms) ↔ lim.maxAtoms < unionSize a b := by
  constructor
  · intro h
    by_cases h2 : lim.maxAtoms < unionSize a b
    · exact h2
    · obtain ⟨d, hd, _⟩ := mixture_vals h1 h2
      rw [hd] at h; cases h
  · intro h2
    simp [mixture, h1, h2]

/-- DS14: `mixture` accepts exactly when neither limit is exceeded. -/
theorem mixture_ok_iff (lim : Limits) (lam : Prob) (a b : Dist α) :
    (∃ d : Dist α, mixture lim lam a b = .ok d) ↔ ¬ lim.maxBits < lam.val.bits ∧ ¬ lim.maxAtoms < unionSize a b := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · rw [mixture_numberTooLarge h1] at hd; cases hd
    · by_cases h1 : lim.maxBits < lam.val.bits
      · rw [mixture_numberTooLarge h1] at hd; cases hd
      · have := (mixture_tooManyAtoms_iff (a := a) (b := b) h1).mpr h2
        rw [this] at hd; cases hd
  · rintro ⟨h1, h2⟩
    obtain ⟨d, hd, _⟩ := mixture_vals h1 h2
    exact ⟨d, hd⟩

/-! ## DS11: the probability at every key -/

/-- The probability a distribution gives a key: 0 off the support. -/
def probAt [DecidableEq α] (d : Dist α) (k : α) : Rat := weightAt k (d.atoms.map (fun a => (a.1, a.2.val)))

theorem probAt_of_mem [DecidableEq α] (d : Dist α) {k : α} {p : Prob} (h : (k, p) ∈ d.atoms) : probAt d k = p.val := by
  have hk : ((d.atoms.map (fun a => (a.1, a.2.val))).map (·.1)).Pairwise (· < ·) := by
    simpa [List.map_map, Function.comp_def] using d.sorted
  exact wa_mem k p.val _ hk (List.mem_map.mpr ⟨(k, p), h, rfl⟩)

theorem probAt_of_not_mem [DecidableEq α] (d : Dist α) {k : α} (h : k ∉ d.support) : probAt d k = 0 :=
  wa_not k _ (by simpa [support, List.map_map, Function.comp_def] using h)

omit [Key α] in
theorem weightAt_filter_pos [DecidableEq α] (k : α) : ∀ L : List (α × Rat), (∀ x ∈ L, 0 ≤ x.2) →
    weightAt k (L.filter (fun x => decide (0 < x.2))) = weightAt k L
  | [], _ => rfl
  | x :: L, h => by
    have ih := weightAt_filter_pos k L (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    by_cases hz : 0 < x.2
    · simp only [List.filter_cons, hz, decide_true, ↓reduceIte, weightAt_cons, ih]
    · have h0 : x.2 = 0 := by grind
      have hd : decide (0 < x.2) = false := by simpa using hz
      simp only [List.filter_cons, hd, Bool.false_eq_true, ↓reduceIte, weightAt_cons, ih]
      rw [h0]
      split <;> simp [Rat.zero_add]

/-- DS11: at every key `k`, `d(k) = (1 - lam)·a(k) + lam·b(k)` (with 0 off the support). -/
theorem mixture_prob [DecidableEq α] {lim : Limits} {lam : Prob} {a b d : Dist α}
    (h : mixture lim lam a b = .ok d) (k : α) :
    probAt d k = (1 - lam.val) * probAt a k + lam.val * probAt b k := by
  have hat := mixture_atoms h
  have hb := mixKept_bounds lam a b
  have hvals := mixAtoms_vals _ (fun x hx => ⟨Rat.le_of_lt (hb x hx).1, (hb x hx).2⟩)
  unfold probAt
  rw [hat, hvals]
  have e1 : mixKept lam (rows a b) = (mixW lam a b).filter (fun x => decide (0 < x.2)) := rfl
  rw [e1, weightAt_filter_pos k _ (mixW_nonneg lam a b)]
  have := weightAt_mixWeight lam k (rows a b)
  unfold mixW
  rw [this]
  unfold rows
  rw [mergeRows_weightAt k _ a.atoms b.atoms (Nat.le_refl _), mergeRows_weightAt2 k _ a.atoms b.atoms (Nat.le_refl _)]

/-! ## DS13: expectation and mean -/

omit [Key α] in
theorem sum_filter_pos_f (f : α → Rat) : ∀ L : List (α × Rat), (∀ x ∈ L, 0 ≤ x.2) →
    ((L.filter (fun x => decide (0 < x.2))).map (fun x => f x.1 * x.2)).sum = (L.map (fun x => f x.1 * x.2)).sum
  | [], _ => rfl
  | x :: L, h => by
    have ih := sum_filter_pos_f f L (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    by_cases hz : 0 < x.2
    · simp only [List.filter_cons, hz, decide_true, ↓reduceIte, List.map_cons, List.sum_cons, ih]
    · have h0 : x.2 = 0 := by grind
      have hd : decide (0 < x.2) = false := by simpa using hz
      simp only [List.filter_cons, hd, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons, ih]
      rw [h0, Rat.mul_zero, Rat.zero_add]

/-- DS13: the expectation of any `f` over a mixture is the mixture of the expectations. -/
theorem mixture_expect {lim : Limits} {lam : Prob} {a b d : Dist α} (h : mixture lim lam a b = .ok d)
    (f : α → Rat) : d.expect f = (1 - lam.val) * a.expect f + lam.val * b.expect f := by
  have hat := mixture_atoms h
  have hb := mixKept_bounds lam a b
  have hvals := mixAtoms_vals _ (fun x hx => ⟨Rat.le_of_lt (hb x hx).1, (hb x hx).2⟩)
  have e : d.atoms.map (fun x => f x.1 * x.2.val)
      = (mixKept lam (rows a b)).map (fun x => f x.1 * x.2) := by
    rw [← hvals, hat, List.map_map]
    rfl
  unfold expect
  rw [e]
  have e1 : mixKept lam (rows a b) = (mixW lam a b).filter (fun x => decide (0 < x.2)) := rfl
  rw [e1, sum_filter_pos_f f _ (mixW_nonneg lam a b)]
  have e2 : (mixW lam a b).map (fun x => f x.1 * x.2) = (rows a b).map (fun r => f r.1 * mixWeight lam r.2) := by
    simp [mixW, List.map_map, Function.comp_def]
  rw [e2, sum_mixWeight]
  unfold rows
  rw [mergeRows_sum1 f _ a.atoms b.atoms (Nat.le_refl _), mergeRows_sum2 f _ a.atoms b.atoms (Nat.le_refl _)]

/-- DS13: the mean of a mixture over rational keys is the mixture of the means. -/
theorem mixture_mean {lim : Limits} {lam : Prob} {a b d : Dist Rat} (h : mixture lim lam a b = .ok d) :
    d.mean = (1 - lam.val) * a.mean + lam.val * b.mean :=
  mixture_expect h id

/-! ## DS12: the ends, symmetry and idempotence -/

/-- A mixture whose kept weights are the atoms of `c` is `c`. -/
theorem mixCore_of_kept {lam : Prob} {a b c : Dist α}
    (h : mixKept lam (rows a b) = c.atoms.map (fun x => (x.1, x.2.val))) : mixCore lam a b = .ok c := by
  obtain ⟨d, hd, hat⟩ := mixCore_ok lam a b
  rw [hd]
  congr 1
  apply Dist.ext
  rw [hat, h, mixAtoms_of_atoms]

omit [Key α] in
theorem mixWeight_zero (r : Rat × Rat) : mixWeight Prob.zero r = r.1 := by
  show (1 - (0 : Rat)) * r.1 + 0 * r.2 = r.1
  have : (1 : Rat) - 0 = 1 := by decide +kernel
  rw [this, Rat.one_mul, Rat.zero_mul, Rat.add_zero]

/-- DS12: `lam = 0` gives the first operand. -/
theorem mixCore_zero (a b : Dist α) : mixCore Prob.zero a b = .ok a := by
  apply mixCore_of_kept
  have e : (rows a b).map (fun r => (r.1, mixWeight Prob.zero r.2)) = (rows a b).map (fun r => (r.1, r.2.1)) :=
    List.map_congr_left (fun r _ => by rw [mixWeight_zero])
  show ((rows a b).map (fun r => (r.1, mixWeight Prob.zero r.2))).filter _ = _
  rw [e]
  unfold rows
  exact mergeRows_pos1 _ a.atoms b.atoms (Nat.le_refl _) a.positive

theorem mixCore_swap (lam : Prob) (a b : Dist α) : mixCore (Prob.complement lam) b a = mixCore lam a b := by
  have e : mixKept (Prob.complement lam) (rows b a) = mixKept lam (rows a b) := by
    unfold mixKept
    rw [rows_swap, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp_apply, swapRow, mixWeight, Prob.complement_val]
    rw [Prob.one_sub_one_sub, Rat.add_comm]
  unfold mixCore
  rw [e]

/-- DS12: `lam = 1` gives the second operand. -/
theorem mixCore_one (a b : Dist α) : mixCore Prob.one a b = .ok b := by
  have := mixCore_swap Prob.zero b a
  rw [Prob.complement_zero] at this
  rw [this]
  exact mixCore_zero b a

/-- DS12: mixing a distribution with itself changes nothing. -/
theorem mixCore_self (lam : Prob) (a : Dist α) : mixCore lam a a = .ok a := by
  apply mixCore_of_kept
  unfold rows
  rw [mergeRows_self _ a.atoms (by omega)]
  show ((List.map (fun a => (a.1, (a.2.val, a.2.val))) a.atoms).map (fun r => (r.1, mixWeight lam r.2))).filter _ = _
  rw [List.map_map]
  have e : ((fun r : α × (Rat × Rat) => (r.1, mixWeight lam r.2)) ∘ fun a : α × Prob => (a.1, (a.2.val, a.2.val)))
      = fun a : α × Prob => (a.1, a.2.val) := by
    funext x
    simp only [Function.comp_apply, mixWeight]
    have : (1 - lam.val) * x.2.val + lam.val * x.2.val = ((1 - lam.val) + lam.val) * x.2.val := by rw [Rat.add_mul]
    rw [this]
    have h1 : (1 - lam.val) + lam.val = 1 := by grind
    rw [h1, Rat.one_mul]
  rw [e, List.filter_eq_self]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  simpa using a.positive p hp

theorem unionSize_swap (a b : Dist α) : unionSize b a = unionSize a b := by
  unfold unionSize
  rw [rows_swap]; simp

/-- DS12 (with the limits): `lam = 0` gives `a`. -/
theorem mixture_zero {lim : Limits} {a b : Dist α}
    (h1 : ¬ lim.maxBits < Prob.zero.val.bits) (h2 : ¬ lim.maxAtoms < unionSize a b) :
    mixture lim Prob.zero a b = .ok a := by
  rw [mixture_eq_core h1 h2]; exact mixCore_zero a b

/-- DS12 (with the limits): `lam = 1` gives `b`. -/
theorem mixture_one {lim : Limits} {a b : Dist α}
    (h1 : ¬ lim.maxBits < Prob.one.val.bits) (h2 : ¬ lim.maxAtoms < unionSize a b) :
    mixture lim Prob.one a b = .ok b := by
  rw [mixture_eq_core h1 h2]; exact mixCore_one a b

/-- DS12 (with the limits): `mixture lam a b = mixture (complement lam) b a`. -/
theorem mixture_swap {lim : Limits} {lam : Prob} {a b : Dist α}
    (h1 : ¬ lim.maxBits < lam.val.bits) (h1' : ¬ lim.maxBits < (Prob.complement lam).val.bits)
    (h2 : ¬ lim.maxAtoms < unionSize a b) :
    mixture lim lam a b = mixture lim (Prob.complement lam) b a := by
  rw [mixture_eq_core h1 h2, mixture_eq_core h1' (by rw [unionSize_swap]; exact h2), mixCore_swap]

/-- DS12 (with the limits): `mixture lam a a = a`. -/
theorem mixture_self {lim : Limits} {lam : Prob} {a : Dist α}
    (h1 : ¬ lim.maxBits < lam.val.bits) (h2 : ¬ lim.maxAtoms < unionSize a a) :
    mixture lim lam a a = .ok a := by
  rw [mixture_eq_core h1 h2]; exact mixCore_self lam a

/-! ## Non-vacuity witnesses (`A`: 100 ↦ 1/4, 200 ↦ 1/2, 300 ↦ 1/4; `B`: 200 ↦ 1/2, 300 ↦ 1/2) -/

/-- The known-answer distribution `B`. -/
def distB : Dist Int where
  atoms := [(200, pr (1/2)), (300, pr (1/2))]
  sorted := by decide +kernel
  positive := by decide +kernel
  total := by decide +kernel

/-- `B` with a fourth key beyond `A`'s: 200 ↦ 1/2, 400 ↦ 1/2. -/
def distB4 : Dist Int where
  atoms := [(200, pr (1/2)), (400, pr (1/2))]
  sorted := by decide +kernel
  positive := by decide +kernel
  total := by decide +kernel

/-- `A` over rational keys. -/
def ratA : Dist Rat where
  atoms := [(100, pr (1/4)), (200, pr (1/2)), (300, pr (1/4))]
  sorted := by decide +kernel
  positive := by decide +kernel
  total := by decide +kernel

/-- `B` over rational keys. -/
def ratB : Dist Rat where
  atoms := [(200, pr (1/2)), (300, pr (1/2))]
  sorted := by decide +kernel
  positive := by decide +kernel
  total := by decide +kernel

-- DS11: `mixture 1/2 A B` is 100 ↦ 1/8, 200 ↦ 1/2, 300 ↦ 3/8; and `mixture 1/4 A B` is 3/16, 1/2, 5/16.
example : ∃ d : Dist Int, mixture Limits.default (pr (1/2)) distA distB = .ok d ∧
    d.atoms.map (fun x => (x.1, x.2.val)) = [(100, 1/8), (200, 1/2), (300, 3/8)] := by
  obtain ⟨d, hd, hat⟩ := mixture_vals (lim := Limits.default) (lam := pr (1/2)) (a := distA) (b := distB)
    (by decide +kernel) (by decide +kernel)
  refine ⟨d, hd, ?_⟩
  rw [hat]; decide +kernel

example : ∃ d : Dist Int, mixture Limits.default (pr (1/4)) distA distB = .ok d ∧
    d.atoms.map (fun x => (x.1, x.2.val)) = [(100, 3/16), (200, 1/2), (300, 5/16)] := by
  obtain ⟨d, hd, hat⟩ := mixture_vals (lim := Limits.default) (lam := pr (1/4)) (a := distA) (b := distB)
    (by decide +kernel) (by decide +kernel)
  refine ⟨d, hd, ?_⟩
  rw [hat]; decide +kernel

-- DS11, the formula at the keys 100 (off B's support), 200 and 400 (off both): 1/8, 1/2, 0.
example : ∀ d : Dist Int, mixture Limits.default (pr (1/2)) distA distB = .ok d →
    probAt d 100 = 1/8 ∧ probAt d 200 = 1/2 ∧ probAt d 400 = 0 := by
  intro d hd
  have h := mixture_prob hd
  refine ⟨?_, ?_, ?_⟩
  · rw [h 100]; decide +kernel
  · rw [h 200]; decide +kernel
  · rw [h 400]; decide +kernel

-- DS12: the ends (`lam = 0` and `lam = 1`) on A, B, under the default limits; and the symmetry and idempotence hypotheses hold.
example : mixture Limits.default Prob.zero distA distB = .ok distA :=
  mixture_zero (by decide +kernel) (by decide +kernel)
example : mixture Limits.default Prob.one distA distB = .ok distB :=
  mixture_one (by decide +kernel) (by decide +kernel)
example : mixture Limits.default (pr (1/4)) distA distB = mixture Limits.default (Prob.complement (pr (1/4))) distB distA :=
  mixture_swap (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : mixture Limits.default (pr (1/4)) distA distA = .ok distA :=
  mixture_self (by decide +kernel) (by decide +kernel)

-- DS13: A has mean 200, B has mean 250; `mixture 1/2 A B` has mean 225 and `mixture 1/4 A B` has mean 425/2.
example : ratA.mean = 200 := by decide +kernel
example : ratB.mean = 250 := by decide +kernel
example : ∀ d : Dist Rat, mixture Limits.default (pr (1/2)) ratA ratB = .ok d → d.mean = 225 := by
  intro d hd
  rw [mixture_mean hd]; decide +kernel
example : ∀ d : Dist Rat, mixture Limits.default (pr (1/4)) ratA ratB = .ok d → d.mean = 425/2 := by
  intro d hd
  rw [mixture_mean hd]; decide +kernel
-- the hypothesis of DS13 holds on these literals
example : ∃ d : Dist Rat, mixture Limits.default (pr (1/2)) ratA ratB = .ok d :=
  (mixture_ok_iff _ _ _ _).mpr ⟨by decide +kernel, by decide +kernel⟩

-- DS14: with `maxAtoms = 3`, A and B (keys inside A's) is accepted; with a fourth key it refuses `tooManyAtoms 4 3`.
example : ∃ d : Dist Int, mixture { Limits.default with maxAtoms := 3 } (pr (1/2)) distA distB = .ok d :=
  (mixture_ok_iff _ _ _ _).mpr ⟨by decide +kernel, by decide +kernel⟩
example : mixture { Limits.default with maxAtoms := 3 } (pr (1/2)) distA distB4 = .error (.tooManyAtoms 4 3) :=
  (mixture_tooManyAtoms_iff (by decide +kernel)).mpr (by decide +kernel)
-- DS14: a weight above the bit limit refuses `numberTooLarge`.
example : mixture { Limits.default with maxBits := 2 } (pr (1/2)) distA distB =
    .error (.numberTooLarge 0 (pr (1/2)).val.bits 2) :=
  mixture_numberTooLarge (by decide +kernel)

end Dist
end VbmProb
