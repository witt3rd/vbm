import VbmProb.Dist.Quantile
import VbmProbProofs.Dist.Query
/-! # `quantile`: the properties DS8 and DS9, each with its witness -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-! ## Two facts about a list of keys -/

omit [Key α] in
theorem list_find_split {p : α → Bool} {l : List α} {k : α} (h : l.find? p = some k) :
    ∃ as bs, l = as ++ k :: bs ∧ p k = true ∧ ∀ a ∈ as, p a = false := by
  obtain ⟨h2, as, bs, h1, h3⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨as, bs, h1, h2, fun a ha => by simpa using h3 a ha⟩

/-- A non-empty list of keys has a greatest element. -/
theorem exists_greatest : ∀ l : List α, l ≠ [] → ∃ m ∈ l, ∀ a ∈ l, Key.le a m
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun b hb => by simp at hb; subst hb; exact Key.le_refl _⟩
  | a :: b :: rest, _ => by
    obtain ⟨m, hm, hmax⟩ := exists_greatest (b :: rest) (by simp)
    rcases Key.le_total a m with h | h
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h
      · exact hmax c hc
    · refine ⟨a, by simp, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Key.le_refl _
      · exact Key.le_trans (hmax c hc) h

/-- If some key of a list is at most `x`, the greatest such key exists. -/
theorem exists_greatest_le {x : α} (l : List α) (h : ∃ a ∈ l, Key.le a x) :
    ∃ b ∈ l, Key.le b x ∧ ∀ a ∈ l, Key.le a x → Key.le a b := by
  obtain ⟨m, hm, hmax⟩ := exists_greatest (l.filter (fun a => !decide (x < a)))
    (by
      obtain ⟨a, ha, hax⟩ := h
      intro h0
      have : a ∈ l.filter (fun a => !decide (x < a)) := List.mem_filter.mpr ⟨ha, by simpa [Key.le] using hax⟩
      rw [h0] at this; simp at this)
  have hm' := List.mem_filter.mp hm
  refine ⟨m, hm'.1, by simpa [Key.le] using hm'.2, fun a ha hax => hmax a ?_⟩
  exact List.mem_filter.mpr ⟨ha, by simpa [Key.le] using hax⟩

/-! ## DS8: the quantile is total on (0, 1] -/

/-- DS8: a level at or below 0 is refused. -/
theorem quantile_levelNotPositive (d : Dist α) {q : Rat} (h : q ≤ 0) :
    d.quantile q = .error (.levelNotPositive q) := by
  simp [quantile, h]

/-- DS8: a level above 1 is refused. -/
theorem quantile_levelAboveOne (d : Dist α) {q : Rat} (h : 1 < q) :
    d.quantile q = .error (.levelAboveOne q) := by
  have : ¬ q ≤ 0 := fun h0 => Rat.not_lt.mpr (Rat.le_trans h0 (by decide +kernel)) h
  simp [quantile, this, h]

/-- The greatest key of the support has cdf 1, so the search finds a key for every level at most 1. -/
theorem find_isSome (d : Dist α) {q : Rat} (h1 : q ≤ 1) :
    ∃ k, d.support.find? (fun k => decide (q ≤ (d.cdf k).val)) = some k := by
  have hne : d.support ≠ [] := by
    have := size_pos d
    unfold size at this
    intro h0
    have : d.atoms = [] := List.map_eq_nil_iff.mp h0
    simp_all
  obtain ⟨m, hm, hmax⟩ := exists_greatest d.support hne
  have hcdf : d.cdf m = Prob.one := cdf_above d hmax
  cases hf : d.support.find? (fun k => decide (q ≤ (d.cdf k).val)) with
  | some k => exact ⟨k, rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf m hm
    rw [hcdf] at this
    exact (this (decide_eq_true h1)).elim

/-- DS8: for a level in (0, 1] the quantile is a key of the support. -/
theorem quantile_ok (d : Dist α) {q : Rat} (h0 : 0 < q) (h1 : q ≤ 1) :
    ∃ k, d.quantile q = .ok k ∧ k ∈ d.support := by
  obtain ⟨k, hk⟩ := find_isSome d h1
  refine ⟨k, ?_, List.mem_of_find?_eq_some hk⟩
  have : ¬ q ≤ 0 := Rat.not_le.mpr h0
  have h1' : ¬ 1 < q := Rat.not_lt.mpr h1
  simp [quantile, this, h1', hk]

/-- If the quantile is `k`, then `k` is the first key of the search. -/
theorem quantile_find {d : Dist α} {q : Rat} {k : α} (h : d.quantile q = .ok k) :
    d.support.find? (fun k => decide (q ≤ (d.cdf k).val)) = some k := by
  unfold quantile at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i k' hk'
        cases h
        exact hk'
      · cases h

/-- DS8: the quantile is a key of the support. -/
theorem quantile_mem {d : Dist α} {q : Rat} {k : α} (h : d.quantile q = .ok k) : k ∈ d.support :=
  List.mem_of_find?_eq_some (quantile_find h)

/-- The cdf at the quantile reaches the level. -/
theorem quantile_cdf_ge {d : Dist α} {q : Rat} {k : α} (h : d.quantile q = .ok k) : q ≤ (d.cdf k).val := by
  have := List.find?_some (quantile_find h)
  simpa using this

/-- A support key below the quantile has a cdf below the level. -/
theorem quantile_lt_support {d : Dist α} {q : Rat} {k : α} (h : d.quantile q = .ok k)
    {b : α} (hb : b ∈ d.support) (hbk : b < k) : (d.cdf b).val < q := by
  obtain ⟨as, bs, hl, _, hfail⟩ := list_find_split (quantile_find h)
  have hs : d.support.Pairwise (· < ·) := d.sorted
  rw [hl] at hb hs
  rcases List.mem_append.mp hb with hb | hb
  · have := hfail b hb
    exact Rat.not_le.mp (by simpa using this)
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact absurd hbk (Key.lt_irrefl _)
    · have := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 b hb
      exact absurd hbk (Key.lt_asymm this)

/-! ## DS9: the Galois property -/

/-- DS9: for `0 < q ≤ 1` and `quantile d q = .ok k`, for every `x` (a key or not), `q ≤ cdf d x ↔ k ≤ x`. -/
theorem quantile_galois (d : Dist α) {q : Rat} (h0 : 0 < q) {k : α} (hk : d.quantile q = .ok k) (x : α) :
    q ≤ (d.cdf x).val ↔ Key.le k x := by
  constructor
  · intro hq
    refine Classical.byContradiction (fun hkx => ?_)
    have hxk : x < k := Decidable.of_not_not hkx
    by_cases hex : ∃ a ∈ d.support, Key.le a x
    · obtain ⟨b, hb, hbx, hgr⟩ := exists_greatest_le d.support hex
      have hbk : b < k := by
        rcases Key.le_iff.mp hbx with h | h
        · exact Key.lt_trans h hxk
        · exact h ▸ hxk
      have hc : d.cdf x = d.cdf b := cdf_right_cont d hbx (fun a ha hax => hgr a ha hax)
      rw [hc] at hq
      exact absurd (quantile_lt_support hk hb hbk) (Rat.not_lt.mpr hq)
    · have hz : d.cdf x = Prob.zero :=
        cdf_below d (fun a ha => Decidable.of_not_not (fun h => hex ⟨a, ha, h⟩))
      rw [hz] at hq
      exact absurd h0 (Rat.not_lt.mpr (by simpa [Prob.zero] using hq))
  · intro hkx
    exact Rat.le_trans (quantile_cdf_ge hk) (cdf_mono d hkx)

/-- DS9: `x < k` implies `cdf x < q`. -/
theorem quantile_cdf_lt (d : Dist α) {q : Rat} (h0 : 0 < q) {k : α} (hk : d.quantile q = .ok k) {x : α}
    (hx : x < k) : (d.cdf x).val < q :=
  Rat.not_le.mp (fun h => (quantile_galois d h0 hk x).mp h hx)

/-- DS9: the quantile is the smallest key of the support whose cdf reaches the level. -/
theorem quantile_least (d : Dist α) {q : Rat} (h0 : 0 < q) {k : α} (hk : d.quantile q = .ok k) {a : α}
    (hq : q ≤ (d.cdf a).val) : Key.le k a :=
  (quantile_galois d h0 hk a).mp hq

/-- DS9: the quantile is monotone in the level. -/
theorem quantile_mono (d : Dist α) {q q' : Rat} (h0 : 0 < q) (hle : q ≤ q') {k k' : α}
    (hk : d.quantile q = .ok k) (hk' : d.quantile q' = .ok k') : Key.le k k' :=
  (quantile_galois d h0 hk k').mp (Rat.le_trans hle (quantile_cdf_ge hk'))

/-! ## Non-vacuity witnesses (A: 100 ↦ 1/4, 200 ↦ 1/2, 300 ↦ 1/4) -/

/-- A quantile given as an `Option` (a decidable form for witnesses) is the quantile. -/
theorem quantile_of_toOption {d : Dist α} {q : Rat} {k : α} (h : (d.quantile q).toOption = some k) :
    d.quantile q = .ok k := by
  cases h' : d.quantile q <;> simp_all [Except.toOption]

-- DS8: A at q = 1 gives 300; q = 0 and q = 11/10 refuse.
example : distA.quantile 1 = .ok 300 := quantile_of_toOption (by decide +kernel)
example : distA.quantile 0 = .error (.levelNotPositive 0) := quantile_levelNotPositive _ (by decide +kernel)
example : distA.quantile (11/10) = .error (.levelAboveOne (11/10)) := quantile_levelAboveOne _ (by decide +kernel)
example : ∃ k, distA.quantile (1/2) = .ok k ∧ k ∈ distA.support := quantile_ok _ (by decide +kernel) (by decide +kernel)

-- DS9: A at q = 1/4 gives 100 (cdf 100 = 1/4 ≥ q, cdf 99 = 0 < q); q = 1/3 gives 200 (q strictly between two cdf values).
example : distA.quantile (1/4) = .ok 100 := quantile_of_toOption (by decide +kernel)
example : distA.quantile (1/3) = .ok 200 := quantile_of_toOption (by decide +kernel)
example : distA.quantile (3/4) = .ok 200 := quantile_of_toOption (by decide +kernel)
example : distA.quantile (4/5) = .ok 300 := quantile_of_toOption (by decide +kernel)
example : distA.quantile (1/1000) = .ok 100 := quantile_of_toOption (by decide +kernel)
example : (distA.cdf 100).val = 1/4 ∧ (distA.cdf 99).val < 1/4 := by decide +kernel
-- the Galois property at a non-key (150) and below the quantile (99), instantiated.
example : (1/3 : Rat) ≤ (distA.cdf 250).val ↔ Key.le (200 : Int) 250 :=
  quantile_galois distA (by decide +kernel) (k := 200) (quantile_of_toOption (by decide +kernel)) 250
example : (distA.cdf 150).val < 1/3 := quantile_cdf_lt distA (by decide +kernel) (k := 200) (quantile_of_toOption (by decide +kernel)) (by decide +kernel)
example : Key.le (100 : Int) 200 :=
  quantile_mono distA (q := 1/4) (q' := 1/3) (by decide +kernel) (by decide +kernel) (k := 100) (k' := 200)
    (quantile_of_toOption (by decide +kernel)) (quantile_of_toOption (by decide +kernel))

end Dist
end VbmProb
