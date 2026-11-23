import VbmProb.Dist.Query
import VbmProbProofs.Dist
import VbmProbProofs.Limits
/-! # `mass`, `expect`, `mean`, `cdf`: the properties DS6, DS7, DS10 (and the query clauses of DS3), each with its witness

All statements are about the exact `Rat` sums of `VbmProb.Dist.Query`. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

theorem add_add_add_swap (a b c d : Rat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Rat.add_assoc, ← Rat.add_assoc b c d, Rat.add_comm b c, Rat.add_assoc c b d, ← Rat.add_assoc]

/-! ## The sums over the atom list -/

omit [Key α] in
theorem massVal_true : ∀ l : List (α × Prob), massVal (fun _ => true) l = (l.map (·.2.val)).sum
  | [] => rfl
  | a :: l => by simp [massVal, massVal_true l]

omit [Key α] in
theorem massVal_false : ∀ l : List (α × Prob), massVal (fun _ => false) l = 0
  | [] => rfl
  | a :: l => by simp [massVal, massVal_false l]

omit [Key α] in
theorem massVal_congr {e e' : α → Bool} : ∀ l : List (α × Prob), (∀ a ∈ l, e a.1 = e' a.1) →
    massVal e l = massVal e' l
  | [], _ => rfl
  | a :: l, h => by
    have h1 : e a.1 = e' a.1 := h a (by simp)
    have ih := massVal_congr (e := e) (e' := e') l (fun b hb => h b (by simp [hb]))
    simp only [massVal, h1, ih]

omit [Key α] in
theorem massVal_mono {e e' : α → Bool} : ∀ l : List (α × Prob), (∀ a ∈ l, e a.1 = true → e' a.1 = true) →
    massVal e l ≤ massVal e' l
  | [], _ => Rat.le_refl
  | a :: l, h => by
    have ih := massVal_mono (e := e) (e' := e') l (fun b hb => h b (by simp [hb]))
    have h1 := h a (by simp)
    unfold massVal
    by_cases he : e a.1 = true
    · have he' := h1 he
      simp only [he, he', ite_true]
      exact Rat.add_le_add_left.mpr ih
    · have he0 : e a.1 = false := by simpa using he
      simp only [he0, Bool.false_eq_true, ite_false]
      by_cases he' : e' a.1 = true
      · simp only [he', ite_true]
        exact Rat.le_trans ih (by
          have := Rat.add_le_add_right (a := 0) (b := a.2.val) (c := massVal e' l)
          rw [Rat.zero_add] at this
          exact this.mpr a.2.nonneg)
      · have he'0 : e' a.1 = false := by simpa using he'
        simp only [he'0, Bool.false_eq_true, ite_false]
        exact ih

omit [Key α] in
theorem massVal_or {e e' : α → Bool} : ∀ l : List (α × Prob), (∀ a ∈ l, ¬ (e a.1 = true ∧ e' a.1 = true)) →
    massVal (fun x => e x || e' x) l = massVal e l + massVal e' l
  | [], _ => by simp [massVal]; decide +kernel
  | a :: l, h => by
    have ih := massVal_or (e := e) (e' := e') l (fun b hb => h b (by simp [hb]))
    have h1 := h a (by simp)
    unfold massVal
    by_cases he : e a.1 = true
    · have he' : e' a.1 = false := by
        cases hh : e' a.1
        · rfl
        · exact absurd ⟨he, hh⟩ h1
      simp only [he, he', Bool.true_or, ite_true, Bool.false_eq_true, ite_false, ih]
      rw [Rat.add_assoc]
    · have he0 : e a.1 = false := by simpa using he
      simp only [he0, Bool.false_or, Bool.false_eq_true, ite_false]
      by_cases he' : e' a.1 = true
      · simp only [he', ite_true, ih]
        rw [Rat.add_left_comm]
      · have he'0 : e' a.1 = false := by simpa using he'
        simp only [he'0, Bool.false_eq_true, ite_false, ih]

omit [Key α] in
theorem massVal_not (e : α → Bool) : ∀ l : List (α × Prob),
    massVal (fun x => !e x) l + massVal e l = (l.map (·.2.val)).sum
  | [] => by simp [massVal]; decide +kernel
  | a :: l => by
    have ih := massVal_not e l
    simp only [List.map_cons, List.sum_cons]
    unfold massVal
    by_cases he : e a.1 = true
    · simp only [he, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      rw [Rat.add_left_comm, ih]
    · have he0 : e a.1 = false := by simpa using he
      simp only [he0, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
      rw [Rat.add_assoc, ih]

/-! ## DS6: `mass` -/

/-- DS6: the certain event has mass 1. -/
theorem mass_true (d : Dist α) : d.mass (fun _ => true) = Prob.one :=
  Prob.ext (by show massVal _ d.atoms = 1; rw [massVal_true]; exact d.total)

/-- DS6: the impossible event has mass 0. -/
theorem mass_false (d : Dist α) : d.mass (fun _ => false) = Prob.zero :=
  Prob.ext (by show massVal _ d.atoms = 0; exact massVal_false _)

/-- DS6: the mass of a union of two events no atom satisfies together is the sum of their masses. -/
theorem mass_or_val (d : Dist α) (e e' : α → Bool) (h : ∀ a ∈ d.support, ¬ (e a = true ∧ e' a = true)) :
    (d.mass (fun x => e x || e' x)).val = (d.mass e).val + (d.mass e').val :=
  massVal_or d.atoms (fun a ha => h a.1 (List.mem_map_of_mem ha))

/-- DS6: for disjoint events, adding their masses succeeds and gives the mass of the union. -/
theorem mass_or (d : Dist α) (e e' : α → Bool) (h : ∀ a ∈ d.support, ¬ (e a = true ∧ e' a = true)) :
    Prob.add (d.mass e) (d.mass e') = .ok (d.mass (fun x => e x || e' x)) := by
  have hv := mass_or_val d e e' h
  have hle : (d.mass e).val + (d.mass e').val ≤ 1 := by rw [← hv]; exact (d.mass _).le_one
  unfold Prob.add
  simp only [hle, dite_true]
  exact congrArg _ (Prob.ext hv.symm)

/-- DS6: the mass of the complement event is the complement of the mass. -/
theorem mass_not (d : Dist α) (e : α → Bool) : d.mass (fun x => !e x) = Prob.complement (d.mass e) := by
  apply Prob.ext
  show massVal _ d.atoms = 1 - massVal e d.atoms
  have h := massVal_not e d.atoms
  rw [d.total] at h
  rw [← h, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

/-- The mass is a monotone function of the event. -/
theorem mass_mono (d : Dist α) {e e' : α → Bool} (h : ∀ a ∈ d.support, e a = true → e' a = true) :
    d.mass e ≤ d.mass e' :=
  massVal_mono d.atoms (fun a ha => h a.1 (List.mem_map_of_mem ha))

/-- The mass depends only on the event's values at the support. -/
theorem mass_congr (d : Dist α) {e e' : α → Bool} (h : ∀ a ∈ d.support, e a = e' a) : d.mass e = d.mass e' :=
  Prob.ext (massVal_congr d.atoms (fun a ha => h a.1 (List.mem_map_of_mem ha)))

/-! ## DS7: `cdf` -/

theorem cdf_event {x a : α} : (!decide (x < a)) = true ↔ Key.le a x := by
  simp [Key.le]

/-- DS7: the cdf is monotone. -/
theorem cdf_mono (d : Dist α) {x y : α} (h : Key.le x y) : d.cdf x ≤ d.cdf y :=
  mass_mono d (fun _ _ ha => cdf_event.mpr (Key.le_trans (cdf_event.mp ha) h))

/-- DS7: below the least key (below every key of the support) the cdf is 0. -/
theorem cdf_below (d : Dist α) {x : α} (h : ∀ a ∈ d.support, x < a) : d.cdf x = Prob.zero := by
  have : d.cdf x = d.mass (fun _ => false) :=
    mass_congr d (fun a ha => by simp [h a ha])
  rw [this, mass_false]

/-- DS7: at and above the greatest key (at or above every key of the support) the cdf is 1. -/
theorem cdf_above (d : Dist α) {x : α} (h : ∀ a ∈ d.support, Key.le a x) : d.cdf x = Prob.one := by
  have : d.cdf x = d.mass (fun _ => true) :=
    mass_congr d (fun a ha => cdf_event.mpr (h a ha))
  rw [this, mass_true]

/-- DS7: right-continuity: at `x` the cdf equals the cdf at the greatest key `k` of the support with `k ≤ x`. -/
theorem cdf_right_cont (d : Dist α) {k x : α} (hk : Key.le k x)
    (hg : ∀ a ∈ d.support, Key.le a x → Key.le a k) : d.cdf x = d.cdf k :=
  mass_congr d (fun a ha => by
    cases h1 : (!decide (x < a))
    · cases h2 : (!decide (k < a))
      · rfl
      · exact absurd (cdf_event.mpr (Key.le_trans (cdf_event.mp h2) hk)) (by simp [h1])
    · cases h2 : (!decide (k < a))
      · exact absurd (cdf_event.mpr (hg a ha (cdf_event.mp h1))) (by simp [h2])
      · rfl)

/-! ## DS10: `expect` and `mean` -/

omit [Key α] in
theorem sum_map_add (f g : α × Prob → Rat) : ∀ l : List (α × Prob),
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum
  | [] => by simp; decide +kernel
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_add f g l]; exact add_add_add_swap _ _ _ _

omit [Key α] in
theorem sum_map_mul (c : Rat) (f : α × Prob → Rat) : ∀ l : List (α × Prob),
    (l.map (fun a => c * f a)).sum = c * (l.map f).sum
  | [] => by simp
  | a :: l => by simp only [List.map_cons, List.sum_cons, sum_map_mul c f l, Rat.mul_add]

/-- DS10: `expect` is additive in the function. -/
theorem expect_add (d : Dist α) (f g : α → Rat) :
    d.expect (fun a => f a + g a) = d.expect f + d.expect g := by
  unfold expect
  rw [← sum_map_add]
  congr 1
  apply List.map_congr_left
  intro a _
  exact Rat.add_mul _ _ _

/-- DS10: `expect` commutes with a constant factor. -/
theorem expect_smul (d : Dist α) (c : Rat) (f : α → Rat) :
    d.expect (fun a => c * f a) = c * d.expect f := by
  unfold expect
  rw [← sum_map_mul]
  congr 1
  apply List.map_congr_left
  intro a _
  exact Rat.mul_assoc _ _ _

/-- DS10: the expectation of a constant is that constant. -/
theorem expect_const (d : Dist α) (c : Rat) : d.expect (fun _ => c) = c := by
  have h := sum_map_mul c (fun a => a.2.val) d.atoms
  unfold expect
  rw [h, d.total, Rat.mul_one]

omit [Key α] in
theorem sum_map_le (f g : α × Prob → Rat) : ∀ l : List (α × Prob), (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => Rat.le_refl
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have ih := sum_map_le f g l (fun b hb => h b (by simp [hb]))
    exact Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr ih)

/-- DS10: `expect` is monotone in the function (on the support). -/
theorem expect_mono (d : Dist α) {f g : α → Rat} (h : ∀ a ∈ d.support, f a ≤ g a) :
    d.expect f ≤ d.expect g :=
  sum_map_le _ _ d.atoms (fun a ha => Rat.mul_le_mul_of_nonneg_right (h a.1 (List.mem_map_of_mem ha)) a.2.nonneg)

/-- The expectation over `point a` is the value at `a`. -/
theorem expect_point (a : α) (f : α → Rat) : (point a).expect f = f a := by
  simp [expect, point, Prob.one, Rat.mul_one, Rat.add_zero]

/-- DS10 (and DS3): the mean of `point a` is `a`. -/
theorem mean_point (a : Rat) : (point a).mean = a := expect_point a id

/-- DS3: the cdf of `point a` at `x ≥ a` is 1. -/
theorem point_cdf_ge (a x : α) (h : Key.le a x) : (point a).cdf x = Prob.one :=
  cdf_above _ (by simpa [point, support] using h)

/-- DS3: the cdf of `point a` below `a` is 0. -/
theorem point_cdf_lt (a x : α) (h : x < a) : (point a).cdf x = Prob.zero :=
  cdf_below _ (by simpa [point, support] using h)

/-! ## Non-vacuity witnesses (the distribution `A`: 100 ↦ 1/4, 200 ↦ 1/2, 300 ↦ 1/4; `B`: 1/3 each at 1, 2, 3) -/

/-- The known-answer distribution `A`. -/
def distA : Dist Int where
  atoms := [(100, pr (1/4)), (200, pr (1/2)), (300, pr (1/4))]
  sorted := by decide +kernel
  positive := by decide +kernel
  total := by decide +kernel

/-- Three atoms of 1/3 at keys 1, 2, 3. -/
def distThirds : Dist Rat where
  atoms := [(1, pr (1/3)), (2, pr (1/3)), (3, pr (1/3))]
  sorted := by decide +kernel
  positive := by decide +kernel
  total := by decide +kernel

-- DS6: `e = (≥ 200)` has mass 3/4 and its negation 1/4; the whole has mass 1.
example : (distA.mass (fun k => decide (200 ≤ k))).val = 3/4 := by decide +kernel
example : (distA.mass (fun k => !decide (200 ≤ k))).val = 1/4 := by decide +kernel
example : (distA.mass (fun k => !decide (200 ≤ k))) = Prob.complement (distA.mass (fun k => decide (200 ≤ k))) :=
  mass_not _ _
-- DS6, disjoint union: `(< 200)` and `(≥ 200)` are disjoint, and their masses add up to 1; the hypothesis fails for `(≥ 100)` and `(≥ 200)`.
example : Prob.add (distA.mass (fun k => decide (k < 200))) (distA.mass (fun k => decide (200 ≤ k))) =
    .ok (distA.mass (fun k => decide (k < 200) || decide (200 ≤ k))) :=
  mass_or _ _ _ (by decide +kernel)
example : ¬ ∀ a ∈ distA.support, ¬ (decide (100 ≤ a) = true ∧ decide (200 ≤ a) = true) := by decide +kernel

-- DS7: the cdf of A at 99, 100, 150, 200, 300.
example : (distA.cdf 99).val = 0 := by decide +kernel
example : (distA.cdf 100).val = 1/4 := by decide +kernel
example : (distA.cdf 150).val = 1/4 := by decide +kernel
example : (distA.cdf 200).val = 3/4 := by decide +kernel
example : (distA.cdf 300).val = 1 := by decide +kernel
-- DS7: the hypotheses of the end clauses hold for A, and right-continuity at 150 (greatest key 100).
example : distA.cdf 99 = Prob.zero := cdf_below _ (by decide +kernel)
example : distA.cdf 1000 = Prob.one := cdf_above _ (by decide +kernel)
example : distA.cdf 150 = distA.cdf 100 :=
  cdf_right_cont _ (by decide +kernel) (by decide +kernel)
example : distA.cdf 100 ≤ distA.cdf 200 := cdf_mono _ (by decide +kernel)

-- DS10: the mean of 1/3 each at keys 1, 2, 3 is 2; the mean of `point 7` is 7; linearity and monotonicity on A.
example : distThirds.mean = 2 := by decide +kernel
example : (point (7 : Rat)).mean = 7 := mean_point 7
example : distA.expect (fun k => (k : Rat) + 1) = distA.expect (fun k => (k : Rat)) + distA.expect (fun _ => 1) :=
  expect_add _ _ _
example : distA.expect (fun _ => (3 : Rat)) = 3 := expect_const _ _
example : distA.expect (fun k => (k : Rat)) ≤ distA.expect (fun k => (k : Rat) + 1) :=
  expect_mono _ (fun a _ => by
    have := Rat.add_le_add_left (a := (0 : Rat)) (b := 1) (c := (a : Rat))
    rw [Rat.add_zero] at this
    exact this.mpr (by decide +kernel))

end Dist
end VbmProb
