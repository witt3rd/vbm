import VbmProb.Dist.Condition
import VbmProbProofs.Dist.Map
/-! # `condition`: the property DS17, with its witnesses

`eventW` sums to the mass of the event, so when that mass is not 0 the division step `normCore` succeeds and its atoms are the kept atoms over the mass (`condition_vals`). The mass of any event under the result is the mass of the conjunction over the mass of the conditioning event (`mass_condition`); conditioning twice is conditioning on the conjunction. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

omit [Key α] in
theorem eventW_sum (e : α → Bool) : ∀ l : List (α × Prob),
    ((((l.filter (fun a => e a.1)).map (fun a => (a.1, a.2.val)))).map (·.2)).sum = massVal e l
  | [] => rfl
  | a :: l => by
    have ih := eventW_sum e l
    by_cases h : e a.1 = true
    · simp only [List.filter_cons, h, ite_true, massVal, List.map_cons, List.sum_cons, ih]
    · simp only [List.filter_cons, h, massVal]
      simpa [h] using ih

theorem eventW_pos (d : Dist α) (e : α → Bool) : ∀ a ∈ eventW d e, 0 < a.2 := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact d.positive b (List.mem_filter.mp hb).1

theorem eventW_keys (d : Dist α) (e : α → Bool) : ((eventW d e).map (·.1)).Pairwise (· < ·) := by
  have : (eventW d e).map (·.1) = (d.atoms.filter (fun a => e a.1)).map (·.1) := by
    simp [eventW, List.map_map, Function.comp_def]
  rw [this]
  exact d.sorted.sublist ((List.filter_sublist).map _)

theorem normWeights_eventW (d : Dist α) (e : α → Bool) : normWeights (eventW d e) = eventW d e := by
  unfold normWeights
  rw [canon_of_increasing _ (eventW_keys d e), List.filter_eq_self]
  intro a ha; simpa using eventW_pos d e a ha

theorem eventW_sum' (d : Dist α) (e : α → Bool) : ((eventW d e).map (·.2)).sum = (d.mass e).val :=
  eventW_sum e d.atoms

theorem eventW_ne (d : Dist α) (e : α → Bool) (h : (d.mass e).val ≠ 0) : eventW d e ≠ [] := by
  intro he
  apply h
  rw [← eventW_sum', he]
  rfl

/-- DS17, the refusal: an event of probability 0 gives `nullEvent`. -/
theorem condition_nullEvent {d : Dist α} {e : α → Bool} (h : (d.mass e).val = 0) :
    condition d e = .error .nullEvent := by
  simp [condition, h]

/-- DS17, acceptance: when the event has non-zero mass, `condition` succeeds, and its atoms are the kept atoms over the mass. -/
theorem condition_core {d : Dist α} {e : α → Bool} (h : (d.mass e).val ≠ 0) :
    ∃ d' : Dist α, condition d e = .ok d' ∧ d'.atoms = normAtoms (eventW d e) := by
  obtain ⟨r, hr, hat⟩ := ofAtoms_normAtoms (eventW_ne d e h) (eventW_pos d e) (eventW_keys d e)
  refine ⟨r, ?_, hat⟩
  have hn := normWeights_eventW d e
  simp [condition, h, normCore, hn, eventW_ne d e h, hr]

/-- DS17: `condition d e` succeeds exactly when the event has non-zero mass. -/
theorem condition_ok_iff (d : Dist α) (e : α → Bool) :
    (∃ d' : Dist α, condition d e = .ok d') ↔ (d.mass e).val ≠ 0 := by
  constructor
  · rintro ⟨d', hd⟩ h
    rw [condition_nullEvent h] at hd; cases hd
  · intro h
    obtain ⟨d', hd, -⟩ := condition_core h
    exact ⟨d', hd⟩

/-- DS17: the atoms of the result, as plain pairs: the atoms satisfying `e`, each probability over the mass. -/
theorem condition_vals {d d' : Dist α} {e : α → Bool} (hd : condition d e = .ok d') :
    d'.atoms.map vals = (d.atoms.filter (fun a => e a.1)).map (fun a => (a.1, a.2.val / (d.mass e).val)) := by
  have h : (d.mass e).val ≠ 0 := fun h => by
    rw [condition_nullEvent h] at hd; cases hd
  obtain ⟨r, hr, hat⟩ := condition_core h
  rw [hr] at hd
  cases hd
  rw [hat]
  unfold normAtoms
  have hs := eventW_sum' d e
  rw [List.map_map, hs]
  unfold eventW
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  have hb := div_bounds (eventW_pos d e) (b := (a.1, a.2.val)) (List.mem_map_of_mem ha)
  rw [hs] at hb
  simp only [Function.comp_apply, vals]
  rw [probOf_val (Rat.le_of_lt hb.1) hb.2]

/-- DS17: the probability at a key with `e k` is `d(k) / mass d e`, and no other key is present. -/
theorem condition_mem {d d' : Dist α} {e : α → Bool} (hd : condition d e = .ok d') (k : α) (q : Rat) :
    (k, q) ∈ d'.atoms.map vals ↔ ∃ p ∈ d.atoms, e p.1 = true ∧ p.1 = k ∧ q = p.2.val / (d.mass e).val := by
  rw [condition_vals hd]
  constructor
  · intro h
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
    simp only [Prod.mk.injEq] at hpe
    exact ⟨p, hp1, hp2, hpe.1, hpe.2.symm⟩
  · rintro ⟨p, hp, he, rfl, rfl⟩
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, he⟩, rfl⟩

omit [Key α] in
theorem gsum_cond (e e' : α → Bool) (m : Rat) : ∀ l : List (α × Prob),
    gsum (ev e') ((l.filter (fun a => e a.1)).map (fun a => (a.1, a.2.val / m))) =
      massVal (fun x => e x && e' x) l / m
  | [] => by simp [gsum, massVal, Rat.div_def, Rat.zero_mul]
  | a :: l => by
    have ih := gsum_cond e e' m l
    by_cases h : e a.1 = true
    · by_cases h' : e' a.1 = true
      · simp only [List.filter_cons, h, ite_true, List.map_cons, gsum_cons, ev, h', massVal,
          Bool.and_self, Rat.one_mul]
        rw [ih, Rat.div_def, Rat.div_def, Rat.div_def, Rat.add_mul]
      · simp only [List.filter_cons, h, ite_true, List.map_cons, gsum_cons, ev, massVal]
        simp [h']
        rw [Rat.zero_add]; exact ih
    · simp only [List.filter_cons, h, massVal]
      simpa using ih

/-- DS17: the mass of any event `e'` under the result is the mass of `e ∧ e'` over the mass of `e`. -/
theorem mass_condition {d d' : Dist α} {e : α → Bool} (hd : condition d e = .ok d') (e' : α → Bool) :
    (d'.mass e').val = (d.mass (fun x => e x && e' x)).val / (d.mass e).val := by
  rw [mass_val_expect, expect_eq_gsum, condition_vals hd]
  exact gsum_cond e e' _ d.atoms

/-- DS17: the result gives the event probability one. -/
theorem mass_condition_self {d d' : Dist α} {e : α → Bool} (hd : condition d e = .ok d') : d'.mass e = Prob.one := by
  have h : (d.mass e).val ≠ 0 := fun h => by
    rw [condition_nullEvent h] at hd; cases hd
  apply Prob.ext
  rw [mass_condition hd]
  have : d.mass (fun x => e x && e x) = d.mass e := by
    congr 1; funext x; exact Bool.and_self _
  rw [this, Rat.div_def, Rat.mul_inv_cancel _ h]
  rfl

/-- DS17: conditioning on the whole space changes nothing. -/
theorem condition_true (d : Dist α) : condition d (fun _ => true) = .ok d := by
  have h : (d.mass (fun _ => true)).val ≠ 0 := by
    rw [mass_true]; decide +kernel
  obtain ⟨d', hd, -⟩ := condition_core h
  rw [hd]
  congr 1
  apply Dist.ext
  apply vals_inj
  rw [condition_vals hd, mass_true]
  rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
  have e1 : Prob.one.val = 1 := rfl
  rw [e1]
  conv => rhs; rw [← List.map_id (d.atoms.map vals)]
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  have e : (1 : Rat)⁻¹ = 1 := by decide +kernel
  simp [vals, Rat.div_def, e]

/-- DS17: conditioning on `e` and then on `e'` is conditioning on `e ∧ e'` (including the refusals). -/
theorem condition_condition {d d' : Dist α} {e : α → Bool} (hd : condition d e = .ok d') (e' : α → Bool) :
    condition d' e' = condition d (fun x => e x && e' x) := by
  have hm : (d.mass e).val ≠ 0 := fun h => by
    rw [condition_nullEvent h] at hd; cases hd
  have hmass := mass_condition hd e'
  by_cases h2 : (d.mass (fun x => e x && e' x)).val = 0
  · rw [condition_nullEvent h2, condition_nullEvent]
    rw [hmass, h2, Rat.div_def, Rat.zero_mul]
  · have h2' : (d'.mass e').val ≠ 0 := by
      rw [hmass, Rat.div_def]
      intro h
      have := Rat.mul_inv_cancel _ hm
      apply h2
      have h3 : (d.mass (fun x => e x && e' x)).val * (d.mass e).val⁻¹ * (d.mass e).val = 0 := by rw [h, Rat.zero_mul]
      rw [Rat.mul_assoc, Rat.mul_comm ((d.mass e).val⁻¹), this, Rat.mul_one] at h3
      exact h3
    obtain ⟨d2, hd2, -⟩ := condition_core h2'
    obtain ⟨d3, hd3, -⟩ := condition_core h2
    rw [hd2, hd3]
    congr 1
    apply Dist.ext
    apply vals_inj
    rw [condition_vals hd2, condition_vals hd3]
    have hc : ∀ v : Rat, v / (d.mass e).val / (d'.mass e').val = v / (d.mass fun x => e x && e' x).val := by
      intro v
      have hi : (d.mass e).val⁻¹ * (d.mass e).val = 1 := by rw [Rat.mul_comm]; exact Rat.mul_inv_cancel _ hm
      rw [hmass, Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.mul_assoc v,
        ← Rat.mul_assoc _ (d.mass e).val, hi, Rat.one_mul]
      rfl
    have h1 : (d'.atoms.filter (fun a => e' a.1)).map vals = (d'.atoms.map vals).filter (fun a => e' a.1) := by
      rw [List.filter_map]; rfl
    have h2 : ((d'.atoms.map vals).filter (fun a => e' a.1)) =
        ((d.atoms.filter (fun a => e a.1 && e' a.1)).map (fun a => (a.1, a.2.val / (d.mass e).val))) := by
      rw [condition_vals hd, List.filter_map, List.filter_filter]
      congr 1
      apply List.filter_congr
      intro a _
      simp [Function.comp, Bool.and_comm]
    have h3 : ∀ (l : List (α × Prob)) (m : Rat), (l.map vals).map (fun a => (a.1, a.2 / m)) =
        l.map (fun a => (a.1, a.2.val / m)) := fun l m => by rw [List.map_map]; rfl
    rw [← h3, h1, h2, List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply]
    rw [hc]

/-! ## Witnesses -/

/-- W (DS17): `A` on `(≥ 200)` gives 200 with 2/3 and 300 with 1/3. -/
example : ∃ d' : Dist Int, condition distA (fun k => decide (200 ≤ k)) = .ok d' ∧
    d'.atoms.map vals = [(200, 2/3), (300, 1/3)] := by
  obtain ⟨d', hd, -⟩ := condition_core (d := distA) (e := fun k => decide (200 ≤ k)) (by decide +kernel)
  refine ⟨d', hd, ?_⟩
  rw [condition_vals hd]
  decide +kernel

/-- W (DS17): the hypothesis fails for `(> 300)`: the event has mass 0 and `condition` refuses `nullEvent`. -/
example : condition distA (fun k => decide (300 < k)) = .error .nullEvent :=
  condition_nullEvent (by decide +kernel)

/-- W (DS17): the result gives the event mass one, and `mass d' e' = mass d (e ∧ e') / mass d e`
(here `e' = (≤ 200)`: 1/2 over 3/4 is 2/3). -/
example : ∃ d' : Dist Int, condition distA (fun k => decide (200 ≤ k)) = .ok d' ∧
    d'.mass (fun k => decide (200 ≤ k)) = Prob.one ∧ (d'.mass (fun k => decide (k ≤ 200))).val = 2/3 := by
  obtain ⟨d', hd, -⟩ := condition_core (d := distA) (e := fun k => decide (200 ≤ k)) (by decide +kernel)
  refine ⟨d', hd, mass_condition_self hd, ?_⟩
  rw [mass_condition hd]
  decide +kernel

/-- W (DS17): conditioning on the whole space changes nothing. -/
example : condition distA (fun _ => true) = .ok distA := condition_true _

/-- W (DS17): conditioning twice (`≥ 200` then `≤ 200`) is conditioning on both: the point at 200 (the result
of `condition d (≥ 200 ∧ ≤ 200)` has the one atom `(200, 1)`). -/
example : ∃ d' d'' : Dist Int, condition distA (fun k => decide (200 ≤ k)) = .ok d' ∧
    condition d' (fun k => decide (k ≤ 200)) = .ok d'' ∧
    condition distA (fun k => decide (200 ≤ k) && decide (k ≤ 200)) = .ok d'' ∧ d''.atoms.map vals = [(200, 1)] := by
  obtain ⟨d', hd, -⟩ := condition_core (d := distA) (e := fun k => decide (200 ≤ k)) (by decide +kernel)
  have h2 := condition_condition hd (fun k => decide (k ≤ 200))
  obtain ⟨d'', hd'', -⟩ := condition_core (d := distA) (e := fun k => decide (200 ≤ k) && decide (k ≤ 200))
    (by decide +kernel)
  refine ⟨d', d'', hd, by rw [h2]; exact hd'', hd'', ?_⟩
  rw [condition_vals hd'']
  decide +kernel

/-- W (DS17): the pointwise reading: the key 300 is present with probability `(1/4) / (3/4) = 1/3`, and 100 is absent. -/
example : ∃ d' : Dist Int, condition distA (fun k => decide (200 ≤ k)) = .ok d' ∧
    ((300, (1/3 : Rat)) ∈ d'.atoms.map vals) ∧ ¬ ((100, (1/3 : Rat)) ∈ d'.atoms.map vals) := by
  obtain ⟨d', hd, -⟩ := condition_core (d := distA) (e := fun k => decide (200 ≤ k)) (by decide +kernel)
  refine ⟨d', hd, ?_, ?_⟩ <;> rw [condition_vals hd] <;> decide +kernel

end Dist
end VbmProb
