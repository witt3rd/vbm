import VbmProb.Apportion
/-! # Apportionment: the properties FX8 to FX12, each with its witness

The proofs are about every input (never by evaluation); only the witnesses evaluate, and those that sort do so by `simp` through `List.mergeSort` (`docs/spec.md`, "Core first"). -/
namespace VbmProb
namespace Apportion

/-! ## Sums over a list of indices -/

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_mul {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map fun x => f x * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem sum_map_le {α : Type} (l : List α) (f : α → Nat) (c : Nat) (h : ∀ x ∈ l, f x ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem sum_map_zero {α : Type} (l : List α) (f : α → Nat) (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The weights read back by index are the weights. -/
theorem map_getD_range (ws : List Nat) : (List.range ws.length).map (fun i => ws.getD i 0) = ws := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [List.getElem?_eq_getElem h1]

/-- A sum over the indices of a function of the weight is the sum over the weights. -/
theorem sum_range_getD (ws : List Nat) (g : Nat → Nat) :
    ((List.range ws.length).map fun i => g (ws.getD i 0)).sum = (ws.map g).sum := by
  have := congrArg (List.map g) (map_getD_range ws)
  rw [List.map_map] at this
  exact congrArg List.sum this

/-- A sum of indicators over a list is the length of the filter. -/
theorem sum_ite_eq_length_filter (l : List Nat) (p : Nat → Prop) [DecidablePred p] :
    (l.map fun x => if p x then 1 else 0).sum = (l.filter fun x => decide (p x)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih] <;> omega

/-- The indicators of a duplicate-free list inside the indices sum to its length. -/
theorem sum_indicator (m : Nat) (l : List Nat) (hn : l.Nodup) (hm : ∀ i ∈ l, i < m) :
    ((List.range m).map fun i => if i ∈ l then 1 else 0).sum = l.length := by
  rw [sum_ite_eq_length_filter]
  have : ((List.range m).filter fun i => decide (i ∈ l)).Perm l := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hn]
    intro a
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hm a h, h⟩⟩
  exact this.length_eq

/-! ## The award order -/

theorem before_total (r : Nat → Nat) (a b : Nat) : (before r a b || before r b a) = true := by
  simp only [before]; simp; omega

theorem before_trans (r : Nat → Nat) (a b c : Nat) (h1 : before r a b = true) (h2 : before r b c = true) :
    before r a c = true := by
  simp only [before] at *; simp at *; omega

theorem order_perm (n : Nat) (ws : List Nat) : (order n ws).Perm (List.range ws.length) :=
  List.mergeSort_perm _ _

theorem order_nodup (n : Nat) (ws : List Nat) : (order n ws).Nodup :=
  (order_perm n ws).nodup_iff.mpr List.nodup_range

theorem order_length (n : Nat) (ws : List Nat) : (order n ws).length = ws.length := by
  simpa using (order_perm n ws).length_eq

theorem order_mem {n : Nat} {ws : List Nat} {i : Nat} (h : i ∈ order n ws) : i < ws.length := by
  simpa using (order_perm n ws).subset h

theorem mem_order {n : Nat} {ws : List Nat} {i : Nat} (h : i < ws.length) : i ∈ order n ws :=
  (order_perm n ws).symm.subset (List.mem_range.mpr h)

theorem order_pairwise (n : Nat) (ws : List Nat) :
    (order n ws).Pairwise (fun a b => before (remAt n ws) a b = true) :=
  List.pairwise_mergeSort (before_trans _) (before_total _) _

/-- Earlier in the award order means a remainder at least as large. -/
theorem before_rem {r : Nat → Nat} {a b : Nat} (h : before r a b = true) : r b ≤ r a := by
  simp only [before] at h; simp at h; omega

theorem chosen_nodup (n : Nat) (ws : List Nat) : (chosen n ws).Nodup :=
  (order_nodup n ws).sublist (List.take_sublist _ _)

theorem chosen_mem {n : Nat} {ws : List Nat} {i : Nat} (h : i ∈ chosen n ws) : i < ws.length :=
  order_mem (List.mem_of_mem_take h)

/-! ## The arithmetic of the shares -/

theorem floor_add_rem (n : Nat) (ws : List Nat) (i : Nat) :
    floorAt n ws i * ws.sum + remAt n ws i = ws.getD i 0 * n := by
  unfold floorAt remAt
  rw [Nat.mul_comm]; exact Nat.div_add_mod _ _

/-- The floors and the remainders together are `n · W`. -/
theorem sum_floor_rem (n : Nat) (ws : List Nat) :
    ((List.range ws.length).map (floorAt n ws)).sum * ws.sum + ((List.range ws.length).map (remAt n ws)).sum
      = ws.sum * n := by
  have h1 : ((List.range ws.length).map fun i => floorAt n ws i * ws.sum + remAt n ws i).sum
      = ((List.range ws.length).map fun i => ws.getD i 0 * n).sum :=
    congrArg List.sum (List.map_congr_left fun i _ => floor_add_rem n ws i)
  rw [sum_map_add, sum_map_mul] at h1
  rw [h1]
  have h2 : ((List.range ws.length).map fun i => ws.getD i 0 * n).sum = (ws.map fun w => w * n).sum :=
    sum_range_getD ws (fun w => w * n)
  have h3 : (ws.map fun w => w * n).sum = ws.sum * n := by simpa using sum_map_mul ws id n
  rw [h2, h3]

theorem floors_le (n : Nat) (ws : List Nat) (hW : 0 < ws.sum) :
    ((List.range ws.length).map (floorAt n ws)).sum ≤ n := by
  have h := sum_floor_rem n ws
  rw [Nat.mul_comm ws.sum n] at h
  have : ((List.range ws.length).map (floorAt n ws)).sum * ws.sum ≤ n * ws.sum := by omega
  exact Nat.le_of_mul_le_mul_right this hW

theorem extra_mul (n : Nat) (ws : List Nat) (hW : 0 < ws.sum) :
    extra n ws * ws.sum = ((List.range ws.length).map (remAt n ws)).sum := by
  have h := sum_floor_rem n ws
  have hF := floors_le n ws hW
  unfold extra
  rw [Nat.sub_mul]
  rw [Nat.mul_comm ws.sum n] at h
  generalize ((List.range ws.length).map (floorAt n ws)).sum = F at *
  generalize ((List.range ws.length).map (remAt n ws)).sum = R at *
  generalize F * ws.sum = x at *
  generalize n * ws.sum = y at *
  omega

theorem extra_le (n : Nat) (ws : List Nat) (hW : 0 < ws.sum) : extra n ws ≤ ws.length := by
  have h := extra_mul n ws hW
  have hb := sum_map_le (List.range ws.length) (remAt n ws) ws.sum
    (fun i _ => Nat.le_of_lt (Nat.mod_lt _ hW))
  rw [List.length_range] at hb
  exact Nat.le_of_mul_le_mul_right (by omega) hW

theorem chosen_length (n : Nat) (ws : List Nat) (hW : 0 < ws.sum) : (chosen n ws).length = extra n ws := by
  unfold chosen
  rw [List.length_take, order_length]
  exact Nat.min_eq_left (extra_le n ws hW)

/-- The chosen indices and the rest of the award order split the indices. -/
theorem order_split (n : Nat) (ws : List Nat) : order n ws = chosen n ws ++ (order n ws).drop (extra n ws) :=
  (List.take_append_drop _ _).symm

/-- Every chosen index has a positive remainder. -/
theorem chosen_rem_pos (n : Nat) (ws : List Nat) (hW : 0 < ws.sum) {i : Nat} (hi : i ∈ chosen n ws) :
    0 < remAt n ws i := by
  apply Nat.pos_of_ne_zero
  intro h0
  have hk := extra_mul n ws hW
  have hlen := chosen_length n ws hW
  have hpos : 0 < extra n ws := by
    rw [← hlen]; exact List.length_pos_of_mem hi
  have hp := order_pairwise n ws
  rw [order_split n ws, List.pairwise_append] at hp
  have hdrop : (((order n ws).drop (extra n ws)).map (remAt n ws)).sum = 0 :=
    sum_map_zero _ _ fun b hb => by
      have := before_rem (hp.2.2 i hi b hb); omega
  have hR : ((List.range ws.length).map (remAt n ws)).sum
      = ((chosen n ws).map (remAt n ws)).sum + (((order n ws).drop (extra n ws)).map (remAt n ws)).sum := by
    have hperm := ((order_perm n ws).map (remAt n ws)).sum_nat
    rw [← hperm, order_split n ws]
    simp only [List.map_append, List.sum_append]
    rw [← order_split n ws]
  have hb := sum_map_le (chosen n ws) (remAt n ws) (ws.sum - 1) fun j _ => by
    have := Nat.mod_lt (ws.getD j 0 * n) hW; unfold remAt; omega
  rw [hlen] at hb
  have e : extra n ws * (ws.sum - 1) + extra n ws = extra n ws * ws.sum := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

/-- The arithmetic of FX9 for one index: the floor `F`, the remainder `r` and one more unit exactly when `r > 0`. -/
theorem within_one_arith (F W r y b : Nat) (e : F * W + r = y) (hr : r < W) (hb : b = 0 ∨ (b = 1 ∧ 0 < r)) :
    -(W : Int) < ((F + b : Nat) : Int) * W - y ∧ ((F + b : Nat) : Int) * W - y < W := by
  have e' : ((F : Int) * W + r) = y := by exact_mod_cast e
  have h1 : (((F + b : Nat) : Int)) * W = (F : Int) * W + (b : Int) * W := by push_cast; exact Int.add_mul _ _ _
  rcases hb with hb | ⟨hb, hp⟩
  · subst hb; rw [h1]; simp; omega
  · subst hb; rw [h1]; simp; omega

/-! ## The result, index by index -/

theorem units_length (n : Nat) (ws : List Nat) : (units n ws).length = ws.length := by simp [units]

theorem units_getElem? (n : Nat) (ws : List Nat) {i : Nat} (h : i < ws.length) :
    (units n ws)[i]? = some (floorAt n ws i + if i ∈ chosen n ws then 1 else 0) := by
  simp [units, List.getElem?_range h]

theorem units_sum (n : Nat) (ws : List Nat) (hW : 0 < ws.sum) : (units n ws).sum = n := by
  unfold units
  rw [sum_map_add, sum_indicator ws.length _ (chosen_nodup n ws) fun i hi => chosen_mem hi, chosen_length n ws hW]
  have := floors_le n ws hW
  unfold extra at *
  omega

end Apportion

/-- Evaluate `apportion` on a small literal: the sort goes through `List.mergeSort` by `simp`. -/
local macro "apportion_eval" : tactic =>
  `(tactic| simp [VbmProb.apportion, VbmProb.Apportion.units, VbmProb.Apportion.floorAt, VbmProb.Apportion.chosen, VbmProb.Apportion.order,
    VbmProb.Apportion.extra, VbmProb.Apportion.before, VbmProb.Apportion.remAt, List.mergeSort, List.range_succ])

/-! ## FX8: the sum and the length -/

/-- FX8: an accepted apportionment sums to the scale and has the length of the weights. -/
theorem apportion_sum {n : Nat} {ws vs : List Nat} (h : apportion n ws = .ok vs) :
    vs.sum = n ∧ vs.length = ws.length := by
  unfold apportion at h
  by_cases hz : ws.sum = 0
  · simp [hz] at h
  · simp only [hz, ite_false, Except.ok.injEq] at h
    subst h
    exact ⟨Apportion.units_sum n ws (Nat.pos_of_ne_zero hz), Apportion.units_length n ws⟩

-- Non-vacuity witness for FX8: scale 10, `[1,1,1]` gives `[4,3,3]` (sum 10).
theorem apportion_ten_ones : apportion 10 [1, 1, 1] = .ok [4, 3, 3] := by
  apportion_eval
example : ∃ vs, apportion 10 [1, 1, 1] = .ok vs ∧ vs.sum = 10 ∧ vs.length = 3 :=
  ⟨_, apportion_ten_ones, by decide⟩
example : (apportion_sum apportion_ten_ones).1 = (rfl : [4, 3, 3].sum = 10) := rfl

/-! ## FX9: within one unit -/

/-- FX9: every unit count is within one unit of the exact proportion: `−W < vsᵢ·W − wsᵢ·n < W`. -/
theorem apportion_within_one {n : Nat} {ws vs : List Nat} (h : apportion n ws = .ok vs) {i v : Nat}
    (hv : vs[i]? = some v) :
    -(ws.sum : Int) < (v : Int) * ws.sum - (ws.getD i 0 : Int) * n ∧
      (v : Int) * ws.sum - (ws.getD i 0 : Int) * n < ws.sum := by
  unfold apportion at h
  by_cases hz : ws.sum = 0
  · simp [hz] at h
  · simp only [hz, ite_false, Except.ok.injEq] at h
    subst h
    have hW := Nat.pos_of_ne_zero hz
    have hi : i < ws.length := by
      by_cases hc : i < ws.length
      · exact hc
      · rw [List.getElem?_eq_none (by rw [Apportion.units_length]; omega)] at hv
        cases hv
    rw [Apportion.units_getElem? n ws hi] at hv
    have hv := Option.some.inj hv
    have e := Apportion.floor_add_rem n ws i
    have hr : Apportion.remAt n ws i < ws.sum := Nat.mod_lt _ hW
    subst hv
    by_cases hc : i ∈ Apportion.chosen n ws
    · have hp := Apportion.chosen_rem_pos n ws hW hc
      simp only [hc, ite_true]
      exact Apportion.within_one_arith _ _ _ _ 1 e hr (Or.inr ⟨rfl, hp⟩)
    · simp only [hc, ite_false]
      exact Apportion.within_one_arith _ _ _ _ 0 e hr (Or.inl rfl)

/-- FX9: a zero weight gets zero units. -/
theorem apportion_zero_weight {n : Nat} {ws vs : List Nat} (h : apportion n ws = .ok vs) {i v : Nat}
    (hv : vs[i]? = some v) (hw : ws.getD i 0 = 0) : v = 0 := by
  unfold apportion at h
  by_cases hz : ws.sum = 0
  · simp [hz] at h
  · simp only [hz, ite_false, Except.ok.injEq] at h
    subst h
    have hW := Nat.pos_of_ne_zero hz
    have hi : i < ws.length := by
      by_cases hc : i < ws.length
      · exact hc
      · rw [List.getElem?_eq_none (by rw [Apportion.units_length]; omega)] at hv
        cases hv
    rw [Apportion.units_getElem? n ws hi] at hv
    have hv := (Option.some.inj hv).symm
    have hf : Apportion.floorAt n ws i = 0 := by unfold Apportion.floorAt; rw [hw]; simp
    have hnc : i ∉ Apportion.chosen n ws := fun hc => by
      have := Apportion.chosen_rem_pos n ws hW hc
      unfold Apportion.remAt at this; rw [hw] at this; simp at this
    simp [hf, hnc] at hv
    exact hv

-- Non-vacuity witness for FX9: scale 10, `[1,2,4]` gives `[1,3,6]` (exact proportions 1.43, 2.86, 5.71).
theorem apportion_one_two_four : apportion 10 [1, 2, 4] = .ok [1, 3, 6] := by
  apportion_eval
example : -(7 : Int) < ((3 : Nat) : Int) * 7 - 2 * 10 ∧ ((3 : Nat) : Int) * 7 - 2 * 10 < 7 := by decide +kernel
example : -(([1, 2, 4] : List Nat).sum : Int) < ((3 : Nat) : Int) * ([1, 2, 4] : List Nat).sum - (([1, 2, 4] : List Nat).getD 1 0 : Int) * 10 ∧
    ((3 : Nat) : Int) * ([1, 2, 4] : List Nat).sum - (([1, 2, 4] : List Nat).getD 1 0 : Int) * 10 < ([1, 2, 4] : List Nat).sum :=
  apportion_within_one apportion_one_two_four (i := 1) (v := 3) rfl
-- A zero weight gets 0 units: `[0,1,2]` at scale 3.
theorem apportion_zero_one_two : apportion 3 [0, 1, 2] = .ok [0, 1, 2] := by
  apportion_eval
example : (0 : Nat) = 0 := apportion_zero_weight apportion_zero_one_two (i := 0) (v := 0) rfl rfl

/-! ## FX10: the refusal -/

/-- FX10: `apportion` refuses `zeroTotalWeight` exactly when every weight is 0 (or the list is empty). -/
theorem apportion_refuses_iff (n : Nat) (ws : List Nat) :
    apportion n ws = .error .zeroTotalWeight ↔ ∀ w ∈ ws, w = 0 := by
  rw [← List.sum_eq_zero_iff_forall_eq_nat]
  unfold apportion
  by_cases hz : ws.sum = 0 <;> simp [hz]

/-- FX10: when some weight is positive, the result is accepted. -/
theorem apportion_ok_of_pos (n : Nat) {ws : List Nat} (h : ∃ w ∈ ws, w ≠ 0) :
    ∃ vs, apportion n ws = .ok vs := by
  have hz : ws.sum ≠ 0 := fun hz =>
    let ⟨w, hw, hne⟩ := h
    hne (List.sum_eq_zero_iff_forall_eq_nat.mp hz w hw)
  exact ⟨Apportion.units n ws, by simp [apportion, hz]⟩

-- Non-vacuity witnesses for FX10: `[]` and `[0,0]` refuse; `[0,1]` at scale 5 gives `[0,5]`.
example : apportion 10 [] = .error .zeroTotalWeight := (apportion_refuses_iff 10 []).mpr (by simp)
example : apportion 10 [0, 0] = .error .zeroTotalWeight := (apportion_refuses_iff 10 [0, 0]).mpr (by simp)
example : apportion 5 [0, 1] = .ok [0, 5] := by
  apportion_eval
example : ∃ vs, apportion 5 [0, 1] = .ok vs := apportion_ok_of_pos 5 ⟨1, by simp, by decide⟩

/-! ## FX11: ties -/

/-- FX11: of two equal weights the earlier index gets at least as many units. -/
theorem apportion_tie {n : Nat} {ws vs : List Nat} (h : apportion n ws = .ok vs) {i j vi vj : Nat}
    (hij : i < j) (hw : ws.getD i 0 = ws.getD j 0) (hvi : vs[i]? = some vi) (hvj : vs[j]? = some vj) :
    vj ≤ vi := by
  unfold apportion at h
  by_cases hz : ws.sum = 0
  · simp [hz] at h
  · simp only [hz, ite_false, Except.ok.injEq] at h
    subst h
    have hW := Nat.pos_of_ne_zero hz
    have hlen := List.getElem?_eq_some_iff.mp hvj
    have hj : j < ws.length := by have := hlen.1; rw [Apportion.units_length] at this; exact this
    have hi : i < ws.length := by omega
    rw [Apportion.units_getElem? n ws hi] at hvi
    rw [Apportion.units_getElem? n ws hj] at hvj
    have hvi := (Option.some.inj hvi).symm
    have hvj := (Option.some.inj hvj).symm
    have hf : Apportion.floorAt n ws i = Apportion.floorAt n ws j := by unfold Apportion.floorAt; rw [hw]
    have hr : Apportion.remAt n ws i = Apportion.remAt n ws j := by unfold Apportion.remAt; rw [hw]
    have key : j ∈ Apportion.chosen n ws → i ∈ Apportion.chosen n ws := by
      intro hjc
      apply Classical.byContradiction
      intro hic
      have hp := Apportion.order_pairwise n ws
      rw [Apportion.order_split n ws, List.pairwise_append] at hp
      have hid : i ∈ (Apportion.order n ws).drop (Apportion.extra n ws) := by
        have := Apportion.mem_order (n := n) hi
        rw [Apportion.order_split n ws, List.mem_append] at this
        exact this.resolve_left hic
      have hb := hp.2.2 j hjc i hid
      simp only [Apportion.before] at hb
      simp at hb
      omega
    subst hvi hvj
    by_cases hjc : j ∈ Apportion.chosen n ws
    · simp [hjc, key hjc, hf]
    · by_cases hic : i ∈ Apportion.chosen n ws <;> simp [hjc, hic, hf]

-- Non-vacuity witness for FX11: scale 2, `[1,1,1]` gives `[1,1,0]` (the earliest indices win the tie).
theorem apportion_two_ones : apportion 2 [1, 1, 1] = .ok [1, 1, 0] := by
  apportion_eval
example : (0 : Nat) < 2 ∧ ([1, 1, 1] : List Nat).getD 0 0 = ([1, 1, 1] : List Nat).getD 2 0 ∧
    ∃ vi vj, [1, 1, 0][0]? = some vi ∧ [1, 1, 0][2]? = some vj ∧ vj ≤ vi :=
  ⟨by decide, rfl, 1, 0, rfl, rfl, by decide⟩
example : (0 : Nat) ≤ 1 := apportion_tie apportion_two_ones (i := 0) (j := 2) (by decide) rfl rfl rfl

/-! ## FX12: idempotence -/

/-- FX12: weights that already sum to the (positive) scale are returned unchanged. -/
theorem apportion_idem {n : Nat} {ws : List Nat} (hn : 0 < n) (h : ws.sum = n) : apportion n ws = .ok ws := by
  have hz : ws.sum ≠ 0 := by omega
  have hf : ∀ i, Apportion.floorAt n ws i = ws.getD i 0 := fun i => by
    unfold Apportion.floorAt; rw [h]; exact Nat.mul_div_cancel _ hn
  have hex : Apportion.extra n ws = 0 := by
    unfold Apportion.extra
    have : (List.range ws.length).map (Apportion.floorAt n ws) = ws := by
      rw [List.map_congr_left fun i _ => hf i]; exact Apportion.map_getD_range ws
    rw [this, h]; omega
  have hc : Apportion.chosen n ws = [] := by simp [Apportion.chosen, hex]
  simp only [apportion, hz, ite_false, Apportion.units, hc, List.not_mem_nil, ite_false, Nat.add_zero, hf]
  rw [Apportion.map_getD_range]

-- Non-vacuity witnesses for FX12: scale 4, `[1,2,1]`; and a case with `Σ ≠ n` where the result differs.
example : apportion 4 [1, 2, 1] = .ok [1, 2, 1] := apportion_idem (by decide) (by decide)
example : apportion 10 [1, 2, 1] = .ok [3, 5, 2] ∧ ([1, 2, 1] : List Nat).sum ≠ 10 := by
  refine ⟨?_, by decide⟩
  apportion_eval

end VbmProb
