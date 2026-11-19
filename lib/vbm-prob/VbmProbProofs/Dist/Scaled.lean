import VbmProb.Dist.Scaled
import VbmProbProofs.Dist
import VbmProbProofs.Dist.Normalize
import VbmProbProofs.Apportion
/-! # `Dist.toScaled` and `Dist.ofScaled`: the properties FX13 and FX14, each with its witness

FX13: the weights of `toScaled` sum to the scale, its keys are the keys of `d` in order, and every weight is within one unit of the exact proportion. FX14: `ofScaled` accepts exactly the weights that sum to the scale, have strictly increasing keys and pass the limits; the probability at each key of positive weight is `w / n`. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-! ## The common denominator -/

omit [Key α] in
theorem commonDen_cons (b : α × Prob) (L : List (α × Prob)) :
    commonDen (b :: L) = Nat.lcm b.2.val.den (commonDen L) := rfl

omit [Key α] in
theorem den_dvd_commonDen : ∀ (L : List (α × Prob)) {a : α × Prob}, a ∈ L → a.2.val.den ∣ commonDen L
  | [], a, h => by simp at h
  | b :: L, a, h => by
    rw [commonDen_cons]
    rcases List.mem_cons.mp h with rfl | hm
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (den_dvd_commonDen L hm) (Nat.dvd_lcm_right _ _)

omit [Key α] in
theorem commonDen_pos : ∀ L : List (α × Prob), 0 < commonDen L
  | [] => by simp [commonDen]
  | b :: L => by
    rw [commonDen_cons]
    exact Nat.lcm_pos (Nat.pos_of_ne_zero b.2.val.den_nz) (commonDen_pos L)

/-- The numerator of one probability over the common denominator `D`. -/
def wt (D : Nat) (a : α × Prob) : Nat := a.2.val.num.toNat * (D / a.2.val.den)

theorem rat_eq_div (q : Rat) : q = (q.num : Rat) / (q.den : Rat) := by
  have h := @Rat.mk_eq_divInt q.num q.den q.den_nz q.reduced
  have h2 := Rat.divInt_eq_div q.num q.den
  rw [h2] at h
  exact h

omit [Key α] in
theorem wt_cast {D : Nat} {a : α × Prob} (h : a.2.val.den ∣ D) : ((wt D a : Nat) : Rat) = a.2.val * D := by
  have h0 : 0 ≤ a.2.val.num := Rat.num_nonneg.mpr a.2.nonneg
  have e1 : ((a.2.val.num.toNat : Nat) : Rat) = (a.2.val.num : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg h0]
  have e2 : (D : Rat) = (a.2.val.den : Rat) * ((D / a.2.val.den : Nat) : Rat) := by
    rw [← Rat.natCast_mul, Nat.mul_div_cancel' h]
  have hd : (a.2.val.den : Rat) ≠ 0 := fun hh => a.2.val.den_nz (Rat.natCast_inj.mp (by simpa using hh))
  have e3 := rat_eq_div a.2.val
  unfold wt
  rw [Rat.natCast_mul, e1, e2]
  generalize ((D / a.2.val.den : Nat) : Rat) = m
  conv => rhs; lhs; rw [e3]
  rw [Rat.div_def]
  grind

omit [Key α] in
theorem sum_wt (D : Nat) : ∀ L : List (α × Prob), (∀ a ∈ L, a.2.val.den ∣ D) →
    (((L.map (wt D)).sum : Nat) : Rat) = (L.map (·.2.val)).sum * D
  | [], _ => by simp [Rat.zero_mul]
  | a :: L, h => by
    have ih := sum_wt D L (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [Rat.natCast_add, ih, wt_cast (h a (by simp)), Rat.add_mul]

/-- The numerators sum to the common denominator. -/
theorem scaledWeights_sum (d : Dist α) : (scaledWeights d).sum = commonDen d.atoms := by
  have h := sum_wt (commonDen d.atoms) d.atoms (fun a ha => den_dvd_commonDen _ ha)
  rw [d.total, Rat.one_mul] at h
  exact Rat.natCast_inj.mp h

theorem scaledWeights_length (d : Dist α) : (scaledWeights d).length = d.atoms.length := by
  simp [scaledWeights]

theorem scaledWeights_pos (d : Dist α) : 0 < (scaledWeights d).sum := by
  rw [scaledWeights_sum]; exact commonDen_pos _

theorem scaledWeights_getD (d : Dist α) {i : Nat} {a : α} {p : Prob} (h : d.atoms[i]? = some (a, p)) :
    (scaledWeights d).getD i 0 = wt (commonDen d.atoms) (a, p) := by
  simp [scaledWeights, List.getD_eq_getElem?_getD, h, wt]

/-! ## FX13 -/

theorem units_length' (sc : Scale) (d : Dist α) : (Apportion.units sc.n (scaledWeights d)).length = d.atoms.length := by
  rw [Apportion.units_length, scaledWeights_length]

theorem support_length (d : Dist α) : d.support.length = d.atoms.length := by simp [support]

/-- FX13: the weights sum to the scale. -/
theorem toScaled_sum (sc : Scale) (d : Dist α) : ((toScaled sc d).map (·.2)).sum = sc.n := by
  unfold toScaled
  rw [List.map_snd_zip (Nat.le_of_eq (by rw [units_length', support_length]))]
  exact Apportion.units_sum _ _ (scaledWeights_pos d)

/-- FX13: the keys are those of `d`, in order. -/
theorem toScaled_keys (sc : Scale) (d : Dist α) : (toScaled sc d).map (·.1) = d.support := by
  unfold toScaled
  exact List.map_fst_zip (Nat.le_of_eq (by rw [units_length', support_length]))

/-- FX13: the result has one entry per atom. -/
theorem toScaled_length (sc : Scale) (d : Dist α) : (toScaled sc d).length = d.atoms.length := by
  have := congrArg List.length (toScaled_keys sc d)
  simpa [support_length] using this

/-- FX13: every weight is within one unit of the exact proportion, in the form `|v − p·n| < 1`. -/
theorem toScaled_close (sc : Scale) (d : Dist α) {i : Nat} {a : α} {p : Prob} {v : Nat}
    (hp : d.atoms[i]? = some (a, p)) (hv : (toScaled sc d)[i]? = some (a, v)) :
    -1 < (v : Rat) - p.val * sc.n ∧ (v : Rat) - p.val * sc.n < 1 := by
  have hz : (toScaled sc d)[i]? = some (a, v) := hv
  unfold toScaled at hz
  rw [List.getElem?_zip_eq_some] at hz
  have hw := scaledWeights_getD d hp
  have happ : apportion sc.n (scaledWeights d) = .ok (Apportion.units sc.n (scaledWeights d)) := by
    simp [apportion, Nat.pos_iff_ne_zero.mp (scaledWeights_pos d)]
  obtain ⟨h1, h2⟩ := apportion_within_one happ hz.2
  rw [hw, scaledWeights_sum] at *
  have hD : (0 : Rat) < (commonDen d.atoms : Rat) := Rat.natCast_pos.mpr (commonDen_pos _)
  have hdv : (a, p).2.val.den ∣ commonDen d.atoms := den_dvd_commonDen _ (List.mem_of_getElem? hp)
  have hc := wt_cast hdv
  have h1' := Rat.intCast_lt_intCast.mpr h1
  have h2' := Rat.intCast_lt_intCast.mpr h2
  simp only [Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_neg, Rat.intCast_natCast] at h1' h2'
  rw [hc] at h1' h2'
  constructor
  · have : (-1 : Rat) * commonDen d.atoms < ((v : Rat) - p.val * sc.n) * commonDen d.atoms := by grind
    exact Rat.lt_of_mul_lt_mul_right this (Rat.le_of_lt hD)
  · have : ((v : Rat) - p.val * sc.n) * commonDen d.atoms < 1 * commonDen d.atoms := by grind
    exact Rat.lt_of_mul_lt_mul_right this (Rat.le_of_lt hD)

/-- FX13: `|weight/n − p| < 1/n`, for every atom. -/
theorem toScaled_error (sc : Scale) (d : Dist α) {i : Nat} {a : α} {p : Prob} {v : Nat}
    (hp : d.atoms[i]? = some (a, p)) (hv : (toScaled sc d)[i]? = some (a, v)) :
    -(1 / (sc.n : Rat)) < (v : Rat) / sc.n - p.val ∧ (v : Rat) / sc.n - p.val < 1 / (sc.n : Rat) := by
  obtain ⟨h1, h2⟩ := toScaled_close sc d hp hv
  have hn : (sc.n : Rat) ≠ 0 := sc.natCast_ne_zero
  have hi : 0 < ((sc.n : Rat))⁻¹ := Rat.inv_pos.mpr (Rat.natCast_pos.mpr sc.pos)
  have hinv : (sc.n : Rat) * ((sc.n : Rat))⁻¹ = 1 := Rat.mul_inv_cancel _ hn
  have e : (v : Rat) / sc.n - p.val = ((v : Rat) - p.val * sc.n) * ((sc.n : Rat))⁻¹ := by
    rw [Rat.div_def]; grind
  rw [e, Rat.div_def]
  constructor
  · have := (Rat.mul_lt_mul_right hi).mpr h1
    grind
  · have := (Rat.mul_lt_mul_right hi).mpr h2
    grind

/-- A literal probability for the witnesses. -/
private def lit (q : Rat) (h0 : 0 ≤ q := by decide +kernel) (h1 : q ≤ 1 := by decide +kernel) : Prob := ⟨q, h0, h1⟩

/-- Three atoms of 1/3 over the keys 1, 2, 3. -/
private def thirds : Dist Nat where
  atoms := [(1, lit (1/3)), (2, lit (1/3)), (3, lit (1/3))]
  sorted := by decide +kernel
  positive := by decide +kernel
  total := by decide +kernel

local macro "units_eval" : tactic =>
  `(tactic| simp [VbmProb.Apportion.units, VbmProb.Apportion.floorAt, VbmProb.Apportion.chosen, VbmProb.Apportion.order,
    VbmProb.Apportion.extra, VbmProb.Apportion.before, VbmProb.Apportion.remAt, List.mergeSort, List.range_succ])

private theorem thirds_weights : scaledWeights thirds = [1, 1, 1] := by
  unfold scaledWeights commonDen thirds lit
  decide +kernel

/-- W: three atoms of 1/3 at scale 10^6 give 333334, 333333, 333333. -/
theorem thirds_toScaled : toScaled Scale.million thirds = [(1, 333334), (2, 333333), (3, 333333)] := by
  unfold toScaled
  rw [thirds_weights]
  have : thirds.support = [1, 2, 3] := rfl
  rw [this]
  show List.zip [1, 2, 3] (Apportion.units 1000000 [1, 1, 1]) = _
  units_eval

/-- W: the sum, the keys and the bound hold on the witness (the hypotheses of the theorems are met). -/
example : ((toScaled Scale.million thirds).map (·.2)).sum = Scale.million.n ∧
    (toScaled Scale.million thirds).map (·.1) = thirds.support :=
  ⟨toScaled_sum _ _, toScaled_keys _ _⟩

example : -(1 / ((Scale.million.n : Nat) : Rat)) < ((333334 : Nat) : Rat) / (Scale.million.n : Nat) - (lit (1/3)).val ∧
    ((333334 : Nat) : Rat) / (Scale.million.n : Nat) - (lit (1/3)).val < 1 / ((Scale.million.n : Nat) : Rat) :=
  toScaled_error Scale.million thirds (i := 0) (a := 1) (p := lit (1/3)) rfl
    (by rw [thirds_toScaled]; rfl)

/-! ## FX14 -/

omit [Key α] in
private theorem bits_none {lim : Limits} {ws : List (α × Rat)} (h : ¬ ∀ a ∈ ws, a.2.bits ≤ lim.maxBits) :
    ∃ i a, firstWhere (fun a : α × Rat => decide (lim.maxBits < a.2.bits)) ws 0 = some (i, a) := by
  cases hf : firstWhere (fun a : α × Rat => decide (lim.maxBits < a.2.bits)) ws 0 with
  | some r => exact ⟨r.1, r.2, rfl⟩
  | none =>
    exact absurd (fun a ha => by simpa using (firstWhere_eq_none_iff _ _ _).mp hf a ha) h

/-- FX14: weights that do not sum to the scale are refused, carrying the sum and the scale. -/
theorem ofScaled_sumNotScale {lim : Limits} {sc : Scale} {ws : List (α × Nat)} (h : (ws.map (·.2)).sum ≠ sc.n) :
    ofScaled lim sc ws = .error (.scaledSumNotScale (ws.map (·.2)).sum sc.n) := by
  simp [ofScaled, h]

/-- FX14: with the sum right, the first key not above its predecessor is refused. -/
theorem ofScaled_keysNotIncreasing {lim : Limits} {sc : Scale} {ws : List (α × Nat)} {i : Nat}
    (h : (ws.map (·.2)).sum = sc.n) (hk : firstNotInc (ws.map (·.1)) 0 = some i) :
    ofScaled lim sc ws = .error (.keysNotIncreasing i) := by
  simp [ofScaled, h, hk]

omit [Key α] in
theorem ws_map_snd (ws : List (α × Nat)) : (ws.map (fun a => (a.1, (a.2 : Rat)))).map (·.2) = (ws.map (·.2)).map (fun w : Nat => (w : Rat)) := by
  simp [List.map_map, Function.comp_def]

theorem sum_cast : ∀ l : List Nat, ((l.sum : Nat) : Rat) = (l.map (fun w : Nat => (w : Rat))).sum
  | [] => by simp
  | w :: l => by simp [Rat.natCast_add, sum_cast l]

/-- FX14: the exact atoms: the keys of positive weight, each with probability `w / n`. -/
theorem ofScaled_vals {lim : Limits} {sc : Scale} {ws : List (α × Nat)} {d : Dist α}
    (h : ofScaled lim sc ws = .ok d) :
    d.atoms.map (fun a => (a.1, a.2.val)) =
      (ws.filter (fun a => 0 < a.2)).map (fun a => (a.1, (a.2 : Rat) / (sc.n : Rat))) := by
  unfold ofScaled at h
  by_cases hs : (ws.map (·.2)).sum ≠ sc.n
  · simp [hs] at h
  · simp only [hs, ↓reduceIte] at h
    have hs' : (ws.map (·.2)).sum = sc.n := Classical.byContradiction hs
    cases hk : firstNotInc (ws.map (·.1)) 0 with
    | some i => simp [hk] at h
    | none =>
      simp only [hk] at h
      have hkeys : ((ws.map (fun a => (a.1, (a.2 : Rat)))).map (·.1)).Pairwise (· < ·) := by
        have := firstNotInc_none _ _ hk
        simpa [List.map_map, Function.comp_def] using this
      have hnn : ∀ a ∈ ws.map (fun a => (a.1, (a.2 : Rat))), 0 ≤ a.2 := fun a ha => by
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha; exact Rat.natCast_nonneg
      have hpos : ∃ a ∈ ws.map (fun a => (a.1, (a.2 : Rat))), 0 < a.2 := by
        apply Classical.byContradiction
        intro hno
        have hall : ∀ a ∈ ws, a.2 = 0 := fun a ha => by
          apply Classical.byContradiction
          intro hne
          exact hno ⟨(a.1, (a.2 : Rat)), List.mem_map_of_mem ha, Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hne)⟩
        have : (ws.map (·.2)).sum = 0 := by
          have : ∀ x ∈ ws.map (·.2), x = 0 := fun x hx => by
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hall y hy
          exact List.sum_eq_zero_iff_forall_eq_nat.mpr this
        have := sc.pos
        omega
      have hn : ¬ lim.maxAtoms < (ws.map (fun a => (a.1, (a.2 : Rat)))).length := fun hh => by
        rw [normalize_tooManyAtoms hh] at h; cases h
      have hb : ∀ a ∈ ws.map (fun a => (a.1, (a.2 : Rat))), a.2.bits ≤ lim.maxBits :=
        Classical.byContradiction fun hh => by
          obtain ⟨i, a, ha⟩ := bits_none hh
          rw [normalize_numberTooLarge hn ha] at h; cases h
      obtain ⟨d', hd', hv⟩ := normalize_vals hn hb hnn hpos
      rw [hd'] at h
      cases h
      rw [hv]
      have hc : normWeights (ws.map (fun a => (a.1, (a.2 : Rat)))) = (ws.map (fun a => (a.1, (a.2 : Rat)))).filter (fun a => decide (0 < a.2)) := by
        unfold normWeights; rw [canon_of_increasing _ hkeys]
      have hsum : ((normWeights (ws.map (fun a => (a.1, (a.2 : Rat))))).map (·.2)).sum = (sc.n : Rat) := by
        rw [weightTotal_normWeights _ hnn, ws_map_snd, ← sum_cast, hs']
      have hf : List.filter ((fun a : α × Rat => decide (0 < a.2)) ∘ fun a : α × Nat => (a.1, (a.2 : Rat))) ws =
          ws.filter (fun a => decide (0 < a.2)) :=
        List.filter_congr (fun a _ => by simp [Rat.natCast_pos])
      rw [hsum, hc, List.filter_map, hf, List.map_map]
      apply List.map_congr_left
      intro a _
      simp

/-- FX14: a key of positive weight is present with probability `w / n`. -/
theorem ofScaled_prob {lim : Limits} {sc : Scale} {ws : List (α × Nat)} {d : Dist α}
    (h : ofScaled lim sc ws = .ok d) {k : α} {w : Nat} (hm : (k, w) ∈ ws) (hw : 0 < w) :
    ∃ p, (k, p) ∈ d.atoms ∧ p.val = (w : Rat) / (sc.n : Rat) := by
  have hv := ofScaled_vals h
  have : (k, (w : Rat) / (sc.n : Rat)) ∈ d.atoms.map (fun a => (a.1, a.2.val)) := by
    rw [hv]
    exact List.mem_map.mpr ⟨(k, w), List.mem_filter.mpr ⟨hm, by simpa using hw⟩, rfl⟩
  obtain ⟨b, hb, e⟩ := List.mem_map.mp this
  have e1 : b.1 = k := congrArg Prod.fst e
  have e2 : b.2.val = (w : Rat) / (sc.n : Rat) := congrArg Prod.snd e
  exact ⟨b.2, by rw [← e1]; exact hb, e2⟩

/-- FX14: `ofScaled` accepts exactly the weights that sum to the scale, have strictly increasing keys, and pass the limits. -/
theorem ofScaled_ok_iff (lim : Limits) (sc : Scale) (ws : List (α × Nat)) :
    (∃ d : Dist α, ofScaled lim sc ws = .ok d) ↔
      (ws.map (·.2)).sum = sc.n ∧ (ws.map (·.1)).Pairwise (· < ·) ∧ ¬ lim.maxAtoms < ws.length ∧
        ∀ a ∈ ws, ((a.2 : Nat) : Rat).bits ≤ lim.maxBits := by
  constructor
  · rintro ⟨d, h⟩
    unfold ofScaled at h
    by_cases hs : (ws.map (·.2)).sum ≠ sc.n
    · simp [hs] at h
    · simp only [hs, ↓reduceIte] at h
      have hs' : (ws.map (·.2)).sum = sc.n := Classical.byContradiction hs
      cases hk : firstNotInc (ws.map (·.1)) 0 with
      | some i => simp [hk] at h
      | none =>
        simp only [hk] at h
        have hn : ¬ lim.maxAtoms < (ws.map (fun a => (a.1, (a.2 : Rat)))).length := fun hh => by
          rw [normalize_tooManyAtoms hh] at h; cases h
        have hb : ∀ a ∈ ws.map (fun a => (a.1, (a.2 : Rat))), a.2.bits ≤ lim.maxBits :=
          Classical.byContradiction fun hh => by
            obtain ⟨i, a, ha⟩ := bits_none hh
            rw [normalize_numberTooLarge hn ha] at h; cases h
        refine ⟨hs', firstNotInc_none _ _ hk, by simpa using hn, fun a ha => ?_⟩
        exact hb (a.1, (a.2 : Rat)) (List.mem_map_of_mem ha)
  · rintro ⟨hs, hk, hn, hb⟩
    have hkn : firstNotInc (ws.map (·.1)) 0 = none := firstNotInc_of_pairwise _ _ hk
    have hnn : ∀ a ∈ ws.map (fun a => (a.1, (a.2 : Rat))), 0 ≤ a.2 := fun a ha => by
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha; exact Rat.natCast_nonneg
    have hpos : ∃ a ∈ ws.map (fun a => (a.1, (a.2 : Rat))), 0 < a.2 := by
      apply Classical.byContradiction
      intro hno
      have hall : ∀ a ∈ ws, a.2 = 0 := fun a ha => by
        apply Classical.byContradiction
        intro hne
        exact hno ⟨(a.1, (a.2 : Rat)), List.mem_map_of_mem ha, Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hne)⟩
      have : (ws.map (·.2)).sum = 0 :=
        List.sum_eq_zero_iff_forall_eq_nat.mpr fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hall y hy
      have := sc.pos
      omega
    obtain ⟨d, hd, -⟩ := normalize_ok (lim := lim) (by simpa using hn)
      (fun a ha => by obtain ⟨b, hb', rfl⟩ := List.mem_map.mp ha; exact hb b hb') hnn hpos
    exact ⟨d, by simp [ofScaled, hs, hkn, hd]⟩

/-! ## FX14 witnesses -/

private theorem w_ok : ∃ d : Dist Nat, ofScaled Limits.default ⟨10, by decide⟩ [(1, 4), (2, 3), (3, 3)] = .ok d :=
  (ofScaled_ok_iff _ _ _).mpr ⟨by decide, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- W: scale 10, `[(1,4),(2,3),(3,3)]` is accepted with probabilities 2/5, 3/10, 3/10. -/
example : ∃ d : Dist Nat, ofScaled Limits.default ⟨10, by decide⟩ [(1, 4), (2, 3), (3, 3)] = .ok d ∧
    d.atoms.map (fun a => (a.1, a.2.val)) = [(1, 2/5), (2, 3/10), (3, 3/10)] := by
  obtain ⟨d, hd⟩ := w_ok
  refine ⟨d, hd, ?_⟩
  rw [ofScaled_vals hd]
  decide +kernel

/-- W: a key of positive weight is present (the hypotheses of `ofScaled_prob` hold). -/
example : ∃ d : Dist Nat, ofScaled Limits.default ⟨10, by decide⟩ [(1, 4), (2, 3), (3, 3)] = .ok d ∧
    ∃ p, ((2 : Nat), p) ∈ d.atoms ∧ p.val = (3 : Rat) / 10 := by
  obtain ⟨d, hd⟩ := w_ok
  exact ⟨d, hd, by
    have := ofScaled_prob hd (k := 2) (w := 3) (by simp) (by decide)
    simpa using this⟩

/-- W: `[(1,4),(2,3)]` sums to 7, not 10, and refuses. -/
example : ofScaled Limits.default (⟨10, by decide⟩ : Scale) [((1 : Nat), 4), (2, 3)] =
    .error (.scaledSumNotScale 7 10) :=
  ofScaled_sumNotScale (by decide)

/-- W: with the sum right, keys that are not increasing are refused. -/
example : ofScaled Limits.default (⟨7, by decide⟩ : Scale) [((2 : Nat), 4), (1, 3)] = .error (.keysNotIncreasing 1) :=
  ofScaled_keysNotIncreasing (by decide) (by decide +kernel)

/-- W: a limit refuses (the iff fails at the limits: two atoms with `maxAtoms = 1`). -/
example : ¬ ∃ d : Dist Nat, ofScaled { Limits.default with maxAtoms := 1 } (⟨7, by decide⟩ : Scale) [((1 : Nat), 4), (2, 3)] = .ok d :=
  fun h => by have := ((ofScaled_ok_iff _ _ _).mp h).2.2.1; exact this (by decide)

end Dist
end VbmProb
