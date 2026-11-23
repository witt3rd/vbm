import VbmDecision.Battery
import VbmDecisionProofs.Truth
/-! # The battery (S10): proofs

B1 to B20 of spec section 14.6. Scores are compared through the integer pair `N` and `D` (cross-multiplied); a witness that evaluates a `Rat` is closed by `decide +kernel`. -/
namespace VbmDecision
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Order on `Rat`, through the integer pair -/

theorem natDiv_eq (a b : Nat) : ((a : Nat) : Rat) / (b : Nat) = Rat.divInt a b := by
  rw [Rat.divInt_eq_div]; rfl

theorem natDiv_le_iff {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) :
    ((a : Nat) : Rat) / (b : Nat) ≤ ((c : Nat) : Rat) / (d : Nat) ↔ a * d ≤ c * b := by
  rw [natDiv_eq, natDiv_eq, Rat.le_iff_sub_nonneg, Rat.divInt_sub_divInt _ _ (by omega) (by omega)]
  rw [Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos (by omega) (by omega))]
  constructor
  · intro h
    have h2 : ((a * d : Nat) : Int) ≤ ((c * b : Nat) : Int) := by push_cast; omega
    exact Int.ofNat_le.mp h2
  · intro h
    have h2 : ((a * d : Nat) : Int) ≤ ((c * b : Nat) : Int) := Int.ofNat_le.mpr h
    push_cast at h2; omega

/-! ## B1: validity -/

theorem bguard_ok_iff (c : Prop) [Decidable c] (code : BatteryCode) (field : String) (k : Except BatteryRefusal Unit) :
    bguard c code field k = .ok () ↔ c ∧ k = .ok () := by
  unfold bguard; split <;> simp_all

theorem checkItems_ok_iff {α : Type} (l : List (Item α)) : ∀ (i : Nat) (seen : List String),
    checkItems i seen l = .ok () ↔
      (∀ it ∈ l, it.id ≠ "" ∧ it.id ∉ seen ∧ it.weight ≤ maxWeight ∧ it.VetoOk) ∧ (l.map (·.id)).Nodup := by
  induction l with
  | nil => intro i seen; simp [checkItems]
  | cons it rest ih =>
    intro i seen
    rw [checkItems, bguard_ok_iff, bguard_ok_iff, bguard_ok_iff, bguard_ok_iff, ih]
    simp only [List.mem_cons, List.map_cons, List.nodup_cons, List.mem_map, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2, h3, h4, hs, hn⟩
      refine ⟨⟨⟨h1, h2, h3, h4⟩, ?_⟩, ?_, hn⟩
      · intro x hx
        have := hs x hx
        exact ⟨this.1, fun h => this.2.1 (Or.inr h), this.2.2⟩
      · rintro ⟨x, hx, hxe⟩
        have := hs x hx
        exact this.2.1 (Or.inl hxe)
    · rintro ⟨⟨h0, hall⟩, hnd, hn⟩
      refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2, ?_, hn⟩
      intro x hx
      have := hall x hx
      refine ⟨this.1, ?_, this.2.2⟩
      rintro (h | h)
      · exact hnd ⟨x, hx, h⟩
      · exact this.2.1 h

theorem Battery.check_ok_iff {α : Type} (b : Battery α) : b.check = .ok () ↔ b.Valid := by
  unfold Battery.check Battery.Valid
  rw [bguard_ok_iff, bguard_ok_iff]
  cases h : checkItems 0 [] b.items with
  | error e =>
    have hn : ¬ checkItems 0 [] b.items = .ok () := by rw [h]; intro h; cases h
    rw [checkItems_ok_iff] at hn
    constructor
    · rintro ⟨_, _, h⟩; cases h
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exfalso; apply hn
      exact ⟨fun it hit => ⟨h3 it hit, by simp, h5 it hit, h6 it hit⟩, h4⟩
  | ok u =>
    cases u
    have := (checkItems_ok_iff b.items 0 []).mp h
    simp only [h, bguard_ok_iff]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun it hit => (this.1 it hit).1, this.2, fun it hit => (this.1 it hit).2.2.1, fun it hit => (this.1 it hit).2.2.2, h3⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨h1, h2, h7, trivial⟩

theorem checkOutcomes_ok_iff {α : Type} [DecidableEq α] (t : Table α) (l : List (Item α)) : ∀ i,
    checkOutcomes t i l = .ok () ↔ ∀ it ∈ l, ∀ v ∈ it.veto, v.outcome ∈ t.bands.map (·.outcome) := by
  induction l with
  | nil => intro i; simp [checkOutcomes]
  | cons it rest ih =>
    intro i
    simp only [checkOutcomes, bguard_ok_iff, ih, List.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩ x (rfl | hx)
      · exact h1
      · exact h2 x hx
    · intro h; exact ⟨h it (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

theorem checkBands_ok_iff {α : Type} (l : List (Band α)) : ∀ i, checkBands i l = .ok () ↔ BandsOk l := by
  induction l with
  | nil => intro i; simp [checkBands, BandsOk]
  | cons b rest ih =>
    intro i
    cases rest with
    | nil => simp [checkBands, BandsOk, bguard_ok_iff, ih]
    | cons n rest' =>
      rw [checkBands, BandsOk, bguard_ok_iff]
      simp only [bguard_ok_iff]
      rw [ih]

theorem Table.check_ok_iff {α : Type} (t : Table α) : t.check = .ok () ↔ t.Valid := by
  unfold Table.check Table.Valid
  simp only [bguard_ok_iff, checkBands_ok_iff, and_assoc]

/-! ## B2 to B6: the score -/

theorem sum_eq_zero_iff (l : List Nat) : l.sum = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, ih]

theorem scoreD_eq_zero_iff (ps : List (Weight × Prob)) : scoreD ps = 0 ↔ ∀ e ∈ ps, e.1 = 0 := by
  unfold scoreD scale
  rw [Nat.mul_eq_zero, sum_eq_zero_iff]
  simp

theorem scoreN_le (ps : List (Weight × Prob)) : scoreN ps ≤ scoreD ps := by
  induction ps with
  | nil => simp [scoreN, scoreD]
  | cons e ps ih =>
    obtain ⟨w, p⟩ := e
    simp only [scoreN, scoreD, List.map_cons, List.sum_cons] at ih ⊢
    have h1 : w * p.val ≤ w * scale := Nat.mul_le_mul_left w p.le
    have h2 : scale * (w + (ps.map (·.1)).sum) = w * scale + scale * (ps.map (·.1)).sum := by
      rw [Nat.mul_add, Nat.mul_comm scale w]
    rw [h2]
    exact Nat.add_le_add h1 ih

theorem score_ok_iff (ps : List (Weight × Prob)) (s : Rat) :
    Battery.score ps = .ok s ↔ scoreD ps ≠ 0 ∧ s = ((scoreN ps : Nat) : Rat) / ((scoreD ps : Nat) : Rat) := by
  unfold Battery.score
  split
  · simp_all
  · rename_i hne
    simp only [Except.ok.injEq]
    exact ⟨fun h => ⟨hne, h.symm⟩, fun h => h.2.symm⟩

/-- B2: the score is in `[0, 1]` and exact: `s × D = N`. -/
theorem battery_score_range {ps : List (Weight × Prob)} {s : Rat} (h : Battery.score ps = .ok s) :
    0 ≤ s ∧ s ≤ 1 ∧ s * ((scoreD ps : Nat) : Rat) = ((scoreN ps : Nat) : Rat) := by
  obtain ⟨hd, rfl⟩ := (score_ok_iff ps s).mp h
  have hD : ((scoreD ps : Nat) : Rat) ≠ 0 := fun h => hd (Rat.natCast_eq_zero_iff.mp h)
  have hpos : (0 : Rat) < ((scoreD ps : Nat) : Rat) := Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hd)
  refine ⟨?_, ?_, Rat.div_mul_cancel hD⟩
  · rw [natDiv_eq]; exact Rat.divInt_nonneg (by omega) (by omega)
  · apply Rat.le_of_mul_le_mul_right (c := ((scoreD ps : Nat) : Rat)) _ hpos
    rw [Rat.div_mul_cancel hD, Rat.one_mul]
    exact Rat.natCast_le_natCast.mpr (scoreN_le ps)

theorem scoreD_pos_of_ok {ps : List (Weight × Prob)} {s : Rat} (h : Battery.score ps = .ok s) : 0 < scoreD ps :=
  Nat.pos_of_ne_zero ((score_ok_iff ps s).mp h).1

theorem score_le_iff {ps ps' : List (Weight × Prob)} {s s' : Rat} (h : Battery.score ps = .ok s) (h' : Battery.score ps' = .ok s') :
    s ≤ s' ↔ scoreN ps * scoreD ps' ≤ scoreN ps' * scoreD ps := by
  obtain ⟨_, rfl⟩ := (score_ok_iff ps s).mp h
  obtain ⟨_, rfl⟩ := (score_ok_iff ps' s').mp h'
  exact natDiv_le_iff (scoreD_pos_of_ok h) (scoreD_pos_of_ok h')

theorem score_lt_iff {ps ps' : List (Weight × Prob)} {s s' : Rat} (h : Battery.score ps = .ok s) (h' : Battery.score ps' = .ok s') :
    s < s' ↔ scoreN ps * scoreD ps' < scoreN ps' * scoreD ps := by
  rw [← Rat.not_le, score_le_iff h' h]
  omega

theorem scoreN_insert (l1 l2 : List (Weight × Prob)) (w : Weight) (p : Prob) :
    scoreN (l1 ++ (w, p) :: l2) = (scoreN l1 + scoreN l2) + w * p.val := by
  simp only [scoreN, List.map_append, List.sum_append, List.map_cons, List.sum_cons]; omega

theorem scoreD_insert (l1 l2 : List (Weight × Prob)) (w : Weight) (p : Prob) :
    scoreD (l1 ++ (w, p) :: l2) = scale * ((l1.map (·.1)).sum + (l2.map (·.1)).sum + w) := by
  simp only [scoreD, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
  congr 1
  generalize (List.map (fun x : Weight × Prob => x.fst) l1).sum = a
  generalize (List.map (fun x : Weight × Prob => x.fst) l2).sum = b
  ac_rfl

/-- B3: raising one probability, the others fixed, never lowers the score; it strictly raises it if the weight is positive and the probability grew; a zero weight leaves it unchanged. -/
theorem battery_score_monotone (l1 l2 : List (Weight × Prob)) (w : Weight) (p p' : Prob) (hp : p.val ≤ p'.val) {s s' : Rat}
    (h : Battery.score (l1 ++ (w, p) :: l2) = .ok s) (h' : Battery.score (l1 ++ (w, p') :: l2) = .ok s') :
    s ≤ s' ∧ (0 < w → p.val < p'.val → s < s') ∧ (w = 0 → s = s') := by
  have hD := scoreD_insert l1 l2 w p
  have hD' := scoreD_insert l1 l2 w p'
  have hN := scoreN_insert l1 l2 w p
  have hN' := scoreN_insert l1 l2 w p'
  have hpos := scoreD_pos_of_ok h
  have hle : s ≤ s' := by
    rw [score_le_iff h h', hN, hN', hD, hD']
    have h1 : w * p.val ≤ w * p'.val := Nat.mul_le_mul_left w hp
    have key : scoreN l1 + scoreN l2 + w * p.val ≤ scoreN l1 + scoreN l2 + w * p'.val := Nat.add_le_add_left h1 _
    exact Nat.mul_le_mul_right _ key
  refine ⟨hle, ?_, ?_⟩
  · intro hw hlt
    rw [score_lt_iff h h', hN, hN', hD, hD']
    rw [hD] at hpos
    have h1 : w * p.val < w * p'.val := Nat.mul_lt_mul_of_pos_left hlt hw
    have key : scoreN l1 + scoreN l2 + w * p.val < scoreN l1 + scoreN l2 + w * p'.val := Nat.add_lt_add_left h1 _
    exact Nat.mul_lt_mul_of_pos_right key hpos
  · intro hw
    subst hw
    apply Rat.le_antisymm hle
    rw [score_le_iff h' h, hN, hN', hD, hD']
    simp

/-- B4: a permutation of the items (with their probabilities) gives the same score. -/
theorem battery_score_permutation {ps ps' : List (Weight × Prob)} (h : ps.Perm ps') : Battery.score ps = Battery.score ps' := by
  have hN : scoreN ps = scoreN ps' := (h.map _).sum_nat
  have hD : scoreD ps = scoreD ps' := by unfold scoreD; rw [(h.map _).sum_nat]
  unfold Battery.score; rw [hN, hD]

/-- B5: inserting an item of weight 0, with any probability, does not change the score. -/
theorem battery_score_zero_weight (l1 l2 : List (Weight × Prob)) (p : Prob) :
    Battery.score (l1 ++ (0, p) :: l2) = Battery.score (l1 ++ l2) := by
  have hN : scoreN (l1 ++ (0, p) :: l2) = scoreN (l1 ++ l2) := by simp [scoreN]
  have hD : scoreD (l1 ++ (0, p) :: l2) = scoreD (l1 ++ l2) := by simp [scoreD]
  unfold Battery.score; rw [hN, hD]

/-- B6: the score refuses `allWeightsZero` exactly when every weight is 0 (the refusal is returned before any division). -/
theorem battery_score_refuses (ps : List (Weight × Prob)) :
    Battery.score ps = .error ⟨.allWeightsZero, "items"⟩ ↔ ∀ e ∈ ps, e.1 = 0 := by
  rw [← scoreD_eq_zero_iff]
  unfold Battery.score
  split <;> simp_all

theorem battery_score_ok_of_positive {ps : List (Weight × Prob)} {e : Weight × Prob} (he : e ∈ ps) (hw : 0 < e.1) :
    ∃ s, Battery.score ps = .ok s := by
  have : scoreD ps ≠ 0 := fun h => by have h2 : e.1 = 0 := (scoreD_eq_zero_iff ps).mp h e he; exact absurd h2 (Nat.pos_iff_ne_zero.mp hw)
  exact ⟨_, (score_ok_iff ps _).mpr ⟨this, rfl⟩⟩

/-! ## The table: B12 to B15 -/

theorem bandAt_some {α : Type} (s : Rat) : ∀ (l : List (Band α)) (k j : Nat) (b : Band α),
    bandAt s k l = some (j, b) → b ∈ l ∧ b.has s = true ∧ k ≤ j := by
  intro l
  induction l with
  | nil => intro k j b h; simp [bandAt] at h
  | cons x rest ih =>
    intro k j b h
    unfold bandAt at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, hx, Nat.le_refl _⟩
    · obtain ⟨h1, h2, h3⟩ := ih (k + 1) j b h
      exact ⟨List.mem_cons_of_mem _ h1, h2, by omega⟩

theorem bandAt_none_iff {α : Type} (s : Rat) : ∀ (l : List (Band α)) (k : Nat),
    bandAt s k l = none ↔ ∀ b ∈ l, b.has s = false := by
  intro l
  induction l with
  | nil => intro k; simp [bandAt]
  | cons x rest ih =>
    intro k
    unfold bandAt
    split
    · rename_i hx; simp only [reduceCtorEq, false_iff]; intro h; have := h x List.mem_cons_self; simp_all
    · rename_i hx
      rw [ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      simp_all

theorem bandAt_get {α : Type} (s : Rat) : ∀ (l : List (Band α)) (k j : Nat) (b : Band α),
    bandAt s k l = some (j, b) → ∃ i, j = k + i ∧ l[i]? = some b := by
  intro l
  induction l with
  | nil => intro k j b h; simp [bandAt] at h
  | cons x rest ih =>
    intro k j b h
    unfold bandAt at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, by omega, rfl⟩
    · obtain ⟨i, h1, h2⟩ := ih (k + 1) j b h
      exact ⟨i + 1, by omega, h2⟩

/-- The bands are each in range and pairwise ordered: what `BandsOk` gives. -/
def Disj {α : Type} (l : List (Band α)) : Prop := (∀ b ∈ l, b.Ok) ∧ l.Pairwise (fun a b => a.hi ≤ b.lo)

theorem bandsOk_disj {α : Type} : ∀ l : List (Band α), BandsOk l → Disj l := by
  intro l
  induction l with
  | nil => intro _; exact ⟨by simp, List.Pairwise.nil⟩
  | cons b rest ih =>
    intro h
    obtain ⟨hb, hn, hr⟩ := h
    obtain ⟨hok, hpw⟩ := ih hr
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact hok x hx
    · rw [List.pairwise_cons]
      refine ⟨?_, hpw⟩
      intro x hx
      cases rest with
      | nil => simp at hx
      | cons n r =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hn
        · have h1 := (List.pairwise_cons.mp hpw).1 x hx
          have h2 := (hok n List.mem_cons_self).2.1
          grind

theorem has_disjoint {α : Type} {b c : Band α} (hb : b.Ok) (hc : c.Ok) (h : b.hi ≤ c.lo) (s : Rat) (hs : b.has s = true) :
    c.has s = false := by
  unfold Band.has Band.Ok at *
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *
  grind

theorem bandAt_of_get {α : Type} (s : Rat) : ∀ (l : List (Band α)) (k i : Nat) (b : Band α),
    Disj l → l[i]? = some b → b.has s = true → bandAt s k l = some (k + i, b) := by
  intro l
  induction l with
  | nil => intro k i b _ h; simp at h
  | cons x rest ih =>
    intro k i b hd h hb
    have hpw := List.pairwise_cons.mp hd.2
    have hrest : Disj rest := ⟨fun y hy => hd.1 y (List.mem_cons_of_mem _ hy), hpw.2⟩
    unfold bandAt
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [hb]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hmem : b ∈ rest := List.mem_of_getElem? h
      have hx : x.has s = false :=
        Bool.eq_false_iff.mpr fun hxs => by
          have := has_disjoint (hd.1 x List.mem_cons_self) (hd.1 b (List.mem_cons_of_mem _ hmem)) (hpw.1 b hmem) s hxs
          simp_all
      rw [hx]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih (k + 1) i b hrest h hb]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      omega

/-- B12: for a valid table a score is in at most one band, so the index does not depend on the order of the search. -/
theorem table_disjoint {α : Type} {t : Table α} (hv : t.Valid) {s : Rat} {i j : Nat} {b c : Band α}
    (hb : t.bands[i]? = some b) (hc : t.bands[j]? = some c) (hbs : b.has s = true) (hcs : c.has s = true) : i = j := by
  have hd := bandsOk_disj _ hv.2.2
  have h1 := bandAt_of_get s t.bands 0 i b hd hb hbs
  have h2 := bandAt_of_get s t.bands 0 j c hd hc hcs
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  omega

theorem table_index_iff {α : Type} {t : Table α} (hv : t.Valid) (s : Rat) (i : Nat) :
    t.index s = some i ↔ ∃ b, t.bands[i]? = some b ∧ b.has s = true := by
  have hd := bandsOk_disj _ hv.2.2
  unfold Table.index
  constructor
  · intro h
    obtain ⟨⟨j, b⟩, hj, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨_, hh, _⟩ := bandAt_some s t.bands 0 j b hj
    obtain ⟨i', h1, h2⟩ := bandAt_get s t.bands 0 j b hj
    exact ⟨b, by simpa [h1] using h2, hh⟩
  · rintro ⟨b, hb, hs⟩
    rw [bandAt_of_get s t.bands 0 i b hd hb hs]; simp

/-- Past the first match, a later search index is larger: the monotone core of B13. -/
theorem bandAt_mono {α : Type} {s s' : Rat} (hss : s ≤ s') : ∀ (l : List (Band α)) (k i j : Nat) (b c : Band α),
    Disj l → bandAt s k l = some (i, b) → bandAt s' k l = some (j, c) → i ≤ j := by
  intro l
  induction l with
  | nil => intro k i j b c _ h; simp [bandAt] at h
  | cons x rest ih =>
    intro k i j b c hd h1 h2
    have hpw := List.pairwise_cons.mp hd.2
    have hrest : Disj rest := ⟨fun y hy => hd.1 y (List.mem_cons_of_mem _ hy), hpw.2⟩
    have hj := (bandAt_some s' _ _ _ _ h2).2.2
    unfold bandAt at h1 h2
    by_cases hx : x.has s = true
    · simp only [hx, ↓reduceIte] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      omega
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h1
      by_cases hx' : x.has s' = true
      · simp only [hx', ↓reduceIte] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨hmem, hbs, _⟩ := bandAt_some s _ _ _ _ h1
        exfalso
        have hxo := hd.1 x List.mem_cons_self
        have hbo := hd.1 b (List.mem_cons_of_mem _ hmem)
        have hl := hpw.1 b hmem
        unfold Band.has Band.Ok at *
        simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *
        grind
      · simp only [hx', Bool.false_eq_true, ↓reduceIte] at h2
        exact ih (k + 1) i j b c hrest h1 h2

/-- B13: for `s ≤ s'`, the band of `s` is not after the band of `s'`. -/
theorem table_monotone {α : Type} {t : Table α} (hv : t.Valid) {s s' : Rat} (hss : s ≤ s') {i j : Nat}
    (hi : t.index s = some i) (hj : t.index s' = some j) : i ≤ j := by
  unfold Table.index at hi hj
  obtain ⟨⟨i', b⟩, h1, rfl⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨⟨j', c⟩, h2, rfl⟩ := Option.map_eq_some_iff.mp hj
  exact bandAt_mono hss _ _ _ _ _ _ (bandsOk_disj _ hv.2.2) h1 h2

theorem table_lookup_eq {α : Type} (t : Table α) (s : Rat) :
    t.lookup s = match bandAt s 0 t.bands with | some (_, b) => .decided b.outcome | none => .abstain := rfl

/-- B14, `lo`: a score equal to the `lo` of band `i` is in band `i`. -/
theorem table_cut_lo {α : Type} {t : Table α} (hv : t.Valid) {i : Nat} {b : Band α} (hb : t.bands[i]? = some b) :
    t.index b.lo = some i := by
  rw [table_index_iff hv]
  have hok := (bandsOk_disj _ hv.2.2).1 b (List.mem_of_getElem? hb)
  refine ⟨b, hb, ?_⟩
  unfold Band.has; unfold Band.Ok at hok
  simp only [decide_eq_true_eq]
  grind

/-- B14, `hi` met by the next `lo`: the score is in band `i+1`. -/
theorem table_cut_hi_next {α : Type} {t : Table α} (hv : t.Valid) {i : Nat} {b n : Band α}
    (hb : t.bands[i]? = some b) (hn : t.bands[i + 1]? = some n) (h : n.lo = b.hi) : t.index b.hi = some (i + 1) := by
  rw [← h]; exact table_cut_lo hv hn

/-- B14, a gap: the `hi` of band `i` below the `lo` of the next band is in no band. -/
theorem table_cut_hi_gap {α : Type} {t : Table α} (hv : t.Valid) {i : Nat} {b n : Band α}
    (hb : t.bands[i]? = some b) (hn : t.bands[i + 1]? = some n) (h : b.hi < n.lo) : t.index b.hi = none := by
  have hd := bandsOk_disj _ hv.2.2
  have hpw := List.pairwise_iff_getElem.mp hd.2
  unfold Table.index
  rw [Option.map_eq_none_iff, bandAt_none_iff]
  intro x hx
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
  have hbl : i < t.bands.length := (List.getElem?_eq_some_iff.mp hb).1
  have hbi : t.bands[i] = b := (List.getElem?_eq_some_iff.mp hb).2
  have hnl : i + 1 < t.bands.length := (List.getElem?_eq_some_iff.mp hn).1
  have hni : t.bands[i + 1] = n := (List.getElem?_eq_some_iff.mp hn).2
  have hxo := hd.1 x hx
  have hbo := hd.1 b (List.mem_of_getElem? hb)
  have hno := hd.1 n (List.mem_of_getElem? hn)
  have hhi1 : b.hi < 1 := by unfold Band.Ok at hno; grind
  have key : ∀ y : Band α, y.Ok → (y.hi ≤ b.hi ∧ b.hi ≠ y.hi ∨ b.hi < y.lo ∨ (y.lo ≤ b.hi ∧ y.hi ≠ 1 ∧ ¬ b.hi < y.hi)) →
      y.has b.hi = false := by
    intro y hy hc
    unfold Band.has; unfold Band.Ok at hy
    simp only [decide_eq_false_iff_not]
    grind
  apply key x hxo
  unfold Band.Ok at hxo hbo hno
  rcases Nat.lt_trichotomy j i with hlt | heq | hgt
  · have := hpw j i hj hbl hlt
    rw [hjx, hbi] at this
    grind
  · subst heq
    rw [← hjx, hbi]
    grind
  · rcases Nat.lt_or_ge (i + 1) j with h2 | h2
    · have := hpw (i + 1) j hnl hj h2
      rw [hni, hjx] at this
      grind
    · have : j = i + 1 := by omega
      subst this
      rw [← hjx, hni]
      grind

/-- B14, the closed end: a band whose `hi` is 1 contains 1. -/
theorem table_cut_one {α : Type} {t : Table α} (hv : t.Valid) {i : Nat} {b : Band α} (hb : t.bands[i]? = some b)
    (h : b.hi = 1) : t.index 1 = some i := by
  rw [table_index_iff hv]
  have hok := (bandsOk_disj _ hv.2.2).1 b (List.mem_of_getElem? hb)
  refine ⟨b, hb, ?_⟩
  unfold Band.has; unfold Band.Ok at hok
  simp only [decide_eq_true_eq]
  grind

/-- A table has no gap when it starts at 0, each band starts where the last ended and the last ends at 1. -/
def Table.Gapless {α : Type} (t : Table α) : Prop := GaplessFrom 0 t.bands

instance Table.decGapless {α : Type} (t : Table α) : Decidable t.Gapless := gaplessDec 0 t.bands

theorem gapless_covers {α : Type} (s : Rat) (hs1 : s ≤ 1) : ∀ (l : List (Band α)) (lo : Rat) (k : Nat),
    BandsOk l → GaplessFrom lo l → lo ≤ s → lo < 1 → bandAt s k l ≠ none := by
  intro l
  induction l with
  | nil => intro lo k _ hg _ hlt; simp only [GaplessFrom] at hg; grind
  | cons b rest ih =>
    intro lo k hb hg hls hlt
    obtain ⟨hbo, _, hr⟩ := hb
    obtain ⟨hlo, hg'⟩ := hg
    unfold bandAt
    by_cases hh : b.has s = true
    · simp [hh]
    · have hh' : b.has s = false := by simpa using hh
      simp only [hh', Bool.false_eq_true, ↓reduceIte]
      unfold Band.has at hh'
      unfold Band.Ok at hbo
      simp only [decide_eq_false_iff_not] at hh'
      have hsh : b.hi ≤ s := by grind
      have hh1 : b.hi < 1 := by
        rcases Classical.em (b.hi < 1) with h | h
        · exact h
        · exfalso; apply hh'; grind
      exact ih b.hi (k + 1) hr hg' hsh hh1

/-- B15: for a table without a gap every score in `[0, 1]` has a band. -/
theorem table_gapless_total {α : Type} {t : Table α} (hv : t.Valid) (hg : t.Gapless) {s : Rat} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ i, t.index s = some i := by
  have := gapless_covers s h1 t.bands 0 0 hv.2.2 hg h0 (by decide)
  unfold Table.index
  cases h : bandAt s 0 t.bands with
  | none => exact absurd h this
  | some e => exact ⟨e.1, by simp⟩

/-! ## evaluate -/

theorem evaluate_ok_iff {α : Type} [DecidableEq α] (b : Battery α) (t : Table α) (as : Answers) (r : Record α) :
    evaluate b t as = .ok r ↔ b.Valid ∧ t.Valid ∧ b.OutcomesKnown t ∧ r = b.run t as := by
  unfold evaluate
  cases h1 : b.check with
  | error e =>
    have : ¬ b.Valid := fun hv => by have := (Battery.check_ok_iff b).mpr hv; rw [h1] at this; cases this
    simp [this]
  | ok u =>
    cases u
    have hv := (Battery.check_ok_iff b).mp h1
    cases h2 : t.check with
    | error e =>
      have : ¬ t.Valid := fun hv => by have := (Table.check_ok_iff t).mpr hv; rw [h2] at this; cases this
      simp [this]
    | ok u =>
      cases u
      have ht := (Table.check_ok_iff t).mp h2
      cases h3 : checkOutcomes t 0 b.items with
      | error e =>
        have : ¬ b.OutcomesKnown t := fun h => by
          have := (checkOutcomes_ok_iff t b.items 0).mpr h
          rw [h3] at this; cases this
        simp [this]
      | ok u =>
        cases u
        have ho : b.OutcomesKnown t := (checkOutcomes_ok_iff t b.items 0).mp h3
        simp only [Except.ok.injEq, hv, ht, ho, true_and]
        exact eq_comm

theorem Battery.run_battery {α : Type} [DecidableEq α] (b : Battery α) (t : Table α) (as : Answers) :
    (b.run t as).battery = b ∧ (b.run t as).table = t ∧ (b.run t as).replies = as := ⟨rfl, rfl, rfl⟩

/-! ### Reading -/

theorem required_of_weight {α : Type} {i : Item α} (h : 0 < i.weight) : i.required = true := by
  unfold Item.required; simp [h]

theorem readOpt_eq_some {α : Type} (as : Answers) (i : Item α) (x : Item α × Prob) :
    Item.readOpt as i = some x ↔ x.1 = i ∧ i.required = true ∧ i.readIn as = .ok x.2 := by
  obtain ⟨j, p⟩ := x
  unfold Item.readOpt
  by_cases hr : i.required = true
  · simp only [hr, ↓reduceIte]
    cases h : i.readIn as with
    | error f => simp
    | ok q =>
      simp only [Option.some.injEq, Prod.mk.injEq, Except.ok.injEq, true_and]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · simp [hr]

theorem faultOpt_eq_some {α : Type} (as : Answers) (i : Item α) (x : String × Fault) :
    Item.faultOpt as i = some x ↔ x.1 = i.id ∧ i.required = true ∧ i.readIn as = .error x.2 := by
  obtain ⟨k, f⟩ := x
  unfold Item.faultOpt
  by_cases hr : i.required = true
  · simp only [hr, ↓reduceIte]
    cases h : i.readIn as with
    | ok q => simp
    | error g =>
      simp only [Option.some.injEq, Prod.mk.injEq, Except.error.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; simp
      · rintro ⟨rfl, -, rfl⟩; exact ⟨rfl, rfl⟩
  · simp [hr]

theorem faults_nil_iff {α : Type} (b : Battery α) (as : Answers) :
    b.faults as = [] ↔ (∀ it ∈ b.items, it.required = true → ∃ p, it.readIn as = .ok p) ∧ b.unexpected as = [] := by
  unfold Battery.faults
  rw [List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
  apply and_congr_left'
  constructor
  · intro h it hit hr
    have := h it hit
    unfold Item.faultOpt at this
    simp only [hr, ↓reduceIte] at this
    cases hh : it.readIn as with
    | ok p => exact ⟨p, rfl⟩
    | error f => simp [hh] at this
  · intro h it hit
    unfold Item.faultOpt
    by_cases hr : it.required = true
    · obtain ⟨p, hp⟩ := h it hit hr
      simp [hr, hp]
    · simp [hr]

theorem scoreOf_some_iff {α : Type} (b : Battery α) (as : Answers) (s : Rat) :
    b.scoreOf as = some s ↔ b.faults as = [] ∧ Battery.score (b.pairs as) = .ok s := by
  unfold Battery.scoreOf
  by_cases h : (b.faults as).isEmpty = true
  · have h' : b.faults as = [] := List.isEmpty_iff.mp h
    simp only [h, ↓reduceIte, h', true_and]
    cases hs : Battery.score (b.pairs as) with
    | error e => simp [Except.toOption]
    | ok x => simp [Except.toOption, eq_comm]
  · have h' : b.faults as ≠ [] := fun e => h (by simp [e])
    simp [h, h']

theorem mem_pairs {α : Type} (b : Battery α) (as : Answers) (e : Weight × Prob) :
    e ∈ b.pairs as ↔ ∃ it ∈ b.items, it.required = true ∧ ∃ p, it.readIn as = .ok p ∧ e = (it.weight, p) := by
  unfold Battery.pairs Battery.reads
  simp only [List.mem_map, List.mem_filterMap]
  constructor
  · rintro ⟨x, ⟨it, hit, hx⟩, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (readOpt_eq_some as it x).mp hx
    subst h1
    exact ⟨x.1, hit, h2, x.2, h3, rfl⟩
  · rintro ⟨it, hit, hr, p, hp, rfl⟩
    exact ⟨(it, p), ⟨it, hit, (readOpt_eq_some as it (it, p)).mpr ⟨rfl, hr, hp⟩⟩, rfl⟩

/-- A valid battery with no fault has a score. -/
theorem score_of_nofault {α : Type} {b : Battery α} (hv : b.Valid) {as : Answers} (hf : b.faults as = []) :
    ∃ s, Battery.score (b.pairs as) = .ok s := by
  obtain ⟨it, hit, hw⟩ := hv.2.2.2.2.2.2
  obtain ⟨hall, _⟩ := (faults_nil_iff b as).mp hf
  obtain ⟨p, hp⟩ := hall it hit (required_of_weight hw)
  exact battery_score_ok_of_positive (e := (it.weight, p)) ((mem_pairs b as _).mpr ⟨it, hit, required_of_weight hw, p, hp, rfl⟩) hw

theorem scoreOf_some_iff_nofault {α : Type} {b : Battery α} (hv : b.Valid) (as : Answers) :
    (∃ s, b.scoreOf as = some s) ↔ b.faults as = [] := by
  constructor
  · rintro ⟨s, h⟩; exact ((scoreOf_some_iff b as s).mp h).1
  · intro hf
    obtain ⟨s, hs⟩ := score_of_nofault hv hf
    exact ⟨s, (scoreOf_some_iff b as s).mpr ⟨hf, hs⟩⟩

theorem mem_fires {α : Type} (b : Battery α) (as : Answers) (o : α) :
    o ∈ b.fires as ↔ ∃ it ∈ b.items, it.fired as = some o := by
  unfold Battery.fires; simp [List.mem_filterMap]

theorem fired_some {α : Type} {as : Answers} {it : Item α} {o : α} (h : it.fired as = some o) :
    ∃ v, it.veto = some v ∧ v.outcome = o ∧ ∃ p, it.readIn as = .ok p ∧ v.threshold.val ≤ p.val := by
  unfold Item.fired at h
  cases hv : it.veto with
  | none => simp [hv] at h
  | some v =>
    cases hr : it.readIn as with
    | error f => simp [hv, hr] at h
    | ok p =>
      simp only [hv, hr] at h
      by_cases hle : v.threshold.val ≤ p.val
      · simp only [hle, ↓reduceIte, Option.some.injEq] at h
        exact ⟨v, rfl, h, p, rfl, hle⟩
      · simp [hle] at h

theorem fired_of {α : Type} {as : Answers} {it : Item α} {v : Veto α} {p : Prob} (hv : it.veto = some v) (hr : it.readIn as = .ok p)
    (hle : v.threshold.val ≤ p.val) : it.fired as = some v.outcome := by
  unfold Item.fired; simp [hv, hr, hle]

/-! ### verdictOf -/

theorem verdictOf_nil {α : Type} [DecidableEq α] (t : Table α) (sc : Option Rat) :
    verdictOf t [] sc = match sc with
      | none => (.abstain, .fault)
      | some s => match bandAt s 0 t.bands with
        | some (_, b) => (.decided b.outcome, .score)
        | none => (.abstain, .gap) := rfl

theorem verdictOf_cons_uniform {α : Type} [DecidableEq α] (t : Table α) (o : α) (rest : List α) (sc : Option Rat)
    (h : ∀ x ∈ rest, x = o) : verdictOf t (o :: rest) sc = (.decided o, .veto) := by
  unfold verdictOf
  have : (rest.all fun x => Decidable.decide (x = o)) = true := List.all_eq_true.mpr fun x hx => by simp [h x hx]
  simp [this]

theorem verdictOf_cons_conflict {α : Type} [DecidableEq α] (t : Table α) (o : α) (rest : List α) (sc : Option Rat)
    (x : α) (hx : x ∈ rest) (hne : x ≠ o) : verdictOf t (o :: rest) sc = (.abstain, .vetoConflict) := by
  unfold verdictOf
  have : ¬ (rest.all fun y => Decidable.decide (y = o)) = true := by
    rw [List.all_eq_true]; intro h; exact hne (by simpa using h x hx)
  simp [this]

/-- Two distinct outcomes among the fired vetoes: a conflict. -/
theorem verdictOf_conflict {α : Type} [DecidableEq α] (t : Table α) (os : List α) (sc : Option Rat)
    (x y : α) (hx : x ∈ os) (hy : y ∈ os) (hne : x ≠ y) : verdictOf t os sc = (.abstain, .vetoConflict) := by
  cases os with
  | nil => simp at hx
  | cons o rest =>
    by_cases hx' : x = o
    · have hy' : y ∈ rest := by
        rcases List.mem_cons.mp hy with h | h
        · exact absurd (hx'.trans h.symm) hne
        · exact h
      exact verdictOf_cons_conflict t o rest sc y hy' (fun h => hne (hx'.trans h.symm))
    · have hx2 : x ∈ rest := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h hx'
        · exact h
      exact verdictOf_cons_conflict t o rest sc x hx2 hx'

theorem verdictOf_decided_of_ne_nil {α : Type} [DecidableEq α] (t : Table α) (os : List α) (sc : Option Rat) (o : α)
    (hne : os ≠ []) (h : (verdictOf t os sc).1 = .decided o) : ∀ x ∈ os, x = o := by
  cases os with
  | nil => exact absurd rfl hne
  | cons y rest =>
    by_cases hu : ∀ x ∈ rest, x = y
    · rw [verdictOf_cons_uniform t y rest sc hu] at h
      simp only [Verdict.decided.injEq] at h
      subst h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact hu x hx
    · exfalso
      obtain ⟨x, hx, hxy⟩ : ∃ x, x ∈ rest ∧ x ≠ y :=
        Classical.byContradiction fun hc => hu fun x hx => Classical.byContradiction fun hxy => hc ⟨x, hx, hxy⟩
      rw [verdictOf_cons_conflict t y rest sc x hx hxy] at h
      simp at h

/-! ## B7 to B11, B16, B19, B20 -/

theorem run_verdict_veto {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as : Answers} {o : α} (hne : b.fires as ≠ [])
    (h : (b.run t as).verdict = .decided o) : ∀ x ∈ b.fires as, x = o :=
  verdictOf_decided_of_ne_nil t _ _ o hne h

theorem run_no_veto {α : Type} [DecidableEq α] (b : Battery α) (t : Table α) (as : Answers) (hf : b.fires as = []) :
    (b.run t as).verdict = (verdictOf t [] (b.scoreOf as)).1 := by
  unfold Battery.run; simp [hf]

/-- B7: a decision has a cause in a valid answer: every fired veto names `o` (and one fired), or no veto fired, every required item
read `ok` (so the score exists) and the table decides `o` for it. -/
theorem battery_fail_closed {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as : Answers} {r : Record α} {o : α}
    (he : evaluate b t as = .ok r) (hd : r.verdict = .decided o) :
    ((∃ x, x ∈ b.fires as) ∧ ∀ x ∈ b.fires as, x = o) ∨
    (b.fires as = [] ∧ b.faults as = [] ∧ ∃ s, r.score = some s ∧ Battery.score (b.pairs as) = .ok s ∧ t.lookup s = .decided o) := by
  obtain ⟨hv, ht, ho, rfl⟩ := (evaluate_ok_iff b t as r).mp he
  by_cases hf : b.fires as = []
  · right
    refine ⟨hf, ?_⟩
    have hd' : (verdictOf t [] (b.scoreOf as)).1 = .decided o := by
      unfold Battery.run at hd; simpa [hf] using hd
    cases hs : b.scoreOf as with
    | none => rw [hs] at hd'; simp [verdictOf_nil] at hd'
    | some s =>
      obtain ⟨hnf, hsc⟩ := (scoreOf_some_iff b as s).mp hs
      refine ⟨hnf, s, by simp [Battery.run, hs], hsc, ?_⟩
      rw [hs] at hd'
      unfold Table.lookup
      cases hb : bandAt s 0 t.bands with
      | none => simp [verdictOf_nil, hb] at hd'
      | some e => obtain ⟨i, c⟩ := e; simp [verdictOf_nil, hb] at hd' ⊢; exact hd'
  · left
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hf
    exact ⟨⟨x, hx⟩, run_verdict_veto hf hd⟩

/-- B8: with no veto fired and a fault, the verdict is `abstain`, basis `fault`, no score, and `faults` is the list of faults. -/
theorem battery_faults_listed {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as : Answers} {r : Record α}
    (he : evaluate b t as = .ok r) (hf : b.fires as = []) (hn : b.faults as ≠ []) :
    r.verdict = .abstain ∧ r.basis = .fault ∧ r.score = none ∧ r.faults = b.faults as := by
  obtain ⟨hv, ht, ho, rfl⟩ := (evaluate_ok_iff b t as r).mp he
  have hs : b.scoreOf as = none := by
    cases h : b.scoreOf as with
    | none => rfl
    | some s => exact absurd ((scoreOf_some_iff b as s).mp h).1 hn
  simp [Battery.run, hf, hs, verdictOf_nil]

theorem mem_dedup (x : String) : ∀ l : List String, x ∈ dedup l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [dedup]
  | cons y rest ih =>
    unfold dedup
    by_cases h : y ∈ rest
    · simp only [h, ↓reduceIte, ih, List.mem_cons]
      constructor
      · intro hx; exact Or.inr hx
      · rintro (rfl | hx)
        · exact h
        · exact hx
    · simp only [h, ↓reduceIte, List.mem_cons, ih]

theorem nodup_dedup : ∀ l : List String, (dedup l).Nodup := by
  intro l
  induction l with
  | nil => simp [dedup]
  | cons y rest ih =>
    unfold dedup
    by_cases h : y ∈ rest
    · simp only [h, ↓reduceIte]; exact ih
    · simp only [h, ↓reduceIte, List.nodup_cons]
      exact ⟨fun hy => h ((mem_dedup y rest).mp hy), ih⟩

theorem unexpected_mem {α : Type} (b : Battery α) (as : Answers) (x : String × Fault) :
    x ∈ b.unexpected as ↔ x.2 = .unexpectedAnswer ∧ x.1 ∈ as.map (·.1) ∧ x.1 ∉ b.items.map (·.id) := by
  unfold Battery.unexpected
  simp only [List.mem_map, List.mem_filter, mem_dedup]
  obtain ⟨k, f⟩ := x
  constructor
  · rintro ⟨k', ⟨h1, h2⟩, h3⟩
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    exact ⟨rfl, h1, by simpa using h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨k, ⟨h1, by simpa using h2⟩, rfl⟩

theorem faults_mem {α : Type} (b : Battery α) (as : Answers) (x : String × Fault) :
    x ∈ b.faults as ↔ (∃ it ∈ b.items, it.id = x.1 ∧ it.required = true ∧ it.readIn as = .error x.2) ∨
      (x.2 = .unexpectedAnswer ∧ x.1 ∈ as.map (·.1) ∧ x.1 ∉ b.items.map (·.id)) := by
  unfold Battery.faults
  rw [List.mem_append, unexpected_mem, List.mem_filterMap]
  apply or_congr_left
  constructor
  · rintro ⟨it, hit, h⟩
    obtain ⟨h1, h2, h3⟩ := (faultOpt_eq_some as it x).mp h
    exact ⟨it, hit, h1.symm, h2, h3⟩
  · rintro ⟨it, hit, h1, h2, h3⟩
    exact ⟨it, hit, (faultOpt_eq_some as it x).mpr ⟨h1.symm, h2, h3⟩⟩

theorem nodup_filterMap_inj {α β : Type} (f : α → Option β) (l : List α) (hl : l.Nodup)
    (hf : ∀ a ∈ l, ∀ a' ∈ l, ∀ y, f a = some y → f a' = some y → a = a') : (l.filterMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at hl
    have ih' := ih hl.2 (fun x hx x' hx' y h1 h2 => hf x (List.mem_cons_of_mem _ hx) x' (List.mem_cons_of_mem _ hx') y h1 h2)
    rw [List.filterMap_cons]
    cases h : f a with
    | none => exact ih'
    | some y =>
      simp only [List.nodup_cons]
      refine ⟨?_, ih'⟩
      intro hy
      obtain ⟨a', ha', h'⟩ := List.mem_filterMap.mp hy
      have := hf a List.mem_cons_self a' (List.mem_cons_of_mem _ ha') y h h'
      exact hl.1 (this ▸ ha')

theorem map_nodup_of_inj {α β : Type} (f : α → β) (l : List α) (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun ha => h.1 (List.mem_map.mpr ⟨a, ha, rfl⟩), ih h.2⟩

theorem map_nodup_inj {l : List String} (hn : l.Nodup) : (l.map fun k => (k, Fault.unexpectedAnswer)).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hn.2⟩
    intro h
    obtain ⟨k, hk, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq, and_true] at he
    exact hn.1 (he ▸ hk)

theorem read_ne_unexpected {α : Type} (i : Item α) (r : Option Reply) : i.read r ≠ .error .unexpectedAnswer := by
  unfold Item.read
  split <;> (try split) <;> (try split) <;> simp

theorem readIn_ne_unexpected {α : Type} (as : Answers) (i : Item α) : i.readIn as ≠ .error .unexpectedAnswer := by
  unfold Item.readIn
  split
  · exact read_ne_unexpected _ _
  · exact read_ne_unexpected _ _
  · simp

theorem inj_of_nodup_map {α : Type} (f : α → String) : ∀ (l : List α), (l.map f).Nodup → ∀ a ∈ l, ∀ a' ∈ l, f a = f a' → a = a' := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x rest ih =>
    intro h a ha a' ha' heq
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp ha' with h2 | h2
    · rw [h1, h2]
    · subst h1
      exact absurd (List.mem_map.mpr ⟨a', h2, heq.symm⟩) h.1
    · subst h2
      exact absurd (List.mem_map.mpr ⟨a, h1, heq⟩) h.1
    · exact ih h.2 a h1 a' h2 heq

/-- The faults list each item once. -/
theorem faults_nodup {α : Type} {b : Battery α} (hv : b.Valid) (as : Answers) : (b.faults as).Nodup := by
  have hid := hv.2.2.2.1
  have hit : b.items.Nodup := map_nodup_of_inj _ _ hid
  unfold Battery.faults
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply nodup_filterMap_inj _ _ hit
    intro a ha a' ha' y h1 h2
    obtain ⟨e1, -, -⟩ := (faultOpt_eq_some as a (y)).mp h1
    obtain ⟨e2, -, -⟩ := (faultOpt_eq_some as a' (y)).mp h2
    exact inj_of_nodup_map _ _ hid a ha a' ha' (e1.symm.trans e2)
  · unfold Battery.unexpected
    have hn : ((dedup (as.map (·.1))).filter fun k => Decidable.decide (k ∉ b.items.map (·.id))).Nodup :=
      List.Pairwise.sublist List.filter_sublist (nodup_dedup _)
    exact map_nodup_inj hn
  · intro f1 hf1 f2 hf2 heq
    subst heq
    obtain ⟨it, _, h⟩ := List.mem_filterMap.mp hf1
    obtain ⟨_, _, hr⟩ := (faultOpt_eq_some as it f1).mp h
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hf2
    rw [← hk] at hr
    exact readIn_ne_unexpected as it hr

/-! ### Veto, B9 to B11 -/

theorem fired_none_of_noveto {α : Type} {as : Answers} {it : Item α} (h : it.veto = none) : it.fired as = none := by
  unfold Item.fired; simp [h]

theorem fires_nil_iff {α : Type} (b : Battery α) (as : Answers) : b.fires as = [] ↔ ∀ it ∈ b.items, it.fired as = none := by
  unfold Battery.fires; exact List.filterMap_eq_nil_iff

theorem fires_nil_of_noveto {α : Type} {b : Battery α} (h : ∀ it ∈ b.items, it.veto = none) (as : Answers) : b.fires as = [] :=
  (fires_nil_iff b as).mpr fun it hit => fired_none_of_noveto (h it hit)

theorem filterMap_single {α β : Type} [DecidableEq α] (f : α → Option β) (it : α) (o : β) :
    ∀ l : List α, l.Nodup → it ∈ l → (∀ x ∈ l, f x = if x = it then some o else none) → l.filterMap f = [o] := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons x rest ih =>
    intro hn hit hf
    rw [List.nodup_cons] at hn
    rw [List.filterMap_cons, hf x List.mem_cons_self]
    by_cases hx : x = it
    · subst hx
      simp only [↓reduceIte]
      have : rest.filterMap f = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro y hy
        rw [hf y (List.mem_cons_of_mem _ hy)]
        have : y ≠ x := fun e => hn.1 (e ▸ hy)
        simp [this]
      rw [this]
    · simp only [hx, ↓reduceIte]
      have hit' : it ∈ rest := by
        rcases List.mem_cons.mp hit with h | h
        · exact absurd h.symm hx
        · exact h
      exact ih hn.2 hit' (fun y hy => hf y (List.mem_cons_of_mem _ hy))

/-- B9: if exactly one item has a veto and it fired with outcome `o`, the verdict is `decided o`, whatever the other replies are. -/
theorem veto_decides {α : Type} [DecidableEq α] {b : Battery α} (hv : b.Valid) (t : Table α) (as : Answers) {it : Item α} {o : α}
    (hit : it ∈ b.items) (honly : ∀ it' ∈ b.items, it'.veto ≠ none → it' = it) (hf : it.fired as = some o) :
    (b.run t as).verdict = .decided o ∧ (b.run t as).basis = .veto := by
  have hfires : b.fires as = [o] := by
    unfold Battery.fires
    apply filterMap_single _ it o b.items (map_nodup_of_inj _ _ hv.2.2.2.1) hit
    intro it' hit'
    by_cases he : it' = it
    · subst he; simp [hf]
    · have : it'.veto = none := Classical.byContradiction fun hn => he (honly it' hit' hn)
      simp [fired_none_of_noveto this, he]
  unfold Battery.run
  rw [hfires]
  simp [verdictOf]

/-- B10: two fired vetoes that name different outcomes give `abstain`, basis `vetoConflict`. -/
theorem veto_conflict {α : Type} [DecidableEq α] (b : Battery α) (t : Table α) (as : Answers) {i j : Item α} {x y : α}
    (hi : i ∈ b.items) (hj : j ∈ b.items) (hxi : i.fired as = some x) (hyj : j.fired as = some y) (hne : x ≠ y) :
    (b.run t as).verdict = .abstain ∧ (b.run t as).basis = .vetoConflict := by
  have hx : x ∈ b.fires as := (mem_fires b as x).mpr ⟨i, hi, hxi⟩
  have hy : y ∈ b.fires as := (mem_fires b as y).mpr ⟨j, hj, hyj⟩
  unfold Battery.run
  rw [verdictOf_conflict t _ _ x y hx hy hne]
  exact ⟨rfl, rfl⟩

/-- B11: with no veto fired and no fault, the verdict is the table's lookup of the score (also for a battery with no veto item at all). -/
theorem veto_absent_score_decides {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as : Answers} {s : Rat}
    (hf : b.fires as = []) (hs : b.scoreOf as = some s) :
    (b.run t as).verdict = t.lookup s ∧ (b.run t as).score = some s := by
  unfold Battery.run
  simp only [hf, hs, verdictOf_nil]
  unfold Table.lookup
  cases hb : bandAt s 0 t.bands <;> simp

theorem veto_absent_no_veto_items {α : Type} [DecidableEq α] {b : Battery α} (hv : b.Valid) (t : Table α) (as : Answers)
    (hn : ∀ it ∈ b.items, it.veto = none) (hnf : b.faults as = []) :
    ∃ s, b.scoreOf as = some s ∧ (b.run t as).verdict = t.lookup s := by
  obtain ⟨s, hs⟩ := (scoreOf_some_iff_nofault hv as).mpr hnf
  exact ⟨s, hs, (veto_absent_score_decides (fires_nil_of_noveto hn as) hs).1⟩

/-- B16: a decided verdict is the outcome of some band, for a valid battery and table. -/
theorem battery_verdict_in_table {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as : Answers} {r : Record α} {o : α}
    (he : evaluate b t as = .ok r) (hd : r.verdict = .decided o) : o ∈ t.bands.map (·.outcome) := by
  obtain ⟨hv, ht, ho, rfl⟩ := (evaluate_ok_iff b t as r).mp he
  by_cases hf : b.fires as = []
  · have hd' : (verdictOf t [] (b.scoreOf as)).1 = .decided o := by
      unfold Battery.run at hd; simpa [hf] using hd
    cases hs : b.scoreOf as with
    | none => rw [hs] at hd'; simp [verdictOf_nil] at hd'
    | some s =>
      rw [hs] at hd'
      cases hb : bandAt s 0 t.bands with
      | none => simp [verdictOf_nil, hb] at hd'
      | some e =>
        obtain ⟨i, c⟩ := e
        simp only [verdictOf_nil, hb, Verdict.decided.injEq] at hd'
        subst hd'
        exact List.mem_map.mpr ⟨c, (bandAt_some s _ _ _ _ hb).1, rfl⟩
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hf
    have hall := run_verdict_veto (t := t) hf hd
    have : o = x := (hall x hx).symm
    subst this
    obtain ⟨it, hit, hfx⟩ := (mem_fires b as _).mp hx
    obtain ⟨v, hvv, hvo, _⟩ := fired_some hfx
    have := ho it hit v hvv
    rw [hvo] at this
    exact this

/-! ### B17: the battery is monotone -/

/-- B17: for a valid battery with no veto item, when two answer sets read alike except that one probability is raised, the score does not
fall and the band index of the verdict does not fall (the verdicts are the table's lookups of the scores). -/
theorem battery_monotone {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as as' : Answers} (hv : b.Valid) (htv : t.Valid)
    (hn : ∀ it ∈ b.items, it.veto = none) (l1 l2 : List (Weight × Prob)) (w : Weight) (p p' : Prob) (hp : p.val ≤ p'.val)
    (h1 : b.pairs as = l1 ++ (w, p) :: l2) (h2 : b.pairs as' = l1 ++ (w, p') :: l2)
    (hf : b.faults as = []) (hf' : b.faults as' = []) :
    ∃ s s', b.scoreOf as = some s ∧ b.scoreOf as' = some s' ∧ s ≤ s' ∧
      (b.run t as).verdict = t.lookup s ∧ (b.run t as').verdict = t.lookup s' ∧
      ∀ i j, t.index s = some i → t.index s' = some j → i ≤ j := by
  obtain ⟨s, hs⟩ := (scoreOf_some_iff_nofault hv as).mpr hf
  obtain ⟨s', hs'⟩ := (scoreOf_some_iff_nofault hv as').mpr hf'
  have e1 := ((scoreOf_some_iff b as s).mp hs).2
  have e2 := ((scoreOf_some_iff b as' s').mp hs').2
  rw [h1] at e1; rw [h2] at e2
  have hle := (battery_score_monotone l1 l2 w p p' hp e1 e2).1
  exact ⟨s, s', hs, hs', hle, (veto_absent_score_decides (fires_nil_of_noveto hn as) hs).1,
    (veto_absent_score_decides (fires_nil_of_noveto hn as') hs').1, fun i j hi hj => table_monotone htv hle hi hj⟩

/-! ### B18: a permutation of the items -/

theorem valid_perm {α : Type} {b b' : Battery α} (h : b.items.Perm b'.items) (hv : b.Valid) : b'.Valid := by
  obtain ⟨h1, h2, h3, h4, h5, h6, ⟨it, hit, hw⟩⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨it, h.subset hit, hw⟩⟩
  · rw [← h.length_eq]; exact h1
  · rw [← h.length_eq]; exact h2
  · intro x hx; exact h3 x (h.symm.subset hx)
  · exact ((h.map _).nodup_iff).mp h4
  · intro x hx; exact h5 x (h.symm.subset hx)
  · intro x hx; exact h6 x (h.symm.subset hx)

theorem outcomesKnown_perm {α : Type} [DecidableEq α] {b b' : Battery α} {t : Table α} (h : b.items.Perm b'.items)
    (ho : b.OutcomesKnown t) : b'.OutcomesKnown t := fun it hit => ho it (h.symm.subset hit)

theorem verdictOf_perm {α : Type} [DecidableEq α] (t : Table α) {os os' : List α} (h : os.Perm os') (sc : Option Rat) :
    verdictOf t os sc = verdictOf t os' sc := by
  cases os with
  | nil => rw [← List.Perm.nil_eq h]
  | cons o rest =>
    have hne : os' ≠ [] := fun e => by rw [e] at h; exact absurd h.length_eq (by simp)
    obtain ⟨o', rest', rfl⟩ := List.exists_cons_of_ne_nil hne
    by_cases hu : ∀ x ∈ o :: rest, x = o
    · have hu' : ∀ x ∈ o' :: rest', x = o := fun x hx => hu x (h.symm.subset hx)
      have hoo : o' = o := hu' o' List.mem_cons_self
      rw [verdictOf_cons_uniform t o rest sc (fun x hx => hu x (List.mem_cons_of_mem _ hx)),
        hoo, verdictOf_cons_uniform t o rest' sc (fun x hx => hu' x (List.mem_cons_of_mem _ hx))]
    · obtain ⟨x, hx, hxo⟩ : ∃ x, x ∈ o :: rest ∧ x ≠ o :=
        Classical.byContradiction fun hc => hu fun x hx => Classical.byContradiction fun hxy => hc ⟨x, hx, hxy⟩
      have hx2 : o ∈ o :: rest := List.mem_cons_self
      rw [verdictOf_conflict t _ sc x o hx hx2 hxo,
        verdictOf_conflict t _ sc x o (h.subset hx) (h.subset hx2) hxo]

theorem fires_perm {α : Type} {b b' : Battery α} (h : b.items.Perm b'.items) (as : Answers) : (b.fires as).Perm (b'.fires as) :=
  h.filterMap _

theorem faults_perm {α : Type} {b b' : Battery α} (h : b.items.Perm b'.items) (as : Answers) : (b.faults as).Perm (b'.faults as) := by
  unfold Battery.faults Battery.unexpected
  have hid : b.items.map (·.id) = b.items.map (·.id) := rfl
  have hm : ∀ k, (k ∈ b.items.map (·.id)) = (k ∈ b'.items.map (·.id)) := fun k =>
    propext ((h.map _).mem_iff)
  have : ((dedup (as.map (·.1))).filter fun k => Decidable.decide (k ∉ b.items.map (·.id))) =
      ((dedup (as.map (·.1))).filter fun k => Decidable.decide (k ∉ b'.items.map (·.id))) := by
    apply List.filter_congr
    intro k _
    simp only [hm k]
  rw [this]
  exact (h.filterMap _).append (List.Perm.refl _)

theorem pairs_perm {α : Type} {b b' : Battery α} (h : b.items.Perm b'.items) (as : Answers) : (b.pairs as).Perm (b'.pairs as) :=
  (h.filterMap _).map _

theorem scoreOf_perm {α : Type} {b b' : Battery α} (h : b.items.Perm b'.items) (as : Answers) : b.scoreOf as = b'.scoreOf as := by
  unfold Battery.scoreOf
  have hf : (b.faults as).isEmpty = (b'.faults as).isEmpty := by
    have hl := (faults_perm h as).length_eq
    cases h1 : b.faults as <;> cases h2 : b'.faults as <;> simp_all
  rw [hf, battery_score_permutation (pairs_perm h as)]

/-- B18: a permutation of the items of a valid battery (the answers equal) gives the same verdict, basis and score; `used`, `vetoed`
and `faults` are equal up to permutation. -/
theorem battery_permutation {α : Type} [DecidableEq α] {b b' : Battery α} {t : Table α} {as : Answers} {r : Record α}
    (h : b.items.Perm b'.items) (he : evaluate b t as = .ok r) :
    ∃ r', evaluate b' t as = .ok r' ∧ r'.verdict = r.verdict ∧ r'.basis = r.basis ∧ r'.score = r.score ∧
      r'.used.Perm r.used ∧ r'.vetoed.Perm r.vetoed ∧ r'.faults.Perm r.faults := by
  obtain ⟨hv, ht, ho, rfl⟩ := (evaluate_ok_iff b t as r).mp he
  refine ⟨b'.run t as, (evaluate_ok_iff b' t as _).mpr ⟨valid_perm h hv, ht, outcomesKnown_perm h ho, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Battery.run
    rw [verdictOf_perm t (fires_perm h as).symm, scoreOf_perm h as]
  · unfold Battery.run
    rw [verdictOf_perm t (fires_perm h as).symm, scoreOf_perm h as]
  · unfold Battery.run; exact (scoreOf_perm h as).symm
  · unfold Battery.run; exact ((h.symm.filterMap _).map _)
  · unfold Battery.run; exact (((h.symm.filter _)).map _)
  · unfold Battery.run; exact (faults_perm h as).symm

/-! ### B19 and B20: the record -/

/-- B19: the record holds what it needs to be replayed; it has a score exactly when it has no fault. -/
theorem battery_record_replay {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as : Answers} {r : Record α}
    (he : evaluate b t as = .ok r) : evaluate r.battery r.table r.replies = .ok r ∧ ((∃ s, r.score = some s) ↔ r.faults = []) := by
  obtain ⟨hv, ht, ho, rfl⟩ := (evaluate_ok_iff b t as r).mp he
  refine ⟨he, ?_⟩
  exact scoreOf_some_iff_nofault hv as

/-- B20, `used`: the id and probability of each required item that read `ok`, in battery order. -/
theorem battery_record_used {α : Type} [DecidableEq α] {b : Battery α} {t : Table α} {as : Answers} {r : Record α}
    (he : evaluate b t as = .ok r) :
    r.used = (b.items.filterMap (Item.readOpt as)).map (fun e => (e.1.id, e.2)) ∧
    (∀ k p, (k, p) ∈ r.used ↔ ∃ it ∈ b.items, it.id = k ∧ it.required = true ∧ it.readIn as = .ok p) ∧
    (∀ k, k ∈ r.vetoed ↔ ∃ it ∈ b.items, it.id = k ∧ (it.fired as).isSome = true) ∧
    (∀ s, r.score = some s → Battery.score (b.pairs as) = .ok s ∧
      (b.pairs as).map (·.2) = r.used.map (·.2) ∧ (b.pairs as).map (·.1) = (b.reads as).map (·.1.weight)) := by
  obtain ⟨hv, ht, ho, rfl⟩ := (evaluate_ok_iff b t as r).mp he
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro k p
    unfold Battery.run Battery.reads
    simp only [List.mem_map, List.mem_filterMap]
    constructor
    · rintro ⟨e, ⟨it, hit, hx⟩, he⟩
      obtain ⟨h1, h2, h3⟩ := (readOpt_eq_some as it e).mp hx
      obtain ⟨e1, e2⟩ := e
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only at h1 h3
      subst h1
      exact ⟨e1, hit, rfl, h2, h3⟩
    · rintro ⟨it, hit, rfl, hr, hp⟩
      exact ⟨(it, p), ⟨it, hit, (readOpt_eq_some as it (it, p)).mpr ⟨rfl, hr, hp⟩⟩, rfl⟩
  · intro k
    unfold Battery.run
    simp only [List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨it, ⟨hit, hs⟩, rfl⟩; exact ⟨it, hit, rfl, hs⟩
    · rintro ⟨it, hit, rfl, hs⟩; exact ⟨it, ⟨hit, hs⟩, rfl⟩
  · intro s hs
    have := ((scoreOf_some_iff b as s).mp hs).2
    refine ⟨this, ?_, ?_⟩
    · unfold Battery.run Battery.pairs; simp [List.map_map, Function.comp_def]
    · unfold Battery.pairs; simp [List.map_map, Function.comp_def]

/-! ## Vectors (spec 14.7) -/

instance Battery.exceptDecEq {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

inductive Out where
  | reject | review | approve
  deriving DecidableEq, Repr

def pr (n : Nat) (h : n ≤ scale := by decide) : Prob := ⟨n, h⟩

def itA : Item Out := ⟨"a", 2, .decidable, none⟩
def itB : Item Out := ⟨"b", 1, .judgmental, none⟩
def itC : Item Out := ⟨"c", 1, .judgmental, none⟩
def itD : Item Out := ⟨"d", 0, .judgmental, none⟩
def itS : Item Out := ⟨"s", 0, .judgmental, some ⟨pr 900000, .reject⟩⟩
def itT : Item Out := ⟨"t", 0, .judgmental, some ⟨pr 500000, .review⟩⟩

def bat1 : Battery Out := ⟨[itA, itB, itC, itD]⟩
def bat2 : Battery Out := ⟨[itA, itB, itS]⟩
def bat3 : Battery Out := ⟨[itA, itB, itS, itT]⟩

def table1 : Table Out := ⟨[⟨.reject, 0, 3 / 10⟩, ⟨.review, 2 / 5, 7 / 10⟩, ⟨.approve, 7 / 10, 1⟩]⟩
def table1w : Table Out := ⟨[⟨.reject, 0, 3 / 10⟩, ⟨.review, 3 / 10, 7 / 10⟩, ⟨.approve, 7 / 10, 1⟩]⟩

def ans (n : Nat) (h : n ≤ scale := by decide) : Reply := .answer (.noul (pr n h))

def bv1 : Answers := [("a", .code true), ("b", ans 800000), ("c", ans 600000)]

example : table1.Valid := by decide +kernel
example : table1w.Valid := by decide +kernel
example : bat1.Valid := by decide +kernel
example : bat1.check = .ok () := by decide +kernel
example : table1.check = .ok () := by decide +kernel
example : bat2.Valid ∧ bat3.Valid := by decide +kernel

-- BV1: 17/20, approve, `used` a b c.
example : (evaluate bat1 table1 bv1).map (·.score) = .ok (some (17 / 20)) := by decide +kernel
example : (evaluate bat1 table1 bv1).map (·.verdict) = .ok (.decided .approve) := by decide +kernel
example : (evaluate bat1 table1 bv1).map (·.basis) = .ok .score := by decide +kernel
example : (evaluate bat1 table1 bv1).map (·.used.map (·.1)) = .ok ["a", "b", "c"] := by decide +kernel
-- BV2: 7/20 is in the gap.
example : (evaluate bat1 table1 [("a", .code false), ("b", ans 800000), ("c", ans 600000)]).map (fun r => (r.score, r.verdict, r.basis)) =
    .ok (some (7 / 20), .abstain, .gap) := by decide +kernel
-- BV3: 3/20 rejects.
example : (evaluate bat1 table1 [("a", .code false), ("b", ans 400000), ("c", ans 200000)]).map (·.verdict) = .ok (.decided .reject) := by decide +kernel
-- BV4: d (weight 0) changes nothing.
example : (evaluate bat1 table1 (bv1 ++ [("d", ans 1000000)])).map (fun r => (r.score, r.verdict)) = .ok (some (17 / 20), .decided .approve) := by decide +kernel
-- BV5 to BV8: faults.
example : (evaluate bat1 table1 [("a", .code true), ("c", ans 600000)]).map (fun r => (r.verdict, r.basis, r.score)) =
    .ok (.abstain, .fault, (none : Option Rat)) := by decide +kernel
example : (evaluate bat1 table1 [("a", .code true), ("c", ans 600000)]).map (·.faults) = .ok [("b", .missing)] := by decide +kernel
example : (evaluate bat1 table1 [("a", .code true), ("b", .refused ⟨.outOfRange, "x"⟩), ("c", ans 600000)]).map (fun r => (r.verdict, r.faults)) =
    .ok (.abstain, [("b", .refused ⟨.outOfRange, "x"⟩)]) := by decide +kernel
example : (evaluate bat1 table1 [("a", .answer (.noul (pr 1000000))), ("b", ans 800000), ("c", ans 600000)]).map (fun r => (r.verdict, r.score, r.faults)) =
    .ok (.abstain, none, [("a", .wrongKind)]) := by decide +kernel
example : (evaluate bat1 table1 (bv1 ++ [("e", .code true)])).map (fun r => (r.verdict, r.basis, r.score)) =
    .ok (.abstain, .fault, (none : Option Rat)) := by decide +kernel
example : (evaluate bat1 table1 (bv1 ++ [("e", .code true)])).map (·.faults) = .ok [("e", .unexpectedAnswer)] := by decide +kernel
-- BV9, BV18: the author's errors.
example : evaluate (⟨[⟨"a", 0, .decidable, none⟩, ⟨"b", 0, .judgmental, none⟩]⟩ : Battery Out) table1 [] = .error ⟨.allWeightsZero, "items"⟩ := by decide +kernel
example : evaluate (⟨[itA, itB, ⟨"a", 0, .judgmental, some ⟨pr 900000, .reject⟩⟩]⟩ : Battery Out) table1 [] = .error ⟨.duplicateId, "items[2].id"⟩ := by decide +kernel
-- BV10 to BV13: veto.
def bv10 : Answers := [("a", .code true), ("b", ans 900000), ("s", ans 950000)]
def bv13 : Answers := [("a", .code true), ("b", ans 900000), ("s", ans 950000), ("t", ans 600000)]
example : (evaluate bat2 table1 bv10).map (fun r => (r.score, r.verdict, r.basis, r.vetoed, r.used.map (·.1))) =
    .ok (some (29 / 30), .decided .reject, .veto, ["s"], ["a", "b", "s"]) := by decide +kernel
example : (evaluate bat2 table1 [("a", .code true), ("s", ans 950000)]).map (fun r => (r.score, r.verdict, r.basis, r.faults)) =
    .ok (none, .decided .reject, .veto, [("b", .missing)]) := by decide +kernel
example : (evaluate bat2 table1 [("a", .code true), ("b", ans 900000), ("s", ans 899999)]).map (fun r => (r.score, r.verdict)) =
    .ok (some (29 / 30), .decided .approve) := by decide +kernel
example : (evaluate bat3 table1 [("a", .code true), ("b", ans 900000), ("s", ans 950000), ("t", ans 600000)]).map (fun r => (r.verdict, r.basis, r.vetoed)) =
    .ok (.abstain, .vetoConflict, ["s", "t"]) := by decide +kernel
-- BV14 to BV17: the cut points.
example : (evaluate bat1 table1 [("a", .code true), ("b", ans 500000), ("c", ans 300000)]).map (fun r => (r.score, r.verdict)) = .ok (some (7 / 10), .decided .approve) := by decide +kernel
example : (evaluate bat1 table1 [("a", .code false), ("b", ans 700000), ("c", ans 500000)]).map (fun r => (r.score, r.verdict, r.basis)) = .ok (some (3 / 10), .abstain, .gap) := by decide +kernel
example : (evaluate bat1 table1 [("a", .code false), ("b", ans 900000), ("c", ans 700000)]).map (fun r => (r.score, r.verdict)) = .ok (some (2 / 5), .decided .review) := by decide +kernel
example : (evaluate bat1 table1 [("a", .code true), ("b", ans 1000000), ("c", ans 1000000)]).map (fun r => (r.score, r.verdict)) = .ok (some 1, .decided .approve) := by decide +kernel

-- B1: one battery or table violating each code, at its path.
example : (⟨[]⟩ : Battery Out).check = .error ⟨.noItems, "items"⟩ := by decide +kernel
example : (⟨List.replicate 65 itA⟩ : Battery Out).check = .error ⟨.tooManyItems, "items"⟩ := by decide +kernel
example : (⟨[itA, ⟨"", 1, .decidable, none⟩]⟩ : Battery Out).check = .error ⟨.badItemId, "items[1].id"⟩ := by decide +kernel
example : (⟨[itA, ⟨"x", 1000001, .decidable, none⟩]⟩ : Battery Out).check = .error ⟨.weightTooLarge, "items[1].weight"⟩ := by decide +kernel
example : (⟨[itA, ⟨"x", 1, .decidable, some ⟨pr 0, .reject⟩⟩]⟩ : Battery Out).check = .error ⟨.badVetoThreshold, "items[1].veto.threshold"⟩ := by decide +kernel
example : (⟨[⟨"a", 0, .decidable, none⟩]⟩ : Battery Out).check = .error ⟨.allWeightsZero, "items"⟩ := by decide +kernel
example : (⟨[itA, itB, ⟨"a", 0, .judgmental, none⟩]⟩ : Battery Out).check = .error ⟨.duplicateId, "items[2].id"⟩ := by decide +kernel
example : evaluate bat2 (⟨[⟨.approve, 0, 1⟩]⟩ : Table Out) [] = .error ⟨.vetoOutcomeUnknown, "items[2].veto.outcome"⟩ := by decide +kernel
example : (⟨[]⟩ : Table Out).check = .error ⟨.noBands, "bands"⟩ := by decide +kernel
example : (⟨List.replicate 17 ⟨Out.reject, 0, 1⟩⟩ : Table Out).check = .error ⟨.tooManyBands, "bands"⟩ := by decide +kernel
example : (⟨[⟨Out.reject, 1, 1⟩]⟩ : Table Out).check = .error ⟨.bandRange, "bands[0]"⟩ := by decide +kernel
example : (⟨[⟨Out.reject, 0, 1⟩, ⟨.review, 1 / 2, 1⟩]⟩ : Table Out).check = .error ⟨.bandOrder, "bands[1]"⟩ := by decide +kernel

-- B2: BV1 gives 17/20 (weights 2, 1, 1, 0).
example : Battery.score [(2, pr 1000000), (1, pr 800000), (1, pr 600000), (0, pr 0)] = .ok (17 / 20) := by decide +kernel
-- B3: `b` from 0.8 to 0.9 gives 7/8, and a positive weight raises the score strictly.
example : Battery.score [(2, pr 1000000), (1, pr 900000), (1, pr 600000)] = .ok (7 / 8) := by decide +kernel
example : (17 / 20 : Rat) < 7 / 8 := by decide +kernel
example : Battery.score ([(2, pr 1000000)] ++ (1, pr 800000) :: [(1, pr 600000)]) = .ok (17 / 20) ∧
    Battery.score ([(2, pr 1000000)] ++ (1, pr 900000) :: [(1, pr 600000)]) = .ok (7 / 8) := by decide +kernel
-- B4: BV1 reversed.
example : Battery.score [(0, pr 0), (1, pr 600000), (1, pr 800000), (2, pr 1000000)] = .ok (17 / 20) := by decide +kernel
example : [(2, pr 1000000), (1, pr 800000), (1, pr 600000), (0, pr 0)].Perm [(0, pr 0), (1, pr 600000), (1, pr 800000), (2, pr 1000000)] := by decide +kernel
-- B5: `d` at 0 and at 1.
example : Battery.score [(2, pr 1000000), (1, pr 800000), (1, pr 600000), (0, pr 1000000)] = .ok (17 / 20) := by decide +kernel
-- B6: all zero.
example : Battery.score [(0, pr 0), (0, pr 500000)] = .error ⟨.allWeightsZero, "items"⟩ := by decide +kernel
example : Battery.score [(1, pr 0)] = .ok 0 := by decide +kernel

-- B7 to B11, B16, B19, B20 on the vectors above: the hypotheses hold.
example : (evaluate bat1 table1 bv1).map (·.verdict) = .ok (.decided .approve) := by decide +kernel
example : (evaluate bat2 table1 bv10).map (·.verdict) = .ok (.decided .reject) := by decide +kernel
example : bat2.fires bv10 = [Out.reject] := by decide +kernel
example : bat1.faults [("a", .code true), ("c", ans 600000)] = [("b", .missing)] := by decide +kernel
example : bat1.fires [("a", .code true), ("c", ans 600000)] = [] := by decide +kernel
example : (bat2.run table1 [("a", .code true), ("s", ans 950000)]).faults = [("b", .missing)] := by decide +kernel
-- B9: the only veto item is `s`; the other answer is missing (BV11).
example : ∀ it' ∈ bat2.items, it'.veto ≠ none → it' = itS := by decide +kernel
example : itS.fired [("a", .code true), ("s", ans 950000)] = some Out.reject := by decide +kernel
-- B10: BV13.
example : itS.fired bv13 = some Out.reject ∧ itT.fired bv13 = some Out.review := by decide +kernel
-- B11: no veto item at all, and a veto not reached (BV12).
example : ∀ it ∈ bat1.items, it.veto = none := by decide +kernel
example : bat1.faults bv1 = [] := by decide +kernel
example : bat1.scoreOf bv1 = some (17 / 20) := by decide +kernel
example : bat2.fires [("a", .code true), ("b", ans 900000), ("s", ans 899999)] = [] := by decide +kernel
-- B12: 0.7 and 1 are each in one band of table 1.
example : table1.index (7 / 10) = some 2 := by decide +kernel
example : table1.index 1 = some 2 := by decide +kernel
-- B13: 0.35 abstains; 0.15 (reject) <= 0.4 (review) <= 0.7 (approve).
example : table1.index (7 / 20) = none := by decide +kernel
example : table1.index (3 / 20) = some 0 ∧ table1.index (2 / 5) = some 1 ∧ table1.index (7 / 10) = some 2 := by decide +kernel
example : (3 / 20 : Rat) ≤ 2 / 5 := by decide +kernel
-- B14: the cut points of BV14 to BV17.
example : table1.index (3 / 10) = none := by decide +kernel
example : table1.index (2 / 5) = some 1 ∧ table1.index (7 / 10) = some 2 ∧ table1.index 0 = some 0 := by decide +kernel
example : table1.bands[0]? = some ⟨Out.reject, 0, 3 / 10⟩ ∧ table1.bands[1]? = some ⟨Out.review, 2 / 5, 7 / 10⟩ := by decide +kernel
example : table1w.index (3 / 10) = some 1 := by decide +kernel
-- B15: the widened table has no gap and covers every score; BV2 abstains on the original.
example : table1w.Gapless := by decide +kernel
example : ¬ table1.Gapless := by decide +kernel
example : table1w.index (7 / 20) = some 1 := by decide +kernel
example : (evaluate bat1 table1w [("a", .code false), ("b", ans 800000), ("c", ans 600000)]).map (·.verdict) = .ok (.decided .review) := by decide +kernel
-- B16: every decided vector decides a band outcome.
example : Out.approve ∈ table1.bands.map (·.outcome) := by decide +kernel
-- B17: BV3 (reject) below BV1 (approve); `b` at 0.8 and at 0.9 both approve.
example : (evaluate bat1 table1 [("a", .code true), ("b", ans 900000), ("c", ans 600000)]).map (·.verdict) = .ok (.decided .approve) := by decide +kernel
example : bat1.pairs bv1 = [] ++ (2, pr 1000000) :: [(1, pr 800000), (1, pr 600000)] := by decide +kernel
-- B18: BV1 reversed.
example : (evaluate ⟨bat1.items.reverse⟩ table1 bv1).map (fun r => (r.verdict, r.basis, r.score)) = .ok (.decided .approve, .score, some (17 / 20)) := by decide +kernel
example : (evaluate ⟨bat3.items.reverse⟩ table1 bv13).map (fun r => (r.verdict, r.basis)) = .ok (.abstain, .vetoConflict) := by decide +kernel
example : bat1.items.Perm bat1.items.reverse := (List.reverse_perm _).symm
-- B19: the record replays (BV1, BV5, BV10).
example : (evaluate bat1 table1 bv1).bind (fun r => evaluate r.battery r.table r.replies) = evaluate bat1 table1 bv1 := by decide +kernel
example : (evaluate bat1 table1 [("a", .code true), ("c", ans 600000)]).bind (fun r => evaluate r.battery r.table r.replies) =
    evaluate bat1 table1 [("a", .code true), ("c", ans 600000)] := by decide +kernel
example : (evaluate bat2 table1 bv10).bind (fun r => evaluate r.battery r.table r.replies) = evaluate bat2 table1 bv10 := by decide +kernel
-- B20: BV10: `used` has a, b, s and `vetoed = [s]`.
example : (evaluate bat2 table1 bv10).map (fun r => (r.used.map (·.1), r.vetoed)) = .ok (["a", "b", "s"], ["s"]) := by decide +kernel

end VbmDecision
