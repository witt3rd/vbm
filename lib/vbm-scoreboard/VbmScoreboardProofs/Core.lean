import VbmScoreboard.Core
import VbmScoreboardProofs.Direction
/-! # The scoreboard core, proved

Every theorem about `VbmScoreboard.Core`, each with a non-vacuity witness (`example`) over small concrete baselines.

* `check_complete`, `check_held_iff`, `check_unmeasured_fails`, `passes_iff_no_regression`: one verdict per floor; held exactly when a reading is at least as good; an unmeasured floor fails closed.
* `bank_monotone`, `bank_idempotent`, `bank_never_worse`, `bank_then_check_passes`: banking only moves a floor toward better, twice is once, a worse reading changes nothing, and what passed still passes.
* `reset_requires_reason`, `reset_only_loosens`, `reset_recorded`: a reset needs a reason and an author, only loosens, and yields its history entry.
* `history_append_only`: a history only grows at its end.
* `progress_bounds`, `progress_target_reached`, `progress_monotone_in_now`: progress is within 0 and 1000, is 1000 once the target is reached, and never falls as `now` improves.

The order `Direction.better` and its laws are in `VbmScoreboardProofs.Direction`. -/
namespace VbmScoreboard

/-! ## Small lemmas -/

theorem verdictOf_held_iff (rs : List Reading) (f : Floor) :
    (verdictOf rs f).isHeld = true ↔
      ∃ v, lookup rs f.metric = some v ∧ Direction.better f.direction v f.value = true := by
  unfold verdictOf
  cases h : lookup rs f.metric with
  | none => simp [Verdict.isHeld]
  | some v =>
    by_cases hb : Direction.better f.direction v f.value = true <;> simp [hb, Verdict.isHeld]

theorem passes_iff_all_held (vs : List Verdict) :
    passes vs = true ↔ ∀ v ∈ vs, v.isHeld = true := by
  simp [passes]

/-! ## check -/

/-- `check` gives one verdict per floor. -/
theorem check_complete (b : Baseline) (rs : List Reading) :
    (check b rs).length = b.length := by
  simp [check]

example : (check [⟨"a", .higher, 5⟩, ⟨"b", .lower, 3⟩] [⟨"a", 6⟩]).length = 2 := by decide +kernel

/-- The verdict at a floor's position is held iff a reading exists and is at least as good as the floor. -/
theorem check_held_iff (b : Baseline) (rs : List Reading) (i : Nat) (f : Floor)
    (hi : b[i]? = some f) :
    (∃ v, (check b rs)[i]? = some v ∧ v.isHeld = true) ↔
      ∃ n, lookup rs f.metric = some n ∧ Direction.better f.direction n f.value = true := by
  rw [← verdictOf_held_iff]
  simp [check, List.getElem?_map, hi]

example : (check [⟨"a", .higher, 5⟩] [⟨"a", 5⟩])[0]? = some .held := by decide +kernel
example : (check [⟨"a", .higher, 5⟩] [⟨"a", 4⟩])[0]? = some (.regressed "a" 5 4) := by decide +kernel
example : (check [⟨"a", .lower, 5⟩] [⟨"a", 4⟩])[0]? = some .held := by decide +kernel

/-- A floor with no reading is never held, so `passes` is false: fail closed. -/
theorem check_unmeasured_fails (b : Baseline) (rs : List Reading) (f : Floor) (hf : f ∈ b)
    (hn : lookup rs f.metric = none) :
    Verdict.unmeasured f.metric ∈ check b rs ∧ passes (check b rs) = false := by
  have hv : verdictOf rs f = .unmeasured f.metric := by simp [verdictOf, hn]
  refine ⟨?_, ?_⟩
  · exact List.mem_map.2 ⟨f, hf, hv⟩
  · cases hp : passes (check b rs)
    · rfl
    · have := (passes_iff_all_held _).1 hp (verdictOf rs f) (List.mem_map.2 ⟨f, hf, rfl⟩)
      simp [hv, Verdict.isHeld] at this

example : passes (check [⟨"a", .higher, 5⟩] []) = false ∧
    passes (check [⟨"a", .higher, 5⟩] [⟨"a", 5⟩]) = true := by decide +kernel

/-- `passes` holds exactly when no floor regressed and none is unmeasured: every floor has a reading at least as good. -/
theorem passes_iff_no_regression (b : Baseline) (rs : List Reading) :
    passes (check b rs) = true ↔
      ∀ f ∈ b, ∃ v, lookup rs f.metric = some v ∧ Direction.better f.direction v f.value = true := by
  rw [passes_iff_all_held]
  constructor
  · intro h f hf
    exact (verdictOf_held_iff rs f).1 (h _ (List.mem_map.2 ⟨f, hf, rfl⟩))
  · intro h v hv
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hv
    exact (verdictOf_held_iff rs f).2 (h f hf)

example : passes (check [⟨"a", .higher, 5⟩, ⟨"b", .lower, 3⟩] [⟨"a", 7⟩, ⟨"b", 3⟩]) = true := by decide +kernel
example : passes (check [⟨"a", .higher, 5⟩, ⟨"b", .lower, 3⟩] [⟨"a", 7⟩, ⟨"b", 4⟩]) = false := by decide +kernel

/-! ## bank -/

theorem bankFloor_idem (rs : List Reading) (f : Floor) :
    bankFloor rs (bankFloor rs f) = bankFloor rs f := by
  unfold bankFloor
  cases h : lookup rs f.metric with
  | none => simp [h]
  | some v =>
    by_cases hb : Direction.better f.direction v f.value = true
    · simp [hb, h, Direction.better_refl]
    · simp [hb, h]

theorem bankFloor_fixed (rs : List Reading) (f : Floor) (h : lookup rs f.metric = some f.value) :
    bankFloor rs f = f := by
  simp [bankFloor, h, Direction.better_refl]

theorem addNew_prefix (rs : List Reading) (ms : List Metric) (b : Baseline) :
    ∃ extra, addNew rs ms b = b ++ extra := by
  induction ms generalizing b with
  | nil => exact ⟨[], by simp [addNew]⟩
  | cons m rest ih =>
    unfold addNew
    cases h : lookup rs m.name with
    | none => exact ih b
    | some v =>
      by_cases hf : hasFloor b m.name = true
      · simp [hf]; exact ih b
      · simp [hf]
        obtain ⟨e, he⟩ := ih (b ++ [{ metric := m.name, direction := m.direction, value := v }])
        exact ⟨{ metric := m.name, direction := m.direction, value := v } :: e, by rw [he]; simp⟩

theorem addNew_mem (rs : List Reading) (ms : List Metric) (b : Baseline) (f : Floor)
    (hf : f ∈ addNew rs ms b) : f ∈ b ∨ lookup rs f.metric = some f.value := by
  induction ms generalizing b with
  | nil => exact Or.inl (by simpa [addNew] using hf)
  | cons m rest ih =>
    unfold addNew at hf
    cases h : lookup rs m.name with
    | none => rw [h] at hf; exact ih b (by simpa using hf)
    | some v =>
      rw [h] at hf
      by_cases hh : hasFloor b m.name = true
      · simp [hh] at hf; exact ih b hf
      · simp [hh] at hf
        rcases ih _ hf with h1 | h1
        · rcases List.mem_append.1 h1 with h2 | h2
          · exact Or.inl h2
          · right
            simp at h2
            subst h2
            simpa using h
        · exact Or.inr h1

theorem addNew_hasFloor (rs : List Reading) (ms : List Metric) (b : Baseline) (m : Metric)
    (hm : m ∈ ms) (v : Nat) (hv : lookup rs m.name = some v) :
    hasFloor (addNew rs ms b) m.name = true := by
  induction ms generalizing b with
  | nil => simp at hm
  | cons m' rest ih =>
    have keep : ∀ b' : Baseline, hasFloor b' m.name = true →
        hasFloor (addNew rs rest b') m.name = true := by
      intro b' hb'
      obtain ⟨e, he⟩ := addNew_prefix rs rest b'
      rw [he]; simp [hasFloor, List.any_append] at hb' ⊢; exact Or.inl hb'
    unfold addNew
    cases h : lookup rs m'.name with
    | none =>
      simp only []
      rcases List.mem_cons.1 hm with rfl | hm'
      · simp [h] at hv
      · exact ih b hm'
    | some w =>
      simp only []
      by_cases hh : hasFloor b m'.name = true
      · simp only [hh, ite_true]
        rcases List.mem_cons.1 hm with rfl | hm'
        · exact keep b hh
        · exact ih b hm'
      · simp only [hh]
        rcases List.mem_cons.1 hm with rfl | hm'
        · apply keep
          simp [hasFloor, List.any_append]
        · exact ih _ hm'

theorem addNew_noop (rs : List Reading) (ms : List Metric) (b : Baseline)
    (h : ∀ m ∈ ms, ∀ v, lookup rs m.name = some v → hasFloor b m.name = true) :
    addNew rs ms b = b := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    unfold addNew
    cases hl : lookup rs m.name with
    | none => simp only []; exact ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
    | some v =>
      simp only []
      have := h m (List.mem_cons_self ..) v hl
      simp only [this, ite_true]
      exact ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))

/-- After `bank`, the floor at each earlier position is at least as good as before (per its direction), same metric and direction. -/
theorem bank_monotone (ms : List Metric) (b : Baseline) (rs : List Reading) (i : Nat) (f : Floor)
    (hi : b[i]? = some f) :
    ∃ g, (bank ms b rs)[i]? = some g ∧ g.metric = f.metric ∧ g.direction = f.direction ∧
      Direction.better f.direction g.value f.value = true := by
  obtain ⟨e, he⟩ := addNew_prefix rs ms (b.map (bankFloor rs))
  have hmap : (b.map (bankFloor rs))[i]? = some (bankFloor rs f) := by simp [hi]
  have hlt : i < (b.map (bankFloor rs)).length := (List.getElem?_eq_some_iff.1 hmap).1
  refine ⟨bankFloor rs f, ?_, ?_⟩
  · unfold bank; rw [he, List.getElem?_append_left hlt]; exact hmap
  · unfold bankFloor
    cases h : lookup rs f.metric with
    | none => simp [Direction.better_refl]
    | some v =>
      by_cases hb : Direction.better f.direction v f.value = true
      · simp [hb]
      · simp [hb, Direction.better_refl]

example : bank [] [⟨"a", .higher, 5⟩] [⟨"a", 7⟩] = [⟨"a", .higher, 7⟩] := by decide +kernel
example : bank [] [⟨"a", .lower, 5⟩] [⟨"a", 3⟩] = [⟨"a", .lower, 3⟩] := by decide +kernel
example : bank [⟨"b", .lower⟩] [⟨"a", .higher, 5⟩] [⟨"a", 7⟩, ⟨"b", 9⟩] =
    [⟨"a", .higher, 7⟩, ⟨"b", .lower, 9⟩] := by decide +kernel

/-- Banking the same readings twice equals once. -/
theorem bank_idempotent (ms : List Metric) (b : Baseline) (rs : List Reading) :
    bank ms (bank ms b rs) rs = bank ms b rs := by
  have hmem : ∀ f ∈ bank ms b rs, bankFloor rs f = f := by
    intro f hf
    rcases addNew_mem rs ms _ f hf with h1 | h1
    · obtain ⟨g, _, rfl⟩ := List.mem_map.1 h1
      exact bankFloor_idem rs g
    · exact bankFloor_fixed rs f h1
  have hfix : (bank ms b rs).map (bankFloor rs) = bank ms b rs := by
    rw [List.map_congr_left hmem]; exact List.map_id' _ |>.trans rfl
  unfold bank at hfix ⊢
  rw [hfix]
  apply addNew_noop
  intro m hm v hv
  exact addNew_hasFloor rs ms _ m hm v hv

example : bank [⟨"b", .lower⟩] [⟨"a", .higher, 5⟩] [⟨"a", 7⟩, ⟨"b", 9⟩] =
    bank [⟨"b", .lower⟩] (bank [⟨"b", .lower⟩] [⟨"a", .higher, 5⟩] [⟨"a", 7⟩, ⟨"b", 9⟩])
      [⟨"a", 7⟩, ⟨"b", 9⟩] := by decide +kernel

/-- A worse reading leaves the floor as it was. -/
theorem bank_never_worse (ms : List Metric) (b : Baseline) (rs : List Reading) (i : Nat)
    (f : Floor) (hi : b[i]? = some f) (v : Nat) (hl : lookup rs f.metric = some v)
    (hw : Direction.better f.direction v f.value = false) :
    (bank ms b rs)[i]? = some f := by
  obtain ⟨e, he⟩ := addNew_prefix rs ms (b.map (bankFloor rs))
  have hmap : (b.map (bankFloor rs))[i]? = some (bankFloor rs f) := by simp [hi]
  have hlt : i < (b.map (bankFloor rs)).length := (List.getElem?_eq_some_iff.1 hmap).1
  have hb : bankFloor rs f = f := by simp [bankFloor, hl, hw]
  unfold bank; rw [he, List.getElem?_append_left hlt, hmap, hb]

example : bank [] [⟨"a", .higher, 5⟩] [⟨"a", 4⟩] = [⟨"a", .higher, 5⟩] ∧
    bank [] [⟨"a", .lower, 5⟩] [⟨"a", 6⟩] = [⟨"a", .lower, 5⟩] := by decide +kernel

/-- If the readings pass the baseline, then after banking them the same readings still pass: the baseline never rejects what it just recorded. (Without the hypothesis a worse reading keeps its old floor and still regresses, and a floor with no reading stays unmeasured.) -/
theorem bank_then_check_passes (ms : List Metric) (b : Baseline) (rs : List Reading)
    (h : passes (check b rs) = true) : passes (check (bank ms b rs) rs) = true := by
  rw [passes_iff_no_regression] at h ⊢
  intro f hf
  rcases addNew_mem rs ms _ f hf with h1 | h1
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h1
    obtain ⟨v, hv, hb⟩ := h g hg
    refine ⟨v, ?_, ?_⟩
    · simp [bankFloor, hv, hb]
    · simp [bankFloor, hv, hb, Direction.better_refl]
  · exact ⟨f.value, h1, Direction.better_refl _ _⟩

example : passes (check (bank [] [⟨"a", .higher, 5⟩] [⟨"a", 7⟩]) [⟨"a", 7⟩]) = true := by decide +kernel
example : passes (check [⟨"a", .higher, 5⟩] [⟨"a", 7⟩]) = true := by decide +kernel

/-! ## reset -/

/-- An empty reason or an empty author is refused. -/
theorem reset_requires_reason (b : Baseline) (metric : String) (value : Nat)
    (reason author : String) (time : Nat) (h : reason = "" ∨ author = "") :
    ∃ r, reset b metric value reason author time = .error r := by
  unfold reset
  rcases h with h | h
  · exact ⟨.emptyReason, by simp [h]⟩
  · by_cases hr : reason = ""
    · exact ⟨.emptyReason, by simp [hr]⟩
    · exact ⟨.emptyAuthor, by simp [hr, h]⟩

example : reset [⟨"a", .higher, 5⟩] "a" 3 "" "me" 1 = .error .emptyReason := rfl
example : reset [⟨"a", .higher, 5⟩] "a" 3 "why" "" 1 = .error .emptyAuthor := rfl

/-- With a reason and an author, a reset to a better (or equal) value is refused and one to a worse value is accepted. -/
theorem reset_only_loosens (b : Baseline) (metric : String) (value : Nat)
    (reason author : String) (time : Nat) (f : Floor) (hf : floorOf b metric = some f)
    (hr : reason ≠ "") (ha : author ≠ "") :
    (Direction.better f.direction value f.value = true →
        reset b metric value reason author time = .error .notLooser) ∧
    (Direction.better f.direction value f.value = false →
        ∃ b' e, reset b metric value reason author time = .ok (b', e)) := by
  constructor
  · intro hb; simp [reset, hr, ha, hf, hb]
  · intro hb; simp [reset, hr, ha, hf, hb]

example : reset [⟨"a", .higher, 5⟩] "a" 7 "why" "me" 1 = .error .notLooser := rfl
example : reset [⟨"a", .higher, 5⟩] "a" 3 "why" "me" 1 =
    .ok ([⟨"a", .higher, 3⟩], ⟨1, "a", some 5, some 3, .reset "why" "me"⟩) := rfl
example : reset [⟨"a", .lower, 5⟩] "a" 8 "why" "me" 1 =
    .ok ([⟨"a", .lower, 8⟩], ⟨1, "a", some 5, some 8, .reset "why" "me"⟩) := rfl

/-- The history entry of an accepted reset names the metric, the old and the new value, the reason and the author. -/
theorem reset_recorded (b : Baseline) (metric : String) (value : Nat) (reason author : String)
    (time : Nat) (f : Floor) (hf : floorOf b metric = some f) (b' : Baseline) (e : Entry)
    (h : reset b metric value reason author time = .ok (b', e)) :
    e = ⟨time, metric, some f.value, some value, .reset reason author⟩ := by
  unfold reset at h
  by_cases hr : reason = ""
  · simp [hr] at h
  by_cases ha : author = ""
  · simp [hr, ha] at h
  by_cases hb : Direction.better f.direction value f.value = true
  · simp [hr, ha, hf, hb] at h
  · simp [hr, ha, hf, hb] at h
    exact h.2.symm

/-! ## history -/

/-- Adding an entry keeps every earlier entry, in place: the old history is a prefix of the new. -/
theorem history_append_only (h : History) (e : Entry) :
    h <+: record h e ∧ (record h e).length = h.length + 1 ∧ (∀ x ∈ h, x ∈ record h e) ∧
      e ∈ record h e := by
  refine ⟨List.prefix_append _ _, by simp [record], fun x hx => by simp [record, hx], by simp [record]⟩

example : record [⟨1, "a", none, some 5, .added⟩] ⟨2, "a", some 5, some 7, .banked⟩ =
    [⟨1, "a", none, some 5, .added⟩, ⟨2, "a", some 5, some 7, .banked⟩] := by decide +kernel

/-! ## progress -/

/-- Progress is between 0 and 1000 permille. -/
theorem progress_bounds (d : Direction) (floor target now : Nat) :
    0 ≤ progress d floor target now ∧ progress d floor target now ≤ 1000 := by
  refine ⟨Nat.zero_le _, ?_⟩
  unfold progress
  by_cases ht : gain d target floor = 0
  · simp [ht]
  · simp only [ht, ite_false]
    apply Nat.div_le_of_le_mul
    have := Nat.min_le_right (gain d now floor) (gain d target floor)
    have h2 := Nat.mul_le_mul_right 1000 this
    omega

example : progress .higher 10 20 15 = 500 ∧ progress .lower 20 10 15 = 500 ∧
    progress .higher 10 20 5 = 0 := by decide +kernel

/-- When the target is ahead of the floor and `now` has reached or passed it, progress is 1000. -/
theorem progress_target_reached (d : Direction) (floor target now : Nat)
    (hahead : 0 < gain d target floor) (hr : Direction.better d now target = true) :
    progress d floor target now = 1000 := by
  unfold progress
  have hne : gain d target floor ≠ 0 := Nat.pos_iff_ne_zero.1 hahead
  have hge : gain d target floor ≤ gain d now floor := by
    cases d <;> simp [Direction.better, gain] at hr ⊢ <;> omega
  simp only [hne, ite_false]
  rw [Nat.min_eq_right hge]
  exact Nat.mul_div_cancel_left 1000 hahead

/-- A target that is not ahead of the floor gives 0. -/
theorem progress_not_ahead (d : Direction) (floor target now : Nat)
    (h : gain d target floor = 0) : progress d floor target now = 0 := by
  simp [progress, h]

example : progress .higher 10 20 20 = 1000 ∧ progress .higher 10 20 99 = 1000 ∧
    progress .lower 20 10 7 = 1000 := by decide +kernel
example : progress .higher 10 10 50 = 0 ∧ progress .lower 10 20 5 = 0 := by decide +kernel

/-- A better `now` never lowers progress. -/
theorem progress_monotone_in_now (d : Direction) (floor target n1 n2 : Nat)
    (h : Direction.better d n2 n1 = true) :
    progress d floor target n1 ≤ progress d floor target n2 := by
  unfold progress
  by_cases ht : gain d target floor = 0
  · simp [ht]
  · simp only [ht, ite_false]
    apply Nat.div_le_div_right
    have hg : gain d n1 floor ≤ gain d n2 floor := by
      cases d <;> simp [Direction.better, gain] at h ⊢ <;> omega
    have : min (gain d n1 floor) (gain d target floor) ≤
        min (gain d n2 floor) (gain d target floor) := by omega
    exact Nat.mul_le_mul_right _ this

example : progress .higher 10 30 15 ≤ progress .higher 10 30 25 := by decide +kernel
example : progress .lower 30 10 25 ≤ progress .lower 30 10 15 := by decide +kernel

end VbmScoreboard
