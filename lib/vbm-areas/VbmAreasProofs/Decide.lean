import VbmAreas.Decide
import VbmAreasProofs.Area
/-! # The decision: proofs (S4) -/
namespace VbmAreas

variable (cfg : Config) (cs : List Change) (rc : Bool)

/-! ## The shape of the record -/

theorem full_eq : (cfg.decide cs rc).full = (rc || (cs.flatMap Change.split).any (fun c => cfg.gate c.path || cfg.unmappedAt c)) := rfl

theorem run_eq : (cfg.decide cs rc).run = if (cfg.decide cs rc).full = true then cfg.names else (cfg.decide cs rc).touched := rfl

theorem skipped_eq : (cfg.decide cs rc).skipped = cfg.names.filter (fun n => !(cfg.decide cs rc).run.contains n) := rfl

theorem touched_eq : (cfg.decide cs rc).touched = cfg.names.filter (fun n => ((cs.flatMap Change.split).flatMap cfg.hit).contains n) := rfl

theorem mem_touched (n : String) : n ∈ (cfg.decide cs rc).touched ↔ n ∈ cfg.names ∧ ∃ c ∈ cs.flatMap Change.split, n ∈ cfg.hit c := by
  simp only [touched_eq, List.mem_filter, List.contains_iff_mem, List.mem_flatMap]

theorem full_iff : (cfg.decide cs rc).full = true ↔ rc = true ∨ ∃ c ∈ cs.flatMap Change.split, cfg.gate c.path = true ∨ cfg.unmappedAt c = true := by
  rw [full_eq, Bool.or_eq_true, List.any_eq_true]
  simp only [Bool.or_eq_true]

theorem run_full (h : (cfg.decide cs rc).full = true) : (cfg.decide cs rc).run = cfg.names := by
  simp [run_eq, h]

theorem run_not_full (h : (cfg.decide cs rc).full = false) : (cfg.decide cs rc).run = (cfg.decide cs rc).touched := by
  simp [run_eq, h]

theorem touched_sub_names : ∀ n ∈ (cfg.decide cs rc).touched, n ∈ cfg.names := fun n h => ((mem_touched cfg cs rc n).1 h).1

/-! ## Touched, run, full -/

/-- Every touched area is in `run`: rules out a touched area that is skipped. -/
theorem touched_sub_run : ∀ n ∈ (cfg.decide cs rc).touched, n ∈ (cfg.decide cs rc).run := by
  intro n hn
  cases hf : (cfg.decide cs rc).full
  · rw [run_not_full cfg cs rc hf]; exact hn
  · rw [run_full cfg cs rc hf]; exact touched_sub_names cfg cs rc n hn

/-- Nothing full: `run` is exactly `touched`; rules out an untouched area that runs without a reason. -/
theorem run_eq_touched (h : (cfg.decide cs rc).full = false) : (cfg.decide cs rc).run = (cfg.decide cs rc).touched := run_not_full cfg cs rc h

/-- Full: `run` is every area (and `inert` when declared) and nothing is skipped. -/
theorem full_run_all (h : (cfg.decide cs rc).full = true) : (cfg.decide cs rc).run = cfg.names ∧ (cfg.decide cs rc).skipped = [] := by
  refine ⟨run_full cfg cs rc h, ?_⟩
  rw [skipped_eq, run_full cfg cs rc h]
  simp

/-- The release candidate runs every area and skips none. -/
theorem rc_runs_all (h : rc = true) : (cfg.decide cs rc).run = cfg.names ∧ (cfg.decide cs rc).skipped = [] :=
  full_run_all cfg cs rc ((full_iff cfg cs rc).2 (Or.inl h))

/-- An unmapped path makes the landing full: rules out a silent skip. -/
theorem unmapped_full (h : (cfg.decide cs rc).unmapped ≠ []) : (cfg.decide cs rc).full = true := by
  rw [full_iff]
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ h
  simp only [Config.decide, List.mem_map, List.mem_filter] at hp
  obtain ⟨c, ⟨hc, hu⟩, _⟩ := hp
  exact Or.inr ⟨c, List.mem_flatMap.2 (by simpa using hc), Or.inr hu⟩

theorem gate_not_unmapped (c : Change) (h : cfg.gate c.path = true) : cfg.unmappedAt c = false := by
  simp [Config.unmappedAt, h]

/-- A gate-defining path makes the landing full, is listed as gate-defining, and is never listed as unmapped, even when an area owns it. -/
theorem gate_full (c : Change) (hc : c ∈ cs.flatMap Change.split) (h : cfg.gate c.path = true) :
    (cfg.decide cs rc).full = true ∧ c.path ∈ (cfg.decide cs rc).gateDefining ∧ c.path ∉ (cfg.decide cs rc).unmapped := by
  refine ⟨(full_iff cfg cs rc).2 (Or.inr ⟨c, hc, Or.inl h⟩), ?_, ?_⟩
  · simp only [Config.decide, List.mem_map, List.mem_filter]
    exact ⟨c, ⟨hc, h⟩, rfl⟩
  · simp only [Config.decide, List.mem_map, List.mem_filter, not_exists, not_and]
    intro c' ⟨_, hu⟩ e
    have : cfg.gate c'.path = true := by rw [e]; exact h
    simp [gate_not_unmapped cfg c' this] at hu

/-! ## Owned implies touched; renames -/

/-- A change one of whose ends is owned by an area touches that area (the end of a rename included); overlap is the dependency: two owners are both touched. -/
theorem owned_touched (ch : Change) (hch : ch ∈ cs) (c : Change) (hc : c ∈ ch.split) (a : Area) (ha : a ∈ cfg.file.areas)
    (ho : cfg.areaOwns a c = true) : a.name ∈ (cfg.decide cs rc).touched := by
  rw [mem_touched]
  have hmem : a.name ∈ cfg.owners c := by
    simp only [Config.owners, List.mem_append, List.mem_map, List.mem_filter]
    exact Or.inl ⟨a, ⟨ha, ho⟩, rfl⟩
  have hn : a.name ∈ cfg.names := by simp [Config.names, List.mem_map]; exact Or.inl ⟨a, ha, rfl⟩
  refine ⟨hn, c, List.mem_flatMap.2 ⟨ch, hch, hc⟩, ?_⟩
  have hne : (cfg.owners c).isEmpty = false := by
    cases h : cfg.owners c with
    | nil => simp [h] at hmem
    | cons => rfl
  simp [Config.hit, hne, hmem]

/-- With an areas file, an area that owns a path touches it on the path alone (no inert carve-out applies). -/
theorem owned_touched_file (f : Areas) (hf : cfg.areas = some f) (ch : Change) (hch : ch ∈ cs) (c : Change) (hc : c ∈ ch.split)
    (a : Area) (ha : a ∈ f.file.areas) (ho : a.owns c.path = true) : a.name ∈ (cfg.decide cs rc).touched :=
  owned_touched cfg cs rc ch hch c hc a (by simp [Config.file, hf, ha]) (by simp [Config.areaOwns, hf, ho])

theorem split_idem (l : List Change) : (l.flatMap Change.split).flatMap Change.split = l.flatMap Change.split := by
  induction l with
  | nil => rfl
  | cons c r ih =>
    simp only [List.flatMap_cons, List.flatMap_append, ih]
    congr 1
    cases h : c.renamedFrom <;> simp [Change.split, h]

/-- The decision depends on the changes only through their split. -/
theorem decide_congr (cs cs' : List Change) (h : cs.flatMap Change.split = cs'.flatMap Change.split) : cfg.decide cs rc = cfg.decide cs' rc := by
  simp only [Config.decide, h]

/-- A rename is a deletion of the old path plus an addition of the new: `split` says so. -/
theorem split_rename (c : Change) (old : String) (h : c.renamedFrom = some old) :
    c.split = [⟨.deleted, old, none⟩, ⟨.added, c.path, none⟩] := by simp [Change.split, h]

/-- A rename touches exactly what its two ends touch: the decision on the rename is the decision on the deletion and the addition. -/
theorem rename_decide (c : Change) (old : String) (h : c.renamedFrom = some old) (rest : List Change) :
    cfg.decide (c :: rest) rc = cfg.decide (⟨.deleted, old, none⟩ :: ⟨.added, c.path, none⟩ :: rest) rc := by
  apply decide_congr
  have e1 : Change.split ⟨.deleted, old, none⟩ = [⟨.deleted, old, none⟩] := rfl
  have e2 : Change.split ⟨.added, c.path, none⟩ = [⟨.added, c.path, none⟩] := rfl
  simp only [List.flatMap_cons, split_rename c old h, e1, e2]
  rfl

/-- `touched` of two lists of changes is the union of the two (as sets): the decision is a function of each change alone. -/
theorem touched_append (c1 c2 : List Change) (n : String) :
    n ∈ (cfg.decide (c1 ++ c2) rc).touched ↔ n ∈ (cfg.decide c1 rc).touched ∨ n ∈ (cfg.decide c2 rc).touched := by
  simp only [mem_touched, List.flatMap_append, List.mem_append]
  constructor
  · rintro ⟨hn, c, hc | hc, h⟩
    · exact Or.inl ⟨hn, c, hc, h⟩
    · exact Or.inr ⟨hn, c, hc, h⟩
  · rintro (⟨hn, c, hc, h⟩ | ⟨hn, c, hc, h⟩)
    · exact ⟨hn, c, Or.inl hc, h⟩
    · exact ⟨hn, c, Or.inr hc, h⟩

/-- The touched set of a rename is the union of the touched sets of its deletion and its addition. -/
theorem rename_touched (c : Change) (old : String) (h : c.renamedFrom = some old) (n : String) :
    n ∈ (cfg.decide [c] rc).touched ↔ n ∈ (cfg.decide [⟨.deleted, old, none⟩] rc).touched ∨ n ∈ (cfg.decide [⟨.added, c.path, none⟩] rc).touched := by
  rw [← touched_append cfg rc [_] [_] n]
  exact iff_of_eq (congrArg (fun d => n ∈ d.touched) (rename_decide cfg rc c old h []))

/-! ## Monotonicity -/

theorem flatMap_sub {α β : Type} (f : α → List β) {l l' : List α} (h : ∀ x ∈ l, x ∈ l') : ∀ y ∈ l.flatMap f, y ∈ l'.flatMap f := by
  intro y hy
  obtain ⟨x, hx, hy⟩ := List.mem_flatMap.1 hy
  exact List.mem_flatMap.2 ⟨x, h x hx, hy⟩

/-- Adding changed paths never shrinks `touched`, `run`, `unmapped` and never turns `full` off. -/
theorem monotone (cs' : List Change) (h : ∀ c ∈ cs, c ∈ cs') :
    (∀ n ∈ (cfg.decide cs rc).touched, n ∈ (cfg.decide cs' rc).touched) ∧
    (∀ n ∈ (cfg.decide cs rc).run, n ∈ (cfg.decide cs' rc).run) ∧
    (∀ n ∈ (cfg.decide cs rc).unmapped, n ∈ (cfg.decide cs' rc).unmapped) ∧
    ((cfg.decide cs rc).full = true → (cfg.decide cs' rc).full = true) := by
  have hs := flatMap_sub Change.split h
  have ht : ∀ n ∈ (cfg.decide cs rc).touched, n ∈ (cfg.decide cs' rc).touched := by
    intro n hn
    obtain ⟨hn, c, hc, hh⟩ := (mem_touched cfg cs rc n).1 hn
    exact (mem_touched cfg cs' rc n).2 ⟨hn, c, hs c hc, hh⟩
  have hf : (cfg.decide cs rc).full = true → (cfg.decide cs' rc).full = true := by
    intro hf
    rcases (full_iff cfg cs rc).1 hf with h1 | ⟨c, hc, h2⟩
    · exact (full_iff cfg cs' rc).2 (Or.inl h1)
    · exact (full_iff cfg cs' rc).2 (Or.inr ⟨c, hs c hc, h2⟩)
  refine ⟨ht, ?_, ?_, hf⟩
  · intro n hn
    cases hf1 : (cfg.decide cs rc).full
    · rw [run_not_full cfg cs rc hf1] at hn
      exact touched_sub_run cfg cs' rc n (ht n hn)
    · rw [run_full cfg cs rc hf1] at hn
      rw [run_full cfg cs' rc (hf hf1)]; exact hn
  · intro p hp
    simp only [Config.decide, List.mem_map, List.mem_filter] at hp ⊢
    obtain ⟨c, ⟨hc, hu⟩, e⟩ := hp
    exact ⟨c, ⟨hs c hc, hu⟩, e⟩

/-! ## Steps -/

theorem mem_dedupFrom (l : List Step) : ∀ (seen : List Step) (s : Step), s ∈ dedupFrom seen l ↔ s ∈ l ∧ s ∉ seen := by
  induction l with
  | nil => simp [dedupFrom]
  | cons x r ih =>
    intro seen s
    unfold dedupFrom
    by_cases hx : x ∈ seen
    · have : seen.contains x = true := List.contains_iff_mem.2 hx
      simp only [this, ite_true, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (h1 ▸ hx) h2
        · exact ⟨h1, h2⟩
    · have : seen.contains x = false := by simpa using hx
      simp only [this, Bool.false_eq_true, ite_false, List.mem_cons, ih, List.mem_cons]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hx⟩
        · exact ⟨Or.inr h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · by_cases e : s = x
          · exact Or.inl e
          · exact Or.inr ⟨h1, by simp [e]; exact h2⟩

theorem dedupFrom_sublist (l : List Step) : ∀ seen : List Step, (dedupFrom seen l).Sublist l := by
  induction l with
  | nil => intro seen; simp [dedupFrom]
  | cons x r ih =>
    intro seen
    unfold dedupFrom
    split
    · exact (ih seen).cons _
    · exact (ih _).cons_cons _

theorem dedupFrom_nodup (l : List Step) : ∀ seen : List Step, (dedupFrom seen l).Nodup := by
  induction l with
  | nil => intro seen; simp [dedupFrom]
  | cons x r ih =>
    intro seen
    unfold dedupFrom
    split
    · exact ih seen
    · refine List.nodup_cons.2 ⟨fun h => ?_, ih _⟩
      have := (mem_dedupFrom r (x :: seen) x).1 h
      simp at this

theorem steps_eq : (cfg.decide cs rc).steps = dedupFrom [] ((cfg.file.areas.filter (fun a => (cfg.decide cs rc).run.contains a.name)).flatMap Area.steps) := rfl

/-- No narrower selection: a step is listed exactly when some area that runs declares it; no step is selected by anything but its area. -/
theorem mem_steps (s : Step) : s ∈ (cfg.decide cs rc).steps ↔ ∃ a ∈ cfg.file.areas, a.name ∈ (cfg.decide cs rc).run ∧ s ∈ a.steps := by
  rw [steps_eq, mem_dedupFrom]
  simp [List.mem_flatMap, List.mem_filter, and_assoc]

/-- The steps are a sub-list of the file's steps of the areas that run, in file order, and no `(cwd, run)` repeats. -/
theorem steps_sublist_nodup :
    (cfg.decide cs rc).steps.Sublist ((cfg.file.areas.filter (fun a => (cfg.decide cs rc).run.contains a.name)).flatMap Area.steps) ∧
    (cfg.decide cs rc).steps.Nodup :=
  ⟨dedupFrom_sublist _ _, dedupFrom_nodup _ _⟩

/-- A landing whose areas in `run` have no steps has no steps, and says so. -/
theorem stepless (h : ∀ a ∈ cfg.file.areas, a.name ∈ (cfg.decide cs rc).run → a.steps = []) : (cfg.decide cs rc).inert = true := by
  have : (cfg.decide cs rc).steps = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro s hs
    obtain ⟨a, ha, hr, hsa⟩ := (mem_steps cfg cs rc s).1 hs
    simp [h a ha hr] at hsa
  simp [Config.decide] at this ⊢
  simpa using this

/-- `inert` is exactly "the steps are empty". -/
theorem inert_iff : (cfg.decide cs rc).inert = true ↔ (cfg.decide cs rc).steps = [] := by
  simp [Config.decide]

/-! ## Run and skipped partition the areas -/

/-- Every name is in `run` or in `skipped`, never both, and nothing else is in either. -/
theorem partition (n : String) :
    ((n ∈ (cfg.decide cs rc).run ∨ n ∈ (cfg.decide cs rc).skipped) ↔ n ∈ cfg.names) ∧
    ¬ (n ∈ (cfg.decide cs rc).run ∧ n ∈ (cfg.decide cs rc).skipped) := by
  have hr : ∀ n ∈ (cfg.decide cs rc).run, n ∈ cfg.names := by
    intro n hn
    cases hf : (cfg.decide cs rc).full
    · rw [run_not_full cfg cs rc hf] at hn; exact touched_sub_names cfg cs rc n hn
    · rw [run_full cfg cs rc hf] at hn; exact hn
  have hs : ∀ m, m ∈ (cfg.decide cs rc).skipped ↔ m ∈ cfg.names ∧ m ∉ (cfg.decide cs rc).run := by
    intro m; simp [Config.decide, List.mem_filter]
  constructor
  · constructor
    · rintro (h | h)
      · exact hr n h
      · exact ((hs n).1 h).1
    · intro h
      by_cases hn : n ∈ (cfg.decide cs rc).run
      · exact Or.inl hn
      · exact Or.inr ((hs n).2 ⟨h, hn⟩)
  · rintro ⟨h1, h2⟩; exact ((hs n).1 h2).2 h1

/-! ## The closest enclosing area -/

theorem max_getD_le (l : List Nat) (x : Nat) (h : x ∈ l) : x ≤ l.max?.getD 0 := by
  cases hm : l.max? with
  | none => simp [List.max?_eq_none_iff] at hm; simp [hm] at h
  | some v => exact (List.max?_eq_some_iff.1 hm).2 x h

theorem max_getD_mem (l : List Nat) (h : l ≠ []) : l.max?.getD 0 ∈ l := by
  cases hm : l.max? with
  | none => simp [List.max?_eq_none_iff] at hm; exact absurd hm h
  | some v => exact (List.max?_eq_some_iff.1 hm).1

/-- The closest areas are exactly the enclosing ones that no other enclosing area beats by a longer directory: every tie is kept, a shorter one never wins. -/
theorem mem_closest (f : AreasFile) (p : String) (a : Area) :
    a ∈ closest f p ↔ a ∈ f.areas ∧ a.encloses p = true ∧ ∀ b ∈ f.areas, b.encloses p = true → b.depth p ≤ a.depth p := by
  unfold closest
  simp only [List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨ha, he⟩, hm⟩
    refine ⟨ha, he, fun b hb hbe => ?_⟩
    rw [hm]
    exact max_getD_le _ _ (List.mem_map.2 ⟨b, List.mem_filter.2 ⟨hb, hbe⟩, rfl⟩)
  · rintro ⟨ha, he, hb⟩
    have hne : (List.map (fun a => a.depth p) (List.filter (fun a => a.encloses p) f.areas)) ≠ [] := by
      intro h
      have : a.depth p ∈ (List.map (fun a => a.depth p) (List.filter (fun a => a.encloses p) f.areas)) :=
        List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, he⟩, rfl⟩
      rw [h] at this; simp at this
    obtain ⟨b, hbm, hbe⟩ := List.mem_map.1 (max_getD_mem _ hne)
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hbm
    have h1 := hb b hb1 hb2
    have h2 := max_getD_le (List.map (fun a => a.depth p) (List.filter (fun a => a.encloses p) f.areas)) _
      (List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, he⟩, rfl⟩)
    exact ⟨⟨ha, he⟩, by omega⟩

/-- `closest` is empty exactly when no area encloses the path. -/
theorem closest_eq_nil (f : AreasFile) (p : String) : closest f p = [] ↔ ∀ a ∈ f.areas, a.encloses p = false := by
  constructor
  · intro h a ha
    cases he : a.encloses p
    · rfl
    · exfalso
      have hne : (List.map (fun a => a.depth p) (List.filter (fun a => a.encloses p) f.areas)) ≠ [] := by
        intro h'
        have : a.depth p ∈ (List.map (fun a => a.depth p) (List.filter (fun a => a.encloses p) f.areas)) :=
          List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, he⟩, rfl⟩
        rw [h'] at this; simp at this
      obtain ⟨b, hbm, hbe⟩ := List.mem_map.1 (max_getD_mem _ hne)
      obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hbm
      have : b ∈ closest f p := (mem_closest f p b).2 ⟨hb1, hb2, fun c hc hce => by
        rw [hbe]; exact max_getD_le _ _ (List.mem_map.2 ⟨c, List.mem_filter.2 ⟨hc, hce⟩, rfl⟩)⟩
      rw [h] at this; simp at this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.2
    intro a ha
    have := ((mem_closest f p a).1 ha)
    simp [h a this.1] at this

/-- The unowned, ungated, enclosed case: the areas the decision touches for the one path are exactly the closest enclosing ones, ties included
(a shorter enclosing directory never wins, every tie runs). -/
theorem closest_touched (c : Change) (hs : c.split = [c]) (ho : cfg.owners c = []) (hg : cfg.gate c.path = false) (n : String) :
    n ∈ (cfg.decide [c] false).touched ↔ ∃ a ∈ closest cfg.file c.path, a.name = n := by
  rw [mem_touched]
  have hfm : [c].flatMap Change.split = [c] := by simp [hs]
  have hh : cfg.hit c = (closest cfg.file c.path).map Area.name := by simp [Config.hit, ho, hg]
  rw [hfm]
  simp only [List.mem_singleton, exists_eq_left, hh, List.mem_map]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, a, ha, rfl⟩
    have := ((mem_closest _ _ a).1 ha).1
    simp only [Config.names, List.mem_append, List.mem_map]; exact Or.inl ⟨a, this, rfl⟩

/-- Unmapped is exact: no owner, not gate-defining, no enclosing area. -/
theorem unmappedAt_iff (c : Change) : cfg.unmappedAt c = true ↔
    cfg.owners c = [] ∧ cfg.gate c.path = false ∧ ∀ a ∈ cfg.file.areas, a.encloses c.path = false := by
  simp [Config.unmappedAt, closest_eq_nil, and_assoc]

/-! ## Split and inert -/

theorem split_norename (c c' : Change) (h : c' ∈ c.split) : c'.renamedFrom = none := by
  unfold Change.split at h; split at h <;> simp_all <;> rcases h with rfl | rfl <;> rfl

theorem split_length (c : Change) : c.split.length = if c.renamedFrom.isSome then 2 else 1 := by
  unfold Change.split; split <;> simp_all

/-- The paths of a change, old end included, all appear in its split. -/
theorem split_paths (c : Change) : c.path ∈ c.split.map Change.path ∧ ∀ old, c.renamedFrom = some old → old ∈ c.split.map Change.path := by
  unfold Change.split; split <;> simp_all

/-- Splitting a list: no rename remains, and the length grows by the number of renames. -/
theorem flatMap_split_len : ∀ cs : List Change, (cs.flatMap Change.split).length = cs.length + (cs.filter (fun c => c.renamedFrom.isSome)).length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c r ih =>
    simp only [List.flatMap_cons, List.length_append, split_length, ih, List.filter_cons, List.length_cons]
    split <;> simp_all <;> omega

/-- No area of a configuration is named `inert`: the file is validated, or it is the implicit `all`. -/
theorem name_ne_inert : ∀ a ∈ cfg.file.areas, a.name ≠ "inert" := by
  unfold Config.file
  cases h : cfg.areas with
  | none => intro a ha; simp only [implicitFile, List.mem_singleton] at ha; subst ha; simp
  | some f => intro a ha; exact (valid_names_ok f.file f.ok a ha).2

/-- `inert` owns a change exactly when `inertOwns` says so. -/
theorem inert_owner_iff (c : Change) : "inert" ∈ cfg.owners c ↔ cfg.inertOwns c = true := by
  have := name_ne_inert cfg
  simp only [Config.owners, List.mem_append, List.mem_map, List.mem_filter]
  constructor
  · rintro (⟨a, _, e⟩ | h)
    · exact absurd e (this a (by simp_all))
    · by_cases hi : cfg.inertOwns c = true
      · exact hi
      · simp [hi] at h
  · intro h; right; simp [h]

/-- `inert` never owns a deleted path: it falls to enclosure or to unmapped. -/
theorem inert_not_owner_deleted (c : Change) (h : c.status = .deleted) : "inert" ∉ cfg.owners c := by
  rw [inert_owner_iff]; simp [Config.inertOwns, h]

/-! ## Worked cases of the contract -/

private def core : Area := ⟨"core", ["core/*.py"], ["core/gen/*"], [⟨"make gates", none⟩, ⟨"make test", some "core"⟩]⟩
private def shell : Area := ⟨"shell", ["core/*.sh"], [], [⟨"make test", some "core"⟩, ⟨"make sh", none⟩]⟩
private def lib : Area := ⟨"lib", ["lib/*", "README.md"], [], [⟨"make lib", none⟩]⟩
private def docs : Area := ⟨"docs", ["docs/*.md"], [], []⟩
private def top : Area := ⟨"top", ["README.md"], [], [⟨"make top", none⟩]⟩
private def io : Area := ⟨"io", ["core/io/*.json"], [], [⟨"make io", none⟩]⟩
private def file1 : AreasFile := ⟨1, [core, shell, lib, docs, top, io]⟩
private def cfg1 (inert : List String := []) (prot : List String := []) : Config :=
  ⟨some ⟨file1, by decide +kernel⟩, [], inert, prot⟩
private def ch (s : Status) (p : String) : Change := ⟨s, p, none⟩
private def mv (p old : String) : Change := ⟨.added, p, some old⟩
private def all6 : List String := ["core", "shell", "lib", "docs", "top", "io"]

-- A path in two areas touches both (overlap is the dependency); only those run, the rest are skipped.
example : (cfg1.decide [ch .modified "README.md"] false).touched = ["lib", "top"] ∧ (cfg1.decide [ch .modified "README.md"] false).run = ["lib", "top"] ∧
    (cfg1.decide [ch .modified "README.md"] false).skipped = ["core", "shell", "docs", "io"] ∧ (cfg1.decide [ch .modified "README.md"] false).full = false := by decide +kernel
-- The shared step runs once, at its first place in the file's order.
example : (cfg1.decide [ch .modified "core/a.py", ch .modified "core/b.sh"] false).steps =
    [⟨"make gates", none⟩, ⟨"make test", some "core"⟩, ⟨"make sh", none⟩] := by decide +kernel

-- An exclude is honoured: `core/gen/x.py` is excluded from `core` (neither owned nor enclosed by it), so only `shell` encloses it.
example : (cfg1.decide [ch .modified "core/gen/x.py"] false).touched = ["shell"] ∧ (cfg1.decide [ch .modified "core/gen/x.py"] false).full = false := by decide +kernel
example : core.owns "core/a.py" = true ∧ core.owns "core/gen/x.py" = false := by decide

-- A root glob encloses nothing: `notes.txt` is unmapped and runs the full suite, named.
example : (cfg1.decide [ch .added "notes.txt"] false).unmapped = ["notes.txt"] ∧ (cfg1.decide [ch .added "notes.txt"] false).full = true ∧
    (cfg1.decide [ch .added "notes.txt"] false).run = all6 ∧ (cfg1.decide [ch .added "notes.txt"] false).skipped = [] := by decide +kernel
example : (cfg1.decide [ch .added "top.txt"] false).unmapped = ["top.txt"] := by decide +kernel

-- Closest enclosure (unowned paths): the longest directory wins alone; areas that tie all run.
example : (cfg1.decide [ch .added "core/io/z.txt"] false).touched = ["io"] ∧ (cfg1.decide [ch .added "core/io/z.txt"] false).full = false := by decide +kernel
example : (cfg1.decide [ch .added "core/z.txt"] false).touched = ["core", "shell"] ∧ (cfg1.decide [ch .added "core/z.txt"] false).full = false := by decide +kernel

-- An empty-steps area is stepless, and not unmapped.
example : (cfg1.decide [ch .modified "docs/a.md"] false).touched = ["docs"] ∧ (cfg1.decide [ch .modified "docs/a.md"] false).inert = true ∧
    (cfg1.decide [ch .modified "docs/a.md"] false).unmapped = [] := by decide +kernel

-- A gate-defining path under `.land/` or protected runs everything, is listed, and is never unmapped; an owned protected path does not narrow the run.
example : (cfg1.decide [ch .added ".land/x"] false).full = true ∧ (cfg1.decide [ch .added ".land/x"] false).gateDefining = [".land/x"] ∧
    (cfg1.decide [ch .added ".land/x"] false).unmapped = [] := by decide +kernel
example : ((cfg1 [] ["Makefile"]).decide [ch .added "Makefile"] false).full = true ∧ ((cfg1 [] ["Makefile"]).decide [ch .added "Makefile"] false).unmapped = [] := by decide +kernel
example : ((cfg1 [] ["docs/*"]).decide [ch .added "docs/a.md"] false).touched = ["docs"] ∧ ((cfg1 [] ["docs/*"]).decide [ch .added "docs/a.md"] false).full = true := by decide +kernel

-- The release candidate runs every area, even with no change; with nothing changed and no candidate nothing runs, and says so.
example : (cfg1.decide [] true).run = all6 ∧ (cfg1.decide [] true).skipped = [] := by decide +kernel
example : (cfg1.decide [] false).run = [] ∧ (cfg1.decide [] false).inert = true := by decide +kernel

-- A rename across two areas touches both, and is the deletion plus the addition.
example : (cfg1.decide [mv "docs/a.md" "lib/x"] false).touched = ["lib", "docs"] := by decide +kernel
example : cfg1.decide [mv "docs/a.md" "lib/x"] false = cfg1.decide [ch .deleted "lib/x", ch .added "docs/a.md"] false := by decide +kernel
example : (mv "docs/a.md" "lib/x").split = [ch .deleted "lib/x", ch .added "docs/a.md"] := rfl

-- Inert: it owns a non-deleted path of its globs, and does not own a deleted one (which falls to the areas, here `docs`).
example : ((cfg1 ["docs/*.txt"]).decide [ch .modified "docs/x.txt"] false).touched = ["inert"] := by decide +kernel
example : ((cfg1 ["docs/*.txt"]).decide [ch .deleted "docs/x.txt"] false).touched = ["docs"] ∧ ((cfg1 ["docs/*.txt"]).decide [ch .deleted "docs/x.txt"] false).unmapped = [] := by decide +kernel
example : "inert" ∈ (cfg1 ["docs/*.txt"]).owners (ch .modified "docs/x.txt") ∧ "inert" ∉ (cfg1 ["docs/*.txt"]).owners (ch .deleted "docs/x.txt") := by decide +kernel

-- With no areas file: one area `all`, owning everything; the inert globs carve a non-deleted path out of it.
private def cfg0 : Config := ⟨none, [⟨"gates", none⟩, ⟨"tests", none⟩], ["*.md"], []⟩
example : (cfg0.decide [ch .modified "src/a.c"] false).touched = ["all"] ∧ (cfg0.decide [ch .modified "src/a.c"] false).steps = [⟨"gates", none⟩, ⟨"tests", none⟩] := by decide +kernel
example : (cfg0.decide [ch .modified "a.md"] false).touched = ["inert"] ∧ (cfg0.decide [ch .modified "a.md"] false).inert = true := by decide +kernel
example : (cfg0.decide [ch .deleted "a.md"] false).touched = ["all"] := by decide +kernel
example : (implicitFile [⟨"gates", none⟩]).areas.map Area.name = ["all"] := by decide +kernel

-- Non-vacuity of the conditional theorems: each hypothesis holds in a concrete decision.
example : (cfg1.decide [ch .modified "docs/a.md"] false).full = false := by decide +kernel
example : (cfg1.decide [ch .added "notes.txt"] false).unmapped ≠ [] := by decide +kernel
example : cfg1.gate ".land/x" = true := by decide +kernel
example : (cfg1.decide [ch .modified "docs/a.md"] false).steps = [] := by decide +kernel
example : ∀ a ∈ cfg1.file.areas, a.name ∈ (cfg1.decide [ch .modified "docs/a.md"] false).run → a.steps = [] := by decide +kernel
example : ∀ a ∈ cfg1.file.areas, a.name ∈ (cfg1.decide [ch .modified "docs/a.md"] false).run → a.steps = [] := by decide +kernel
example : "lib" ∈ (cfg1.decide [ch .modified "README.md"] false).touched ∧ lib.owns "README.md" = true := by decide +kernel
example : (cfg1.decide [ch .added "core/io/z.txt"] false).full = false ∧ cfg1.owners (ch .added "core/io/z.txt") = [] ∧ cfg1.gate "core/io/z.txt" = false := by decide +kernel
example : (mv "docs/a.md" "lib/x").renamedFrom = some "lib/x" := rfl

end VbmAreas
