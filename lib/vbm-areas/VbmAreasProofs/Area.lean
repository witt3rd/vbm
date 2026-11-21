import VbmAreas.Area
import VbmAreasProofs.Glob
/-! # The areas value: proofs (S3) -/
namespace VbmAreas

/-! ## `owns` -/

/-- `owns` is exactly the rule, both ways: some `paths` glob matches and no `exclude` glob does. -/
theorem owns_iff (a : Area) (p : String) :
    a.owns p = true ↔ (∃ g ∈ a.paths, Glob.matches g p = true) ∧ ∀ g ∈ a.exclude, Glob.matches g p = false := by
  simp only [Area.owns, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true', List.any_eq_false]
  simp

/-- An excluded path is not owned, however many `paths` globs match it: rules out an exclude that loses to a path glob. -/
theorem excluded_not_owned (a : Area) (p g : String) (hg : g ∈ a.exclude) (hm : Glob.matches g p = true) :
    a.owns p = false := by
  cases h : a.owns p
  · rfl
  · have := ((owns_iff a p).1 h).2 g hg; simp_all

/-- Non-vacuity: the area `src/*` excluding `src/gen/*` owns `src/a.c` and not `src/gen/b.c`, which a path glob also matches. -/
example : (Area.mk "x" ["src/*"] ["src/gen/*"] []).owns "src/a.c" = true := by decide
example : Glob.matches "src/*" "src/gen/b.c" = true ∧ (Area.mk "x" ["src/*"] ["src/gen/*"] []).owns "src/gen/b.c" = false := by decide

/-! ## `owners` -/

theorem mem_owners (f : AreasFile) (p : String) (a : Area) : a ∈ Areas.owners f p ↔ a ∈ f.areas ∧ a.owns p = true := by
  simp [Areas.owners]

/-- `owners` keeps file order: it is a sub-list of the file's areas. Rules out a reordering. -/
theorem owners_sublist (f : AreasFile) (p : String) : (Areas.owners f p).Sublist f.areas := List.filter_sublist

/-! ## Validation -/

theorem step_refusal_none_iff (a : String) (s : Step) :
    Step.refusal a s = none ↔ s.run ≠ "" ∧ ∀ c, s.cwd = some c → Glob.validCwd c = true := by
  unfold Step.refusal
  cases hc : s.cwd with
  | none => simp [String.isEmpty_iff]
  | some c =>
    simp only [String.isEmpty_iff, Glob.validCwd, decide_eq_true_eq]
    split <;> simp_all [Option.map_eq_none_iff]

theorem globRefusal_none_iff (a : Area) :
    a.globRefusal = none ↔ ∀ g ∈ a.paths ++ a.exclude, Glob.valid g = true := by
  unfold Area.globRefusal
  rw [List.findSome?_eq_none_iff]
  simp [Glob.valid, Option.map_eq_none_iff]

theorem stepsRefusal_none_iff (a : Area) :
    a.steps.findSome? (Step.refusal a.name) = none ↔
      ∀ s ∈ a.steps, s.run ≠ "" ∧ ∀ c, s.cwd = some c → Glob.validCwd c = true := by
  rw [List.findSome?_eq_none_iff]
  exact forall_congr' fun s => imp_congr_right fun _ => step_refusal_none_iff _ _

/-- An area is accepted exactly when: a name of the right shape and not `inert`, some `paths`, every glob valid, every step with a run and a valid `cwd`. -/
theorem area_refusal_none_iff (a : Area) :
    a.refusal = none ↔ validName a.name = true ∧ a.name ≠ "inert" ∧ a.paths ≠ [] ∧
      (∀ g ∈ a.paths ++ a.exclude, Glob.valid g = true) ∧
      ∀ s ∈ a.steps, s.run ≠ "" ∧ ∀ c, s.cwd = some c → Glob.validCwd c = true := by
  unfold Area.refusal
  rw [← globRefusal_none_iff, ← stepsRefusal_none_iff]
  generalize a.globRefusal = x
  generalize a.steps.findSome? (Step.refusal a.name) = y
  by_cases h1 : validName a.name = true
  · by_cases h2 : a.name = "inert"
    · simp [h2, show validName "inert" = true by decide]
    · by_cases h3 : a.paths = [] <;> simp [h1, h2, h3, Option.or_eq_none_iff]
  · simp [h1]

theorem refusalFrom_none_iff (l : List Area) : ∀ seen : List String,
    Areas.refusalFrom seen l = none ↔
      (∀ a ∈ l, a.refusal = none) ∧ (l.map Area.name).Nodup ∧ ∀ a ∈ l, a.name ∉ seen := by
  induction l with
  | nil => intro seen; simp [Areas.refusalFrom]
  | cons a rest ih =>
    intro seen
    unfold Areas.refusalFrom
    cases hr : a.refusal with
    | some r => simp [hr]
    | none =>
      by_cases hs : a.name ∈ seen
      · simp [hs, hr]
      · simp only [List.contains_eq_any_beq]
        simp [ih, hr, hs]
        intro _
        constructor <;> intro h <;> simp_all

/-- `validate` accepts exactly: version 1, some areas, every area accepted, and unique names. -/
theorem validate_none_iff (f : AreasFile) :
    Areas.validate f = none ↔ f.version = 1 ∧ f.areas ≠ [] ∧ (∀ a ∈ f.areas, a.refusal = none) ∧ (f.areas.map Area.name).Nodup := by
  unfold Areas.validate
  by_cases h1 : f.version = 1
  · by_cases h2 : f.areas = []
    · simp [h1, h2]
    · simp [h1, h2, refusalFrom_none_iff]
  · simp [h1]

/-- A valid file has unique names: rules out two areas sharing a name. -/
theorem valid_names_nodup (f : AreasFile) (h : Areas.validate f = none) : (f.areas.map Area.name).Nodup :=
  ((validate_none_iff f).1 h).2.2.2

/-- A valid file never names an area `inert`, and every name has the right shape. -/
theorem valid_names_ok (f : AreasFile) (h : Areas.validate f = none) : ∀ a ∈ f.areas, validName a.name = true ∧ a.name ≠ "inert" := by
  intro a ha
  have := (area_refusal_none_iff a).1 (((validate_none_iff f).1 h).2.2.1 a ha)
  exact ⟨this.1, this.2.1⟩

/-- For a valid file, `owners` has no duplicates (the areas are distinct, `owners` is a sub-list). -/
theorem owners_nodup (f : AreasFile) (h : Areas.validate f = none) (p : String) : (Areas.owners f p).Nodup := by
  have hn : f.areas.Nodup := by
    have := valid_names_nodup f h
    rw [List.nodup_iff_pairwise_ne] at this ⊢
    rw [List.pairwise_map] at this
    exact this.imp fun {x y} h e => h (by rw [e])
  exact hn.sublist (owners_sublist f p)

/-- The validated value from `check` is exactly the file when accepted, and the first refusal otherwise. -/
theorem check_ok (f : AreasFile) (r : Areas) (h : Areas.check f = .ok r) : r.file = f ∧ Areas.validate f = none := by
  unfold Areas.check at h
  split at h <;> simp_all
  exact h ▸ rfl

/-! ## Each refusal has a witness, and a good file is accepted -/

/-- A good file: the contract's example. -/
def goodFile : AreasFile :=
  ⟨1, [⟨"core", ["core/*.py"], ["core/gen/*"], [⟨"make test", some "core"⟩]⟩, ⟨"docs", ["docs/*"], [], []⟩]⟩

-- Non-vacuity: the good file is accepted, and a stepless area is valid.
example : Areas.validate goodFile = none := by decide +kernel

private def one (a : Area) (v : Nat := 1) : AreasFile := ⟨v, [a]⟩
private def ok : Area := ⟨"a", ["x/*"], [], [⟨"go", none⟩]⟩

example : Areas.validate (one ok) = none := by decide +kernel
example : Areas.validate (one ok 2) = some (.badVersion 2) := by decide +kernel
example : Areas.validate ⟨1, []⟩ = some .noAreas := by decide +kernel
example : Areas.validate (one { ok with name := "A" }) = some (.badName "A") := by decide +kernel
example : Areas.validate (one { ok with name := "" }) = some (.badName "") := by decide +kernel
example : Areas.validate (one { ok with name := "-a" }) = some (.badName "-a") := by decide +kernel
example : Areas.validate (one { ok with name := "a_b-9" }) = none := by decide +kernel
example : Areas.validate (one { ok with name := "inert" }) = some (.reservedName "inert") := by decide +kernel
example : Areas.validate ⟨1, [ok, ok]⟩ = some (.duplicateName "a") := by decide +kernel
example : Areas.validate (one { ok with paths := [] }) = some (.emptyPaths "a") := by decide +kernel
example : Areas.validate (one { ok with exclude := ["a[b"] }) = some (.badGlob "a" "a[b" .forbiddenChar) := by decide +kernel
example : Areas.validate (one { ok with steps := [⟨"go", some "d/*"⟩] }) = some (.badCwd "a" "d/*" .wildcard) := by decide +kernel
example : Areas.validate (one { ok with steps := [⟨"", none⟩] }) = some (.emptyRun "a") := by decide +kernel
example : Areas.validate (one { ok with steps := [] }) = none := by decide +kernel

/-- Every glob refusal reason is raised by a file (a bad `cwd` for `wildcard`, a bad glob for the rest) and names the area: nothing the glob rules refuse slips into a valid file. -/
theorem reason_witness_file (r : Glob.Reason) :
    (r ≠ .wildcard → Areas.validate (one { ok with paths := [r.witness] }) = some (.badGlob "a" r.witness r)) ∧
    (r = .wildcard → Areas.validate (one { ok with steps := [⟨"go", some r.witness⟩] }) = some (.badCwd "a" r.witness r)) := by
  cases r <;> simp <;> decide +kernel

/-! ## Enclosure -/

/-- `encloses`, unfolded: no `exclude` glob matches, and some glob starts in a non-root directory the path lies under by whole segments. -/
theorem encloses_iff (a : Area) (p : String) :
    a.encloses p = true ↔ (∀ g ∈ a.exclude, Glob.matches g p = false) ∧
      ∃ g ∈ a.paths, Glob.startDir g ≠ "" ∧ Glob.under (Glob.startDir g) p = true := by
  unfold Area.encloses Area.excluded Area.enclosingDirs Area.dirs
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.isEmpty_iff,
    List.filter_eq_nil_iff, List.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg => by simpa [List.any_eq_true] using fun h => h1 (List.any_eq_true.2 ⟨g, hg, h⟩), ?_⟩
    apply Classical.byContradiction
    intro hc
    exact h2 (fun d ⟨g, hg, hd⟩ => by
      subst hd
      intro hh
      exact hc ⟨g, hg, by simpa using hh⟩)
  · rintro ⟨h1, g, hg, hne, hu⟩
    refine ⟨fun hany => ?_, fun h => ?_⟩
    · obtain ⟨g', hg', hm⟩ := List.any_eq_true.1 hany
      simp [h1 g' hg'] at hm
    
    have := h _ ⟨g, hg, rfl⟩
    simp [hne, hu] at this

/-- An enclosed path is not excluded: no `exclude` glob matches it. Rules out an enclosure that overrides an exclude. -/
theorem encloses_not_excluded (a : Area) (p : String) (h : a.encloses p = true) : ∀ g ∈ a.exclude, Glob.matches g p = false :=
  ((encloses_iff a p).1 h).1

/-- A path under the directory one of the area's globs starts in (a non-root one, whole segments) and not excluded is enclosed. -/
theorem encloses_of_under (a : Area) (p g : String) (hg : g ∈ a.paths) (hne : Glob.startDir g ≠ "")
    (hu : Glob.under (Glob.startDir g) p = true) (hx : ∀ e ∈ a.exclude, Glob.matches e p = false) : a.encloses p = true :=
  (encloses_iff a p).2 ⟨hx, g, hg, hne, hu⟩

/-- The enclosure length is defined exactly when the area encloses the path. -/
theorem enclosureLength_isSome_iff (a : Area) (p : String) : (a.enclosureLength p).isSome = a.encloses p := by
  unfold Area.enclosureLength Area.encloses
  by_cases hx : a.excluded p = true
  · simp [hx]
  · simp only [hx]
    cases hl : (a.enclosingDirs p) with
    | nil => simp
    | cons d ds => simp [List.max?_cons]

-- Non-vacuity and the whole-segment rule: `core/io/*` encloses `core/io/x.json` and not `core/iodata.json` (a string prefix),
-- and not an excluded path; a glob that starts in the root encloses nothing.
private def io : Area := ⟨"io", ["core/io/*"], ["core/io/gen/*"], []⟩
example : io.encloses "core/io/x.json" = true := by decide
example : io.encloses "core/iodata.json" = false := by decide
example : io.encloses "core/io" = false := by decide
example : io.encloses "core/io/gen/y.json" = false := by decide
example : Glob.matches "core/io/*" "core/io/gen/y.json" = true := by decide
example : (Area.mk "r" ["*.md", "README.md"] [] []).encloses "docs/a.md" = false := by decide
example : io.enclosureLength "core/io/x.json" = some 2 := by decide
example : (Area.mk "c" ["core/*.py", "core/io/*"] [] []).enclosureLength "core/io/x.py" = some 2 := by decide
example : io.enclosureLength "core/iodata.json" = none := by decide

end VbmAreas
