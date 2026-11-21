import VbmAreas.Report
import VbmAreas.Reuse
import VbmAreasProofs.Decide
/-! # The report: proofs (S5) -/
namespace VbmAreas

/-! ## The order on paths -/

theorem lexLt_irrefl : ∀ a : Chars, lexLt a a = false := by
  intro a; induction a with
  | nil => rfl
  | cons c cs ih => simp [lexLt, ih]

theorem lexLt_trans : ∀ a b c : Chars, lexLt a b = true → lexLt b c = true → lexLt a c = true := by
  intro a; induction a with
  | nil => intro b c h1 h2; cases c with
    | nil => cases b <;> simp [lexLt] at h2
    | cons => rfl
  | cons x xs ih =>
    intro b c h1 h2
    cases b with
    | nil => simp [lexLt] at h1
    | cons y ys =>
      cases c with
      | nil => simp [lexLt] at h2
      | cons z zs =>
        simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
        rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
        · exact Or.inl (Nat.lt_trans h1 h2)
        · exact Or.inl h1
        · exact Or.inl h2
        · exact Or.inr ⟨rfl, ih ys zs h1 h2⟩

theorem lexLt_total : ∀ a b : Chars, a ≠ b → lexLt a b = true ∨ lexLt b a = true := by
  intro a; induction a with
  | nil => intro b h; cases b with
    | nil => exact absurd rfl h
    | cons => exact Or.inl rfl
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => exact Or.inr rfl
    | cons y ys =>
      by_cases hxy : x = y
      · subst hxy
        have : xs ≠ ys := fun e => h (by rw [e])
        rcases ih ys this with h1 | h1
        · exact Or.inl (by simp [lexLt, h1])
        · exact Or.inr (by simp [lexLt, h1])
      · have : x.toNat ≠ y.toNat := fun e => hxy (Char.toNat_inj.1 e)
        rcases Nat.lt_or_gt_of_ne this with h1 | h1
        · exact Or.inl (by simp [lexLt, h1])
        · exact Or.inr (by simp [lexLt, h1])

theorem strLt_irrefl (a : String) : strLt a a = false := lexLt_irrefl _
theorem strLt_trans {a b c : String} (h1 : strLt a b = true) (h2 : strLt b c = true) : strLt a c = true := lexLt_trans _ _ _ h1 h2
theorem strLt_total {a b : String} (h : a ≠ b) : strLt a b = true ∨ strLt b a = true :=
  lexLt_total _ _ (fun e => h (String.toList_inj.1 e))

/-- Strictly ascending. -/
def Asc (l : List String) : Prop := l.Pairwise (fun a b => strLt a b = true)

theorem mem_insertU (p : String) : ∀ l x, x ∈ insertU p l ↔ x = p ∨ x ∈ l := by
  intro l; induction l with
  | nil => simp [insertU]
  | cons q qs ih =>
    intro x
    unfold insertU
    split
    · simp
    · split
      · rename_i h1 h2; subst h2; simp
      · simp [ih]; grind

theorem asc_insertU (p : String) : ∀ l, Asc l → Asc (insertU p l) := by
  intro l; induction l with
  | nil => intro _; simp [insertU, Asc]
  | cons q qs ih =>
    intro h0
    have h := List.pairwise_cons.1 h0
    unfold insertU
    split
    · rename_i hl
      simp only [Asc, List.pairwise_cons, List.mem_cons]
      refine ⟨?_, h⟩
      rintro x (rfl | hx)
      · exact hl
      · exact strLt_trans hl (h.1 x hx)
    · split
      · rename_i h1 h2; subst h2; exact h0
      · rename_i h1 h2
        have hq : strLt q p = true := by
          rcases strLt_total (Ne.symm h2) with h3 | h3
          · exact h3
          · simp_all
        simp only [Asc, List.pairwise_cons]
        refine ⟨?_, ih h.2⟩
        intro x hx
        rcases (mem_insertU p qs x).1 hx with rfl | hx
        · exact hq
        · exact h.1 x hx

theorem sortU_asc (l : List String) : Asc (sortU l) := by
  induction l with
  | nil => simp [sortU, Asc]
  | cons a as ih => simp only [sortU, List.foldr_cons] at ih ⊢; exact asc_insertU a _ ih

theorem mem_sortU (l : List String) (x : String) : x ∈ sortU l ↔ x ∈ l := by
  induction l with
  | nil => simp [sortU]
  | cons a as ih => simp only [sortU, List.foldr_cons] at ih ⊢; rw [mem_insertU, ih]; simp

theorem asc_nodup (l : List String) (h : Asc l) : l.Nodup := by
  unfold Asc at h
  refine List.Pairwise.imp ?_ h
  intro a b hab e; subst e; rw [strLt_irrefl] at hab; cases hab

theorem sortU_nodup (l : List String) : (sortU l).Nodup := asc_nodup _ (sortU_asc l)

/-! ## Owners -/

variable (cfg : Config) (tracked : List String)

theorem owners_names (p n : String) (h : n ∈ Report.owners cfg p) : n ∈ cfg.names := by
  simp only [Report.owners, Config.owners, List.mem_append, List.mem_map, List.mem_filter, Config.names] at h ⊢
  rcases h with ⟨a, ⟨ha, _⟩, rfl⟩ | h
  · exact Or.inl ⟨a, ha, rfl⟩
  · right
    have : cfg.inert.isEmpty = false := by
      by_cases e : cfg.inert.isEmpty = true
      · simp [Config.inertOwns, List.isEmpty_iff.1 e] at h
      · simpa using e
    simp [this] at h ⊢; exact h.2

/-! ## Overlap -/

theorem pathsOf_comm (a b : String) : Report.pathsOf cfg tracked a b = Report.pathsOf cfg tracked b a := by
  simp only [Report.pathsOf, Bool.and_comm]

theorem mem_pathsOf (a b p : String) : p ∈ Report.pathsOf cfg tracked a b ↔ p ∈ tracked ∧ a ∈ Report.owners cfg p ∧ b ∈ Report.owners cfg p := by
  simp [Report.pathsOf]

theorem mem_pairs (ns : List String) (ab : String × String) : ab ∈ Report.pairs ns ↔ ab.1 ∈ ns ∧ ab.2 ∈ ns ∧ strLt ab.1 ab.2 = true := by
  obtain ⟨a, b⟩ := ab
  simp [Report.pairs]


theorem asc_pathsOf (a b : String) : Asc (Report.pathsOf cfg (sortU tracked) a b) := by
  unfold Report.pathsOf Asc
  exact List.Pairwise.filter _ (sortU_asc tracked)

/-- An entry of the overlap report: its pair is in name order, both are areas (or `inert`), and its paths are exactly the tracked paths both own, sorted, distinct, never none. -/
theorem mem_overlap (o : Overlap) : o ∈ Report.overlap cfg tracked ↔
    o.a ∈ cfg.names ∧ o.b ∈ cfg.names ∧ strLt o.a o.b = true ∧ o.paths ≠ [] ∧ o.paths = Report.pathsOf cfg (sortU tracked) o.a o.b := by
  obtain ⟨oa, ob, op⟩ := o
  simp only [Report.overlap, List.mem_filterMap, mem_pairs, mem_sortU]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, h⟩
    by_cases he : (Report.pathsOf cfg (sortU tracked) a b).isEmpty = true
    · simp [he] at h
    · simp only [he, Bool.false_eq_true, ite_false, Option.some.injEq, Overlap.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨ha, hb, hab, fun e => he (by simp [e]), rfl⟩
  · rintro ⟨ha, hb, hab, hne, hp⟩
    refine ⟨(oa, ob), ⟨ha, hb, hab⟩, ?_⟩
    have he : (Report.pathsOf cfg (sortU tracked) oa ob).isEmpty = false := by
      rw [← hp]; cases h : op <;> simp_all
    simp only [he, Bool.false_eq_true, ite_false, Option.some.injEq, Overlap.mk.injEq]
    simp only [true_and]; exact hp.symm

theorem strLt_asymm {a b : String} (h : strLt a b = true) : strLt b a = false := by
  cases h' : strLt b a
  · rfl
  · exact absurd (strLt_trans h h') (by rw [strLt_irrefl]; simp)

/-- The overlap report is symmetric in the pair: the paths of `(a, b)` and of `(b, a)` are the same, and only the name-ordered pair is listed, once. -/
theorem overlap_symm (a b : String) (ps : List String) (h : ⟨a, b, ps⟩ ∈ Report.overlap cfg tracked) :
    ps = Report.pathsOf cfg (sortU tracked) b a ∧ (⟨b, a, ps⟩ : Overlap) ∉ Report.overlap cfg tracked := by
  rw [mem_overlap] at h
  obtain ⟨_, _, hab, _, hp⟩ := h
  refine ⟨by simp only at hp; rw [hp, pathsOf_comm], fun h' => ?_⟩
  rw [mem_overlap] at h'
  have := strLt_asymm hab
  simp only at h'
  rw [this] at h'
  exact absurd h'.2.2.1 (by simp)

/-- Each pair is listed once: two entries with the same pair are the same entry. -/
theorem overlap_unique (o o' : Overlap) (h : o ∈ Report.overlap cfg tracked) (h' : o' ∈ Report.overlap cfg tracked) (ha : o.a = o'.a) (hb : o.b = o'.b) : o = o' := by
  rw [mem_overlap] at h h'
  obtain ⟨oa, ob, ops⟩ := o
  obtain ⟨a, b, ps⟩ := o'
  simp only at ha hb h h'
  subst ha hb
  simp only [Overlap.mk.injEq, true_and]
  rw [h.2.2.2.2, h'.2.2.2.2]

/-- A tracked path that two areas both own is listed under their pair, in name order; a path in three areas is therefore under each of the three pairs. -/
theorem overlap_complete (p a b : String) (hp : p ∈ tracked) (ha : a ∈ Report.owners cfg p) (hb : b ∈ Report.owners cfg p) (hab : strLt a b = true) :
    ∃ o ∈ Report.overlap cfg tracked, o.a = a ∧ o.b = b ∧ p ∈ o.paths := by
  have hmem : p ∈ Report.pathsOf cfg (sortU tracked) a b := (mem_pathsOf cfg _ a b p).2 ⟨(mem_sortU tracked p).2 hp, ha, hb⟩
  refine ⟨⟨a, b, Report.pathsOf cfg (sortU tracked) a b⟩, (mem_overlap cfg tracked _).2 ⟨owners_names cfg p a ha, owners_names cfg p b hb, hab, ?_, rfl⟩, rfl, rfl, hmem⟩
  intro e; simp only at e; rw [e] at hmem; simp at hmem

/-- Every path listed under a pair is tracked and owned by both. -/
theorem overlap_sound (o : Overlap) (h : o ∈ Report.overlap cfg tracked) (p : String) (hp : p ∈ o.paths) :
    p ∈ tracked ∧ o.a ∈ Report.owners cfg p ∧ o.b ∈ Report.owners cfg p := by
  rw [mem_overlap] at h
  rw [h.2.2.2.2, mem_pathsOf, mem_sortU] at hp
  exact hp

theorem overlap_paths_asc (o : Overlap) (h : o ∈ Report.overlap cfg tracked) : Asc o.paths := by
  rw [((mem_overlap cfg tracked o).1 h).2.2.2.2]; exact asc_pathsOf cfg tracked _ _

/-! ## The counts -/

theorem mem_overlapNames (n : String) : n ∈ Report.overlapNames cfg tracked ↔ ∃ o ∈ Report.overlap cfg tracked, o.a = n ∨ o.b = n := by
  simp only [Report.overlapNames, mem_sortU, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨o, ho, h⟩; exact ⟨o, ho, by grind⟩
  · rintro ⟨o, ho, h⟩; exact ⟨o, ho, by grind⟩

theorem mem_overlapPaths (p : String) : p ∈ Report.overlapPaths cfg tracked ↔ ∃ o ∈ Report.overlap cfg tracked, p ∈ o.paths := by
  simp [Report.overlapPaths, mem_sortU]

/-- The counts equal the lengths of the lists they count, which have no repeat; no overlap iff the count of areas is zero. -/
theorem counts (cfg : Config) (tracked : List String) :
    (Report.summary cfg tracked).unmapped = (Report.summary cfg tracked).unowned.length ∧
    (Report.summary cfg tracked).areasInOverlap = (Report.overlapNames cfg tracked).length ∧ (Report.overlapNames cfg tracked).Nodup ∧
    (Report.summary cfg tracked).pathsInOverlap = (Report.overlapPaths cfg tracked).length ∧ (Report.overlapPaths cfg tracked).Nodup :=
  ⟨rfl, rfl, sortU_nodup _, rfl, sortU_nodup _⟩

theorem areasInOverlap_zero_iff : (Report.summary cfg tracked).areasInOverlap = 0 ↔ (Report.summary cfg tracked).overlaps = [] := by
  simp only [Report.summary, List.length_eq_zero_iff]
  constructor
  · intro h
    refine List.eq_nil_iff_forall_not_mem.2 fun o ho => ?_
    have : o.a ∈ Report.overlapNames cfg tracked := (mem_overlapNames cfg tracked _).2 ⟨o, ho, Or.inl rfl⟩
    rw [h] at this; simp at this
  · intro h
    refine List.eq_nil_iff_forall_not_mem.2 fun n hn => ?_
    obtain ⟨o, ho, _⟩ := (mem_overlapNames cfg tracked n).1 hn
    rw [h] at ho; simp at ho

/-! ## Unowned -/

/-- A path is listed in `unowned` exactly when it is tracked, no area (nor `inert`) owns it and it is not gate-defining; its list is the declared areas that enclose it. -/
theorem mem_unowned (p : String) (es : List String) : (p, es) ∈ Report.unowned cfg tracked ↔
    p ∈ tracked ∧ Report.owners cfg p = [] ∧ cfg.gate p = false ∧ es = (cfg.file.areas.filter (fun a => a.encloses p)).map Area.name := by
  simp only [Report.unowned, List.mem_filterMap, mem_sortU]
  constructor
  · rintro ⟨q, hq, h⟩
    by_cases hc : ((Report.owners cfg q).isEmpty && !cfg.gate q) = true
    · simp only [hc, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hc
      exact ⟨hq, hc.1, hc.2, rfl⟩
    · simp [hc] at h
  · rintro ⟨hq, ho, hg, rfl⟩
    refine ⟨p, hq, ?_⟩
    simp [ho, hg]

theorem unowned_paths (p : String) : p ∈ (Report.unowned cfg tracked).map Prod.fst ↔ p ∈ tracked ∧ Report.owners cfg p = [] ∧ cfg.gate p = false := by
  simp only [List.mem_map, Prod.exists]
  constructor
  · rintro ⟨q, es, h, rfl⟩; have := (mem_unowned cfg tracked q es).1 h; exact ⟨this.1, this.2.1, this.2.2.1⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨p, _, (mem_unowned cfg tracked p _).2 ⟨h1, h2, h3, rfl⟩, rfl⟩

/-- A listed path with no enclosing area is UNMAPPED: deciding that path alone runs the full suite. -/
theorem unmapped_decide_full (p : String) (h : (p, []) ∈ Report.unowned cfg tracked) :
    (cfg.decide [⟨.modified, p, none⟩] false).full = true := by
  obtain ⟨_, ho, hg, he⟩ := (mem_unowned cfg tracked p []).1 h
  rw [full_iff]
  refine Or.inr ⟨⟨.modified, p, none⟩, by simp [Change.split], Or.inr ?_⟩
  rw [unmappedAt_iff]
  refine ⟨ho, hg, fun a ha => ?_⟩
  cases hh : a.encloses p
  · rfl
  · have : a.name ∈ (cfg.file.areas.filter (fun a => a.encloses p)).map Area.name := List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, hh⟩, rfl⟩
    rw [← he] at this; simp at this

/-! ## Stepless -/

theorem mem_noSteps (n : String) : n ∈ Report.noSteps cfg ↔ (∃ a ∈ cfg.file.areas, a.name = n ∧ a.steps = []) ∨ (n = "inert" ∧ cfg.inert ≠ []) := by
  simp only [Report.noSteps, List.mem_append, List.mem_map, List.mem_filter, List.isEmpty_iff]
  constructor
  · rintro (⟨a, ⟨ha, hs⟩, rfl⟩ | h)
    · exact Or.inl ⟨a, ha, rfl, hs⟩
    · right
      by_cases e : cfg.inert.isEmpty = true
      · simp at h; exact absurd (List.isEmpty_iff.1 e) h.1
      · simp only [Bool.not_eq_true] at e; simp at h; exact ⟨h.2, h.1⟩
  · rintro (⟨a, ha, rfl, hs⟩ | ⟨rfl, hne⟩)
    · exact Or.inl ⟨a, ⟨ha, hs⟩, rfl⟩
    · right; simp [hne]


/-! ## Worked cases (non-vacuity of every statement) -/

private def a1 : Area := ⟨"a", ["src/*"], [], [⟨"go a", none⟩]⟩
private def b1 : Area := ⟨"b", ["src/*.c", "x.md"], [], []⟩
private def c1 : Area := ⟨"c", ["src/lib/*"], ["src/lib/gen/*"], [⟨"go c", none⟩]⟩
private def d1 : Area := ⟨"d", ["core/*.py"], ["core/gen/*"], [⟨"go d", none⟩]⟩
private def cfgR (inert : List String := []) (prot : List String := []) : Config :=
  ⟨some ⟨⟨1, [a1, b1, c1, d1]⟩, by decide +kernel⟩, [], inert, prot⟩

-- a path in three areas appears under each of the three pairs; sorted paths.
example : Report.overlap (cfgR) ["src/lib/z.c", "src/lib/y.c", "src/q.c", "other"] =
    [⟨"a", "b", ["src/lib/y.c", "src/lib/z.c", "src/q.c"]⟩, ⟨"a", "c", ["src/lib/y.c", "src/lib/z.c"]⟩, ⟨"b", "c", ["src/lib/y.c", "src/lib/z.c"]⟩] := by decide +kernel
-- the counts: one overlap of two paths gives (2, 2, 0)
example : (Report.summary (cfgR) ["src/q.c", "src/lib/y.c"]).areasInOverlap = 3 := by decide +kernel
example : (Report.summary (cfgR) ["src/q.c", "x.md", "src/lib/y.c"]).pathsInOverlap = 2 ∧ (Report.summary (cfgR) ["src/q.c", "x.md"]).unmapped = 0 := by decide +kernel
-- `inert` counts as an area in an overlap
example : (Report.overlap (cfgR ["docs/*"]) ["src/a"]).length = 0 := by decide +kernel
-- unowned: a root file is unmapped; a path under an area's directory is listed with it; an excluded one is not enclosed; a gate-defining path is not listed
example : Report.unowned (cfgR) ["notes.txt", "core/x.txt", "core/gen/x.py"] = [("core/gen/x.py", []), ("core/x.txt", ["d"]), ("notes.txt", [])] := by decide +kernel
example : Report.unowned (cfgR [] ["Makefile"]) ["Makefile", "notes.txt", ".land/x"] = [("notes.txt", [])] := by decide +kernel
example : Report.noSteps (cfgR ["d/*"]) = ["b", "inert"] := by decide +kernel
example : (Report.summary (cfgR) ["notes.txt"]).unmapped = 1 ∧ (Report.summary (cfgR) ["notes.txt"]).areasInOverlap = 0 := by decide +kernel

end VbmAreas
