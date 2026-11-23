import VbmAreas.Glob
/-! # The glob language: proofs (S2) -/
namespace VbmAreas
open Glob

/-! ## The matcher -/

/-- Totality: the matcher always answers (it is structural on the pattern), so the answer is `true` or `false`. Rules out a matcher with no answer. -/
theorem matches_total (pat path : String) : Glob.matches pat path = true ∨ Glob.matches pat path = false := by
  cases Glob.matches pat path <;> simp

example : Glob.matches "a*c" "abc" = true := by decide
example : Glob.matches "a*c" "abd" = false := by decide

theorem anySuffix_iff (f : Chars → Bool) (s : Chars) :
    anySuffix f s = true ↔ ∃ u t, s = u ++ t ∧ f t = true := by
  induction s with
  | nil => simp [anySuffix]; exact ⟨fun h => ⟨[], by simpa using h⟩, fun ⟨u, t, h1, h2⟩ => by simp_all⟩
  | cons c s ih =>
    simp only [anySuffix, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨u, t, h1, h2⟩)
      · exact ⟨[], _, rfl, h⟩
      · exact ⟨c :: u, t, by simp [h1], h2⟩
    · rintro ⟨u, t, h1, h2⟩
      cases u with
      | nil => left; simp at h1; subst h1; exact h2
      | cons d u => right; simp at h1; exact ⟨u, t, h1.2, h2⟩

/-- A star matches a run `u` and then the rest of the pattern matches what follows: the star is any run, the empty one and one with `/` included. -/
theorem star_iff (ps s : Chars) :
    matchChars ('*' :: ps) s = true ↔ ∃ u t, s = u ++ t ∧ matchChars ps t = true := by
  simp only [matchChars]; exact anySuffix_iff _ _

/-- `*` matches every path (the empty one, one with `/`): it rules out a star that needs a character or stops at a slash. -/
theorem star_matches_all (s : String) : Glob.matches "*" s = true := by
  simp only [Glob.matches]
  have : ("*" : String).toList = ['*'] := by decide
  rw [this, star_iff]; exact ⟨s.toList, [], by simp, by simp [matchChars]⟩

example : Glob.matches "*" "" = true := by decide
example : Glob.matches "*" "a/b" = true := by decide
example : Glob.matches "src/*" "src/a/b.c" = true := by decide

/-- `**` is the same as `*`: it rules out a double star with a stronger meaning. -/
theorem double_star (ps s : Chars) : matchChars ('*' :: '*' :: ps) s = matchChars ('*' :: ps) s := by
  apply Bool.eq_iff_iff.2
  rw [star_iff, star_iff]
  constructor
  · rintro ⟨u, t, h1, h2⟩
    rw [star_iff] at h2
    obtain ⟨v, w, h3, h4⟩ := h2
    exact ⟨u ++ v, w, by simp [h1, h3], h4⟩
  · rintro ⟨u, t, h1, h2⟩
    exact ⟨[], s, by simp, by rw [star_iff]; exact ⟨u, t, h1, h2⟩⟩

example : Glob.matches "a**c" "a/b/c" = true := by decide

/-- `?` consumes exactly one character. -/
theorem query_cons (ps : Chars) (c : Char) (s : Chars) : matchChars ('?' :: ps) (c :: s) = matchChars ps s := by
  simp [matchChars]

/-- `?` never matches the empty path: it rules out `?` as optional. -/
theorem query_nil (ps : Chars) : matchChars ('?' :: ps) [] = false := by
  simp [matchChars]

example : Glob.matches "a?c" "abc" = true := by decide
example : Glob.matches "a?c" "ac" = false := by decide
example : Glob.matches "?" "" = false := by decide
example : Glob.matches "?" "ab" = false := by decide

theorem lit_cons (c : Char) (ps : Chars) (d : Char) (s : Chars) (h1 : c ≠ '*') (h2 : c ≠ '?') :
    matchChars (c :: ps) (d :: s) = (c == d && matchChars ps s) := by
  simp [matchChars]

theorem lit_nil (c : Char) (ps : Chars) (h1 : c ≠ '*') (h2 : c ≠ '?') : matchChars (c :: ps) [] = false := by
  unfold matchChars; split <;> simp_all

/-- A pattern with no `*` and no `?` matches exactly the path equal to it: it rules out a literal that matches a prefix, a case variant or a neighbour. -/
theorem literal_iff (pat s : Chars) (h : ∀ c ∈ pat, c ≠ '*' ∧ c ≠ '?') :
    matchChars pat s = true ↔ s = pat := by
  induction pat generalizing s with
  | nil => simp [matchChars]
  | cons c ps ih =>
    have hc := h c (by simp)
    have hps : ∀ d ∈ ps, d ≠ '*' ∧ d ≠ '?' := fun d hd => h d (by simp [hd])
    cases s with
    | nil => simp [lit_nil c ps hc.1 hc.2]
    | cons d s =>
      rw [lit_cons c ps d s hc.1 hc.2]
      simp only [Bool.and_eq_true, beq_iff_eq, ih s hps, List.cons.injEq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩

example : Glob.matches "README.md" "README.md" = true := by decide
example : Glob.matches "README.md" "readme.md" = false := by decide
example : Glob.matches "a" "ab" = false := by decide

/-! ## Refusal -/

/-- Every reason has a refused witness (a working directory for `wildcard`, a pattern for the rest). -/
def Glob.Reason.witness : Glob.Reason → String
  | .empty => "" | .forbiddenChar => "a[b" | .leadingSlash => "/a" | .leadingDotSlash => "./a"
  | .trailingSlash => "a/" | .doubleSlash => "a//b" | .dotDotSegment => "a/../b" | .wildcard => "a/*"

/-- Each reason is raised by its witness: nothing the contract refuses is accepted. -/
theorem witness_refused (r : Glob.Reason) :
    (r ≠ .wildcard → Glob.refusal r.witness = some r) ∧ (r = .wildcard → Glob.cwdRefusal r.witness = some r) := by
  cases r <;> simp <;> decide

/-- `valid` is exactly "not refused". -/
theorem valid_iff (g : String) : Glob.valid g = true ↔ Glob.refusal g = none := by simp [Glob.valid]

-- Non-vacuity: good patterns and directories are accepted; a wildcard is a valid glob but not a valid cwd.
example : Glob.valid "src/*.py" = true := by decide
example : Glob.valid "README.md" = true := by decide
example : Glob.validCwd "src/lib" = true := by decide
example : Glob.valid "a/*" = true ∧ Glob.validCwd "a/*" = false := by decide
example : Glob.valid "a?b" = true ∧ Glob.validCwd "a?b" = false := by decide
example : Glob.valid "a.b/c" = true := by decide
example : Glob.valid "a]" = false ∧ Glob.valid "a\\b" = false ∧ Glob.valid "{a}" = false ∧ Glob.valid "a}" = false := by decide

-- Near misses, one per reason: a good pattern close to each refused one is accepted.
example : Glob.valid "a" = true ∧ Glob.valid "a[b" = false := by decide
example : Glob.valid "a/b" = true ∧ Glob.valid "/a" = false := by decide
example : Glob.valid ".a/b" = true ∧ Glob.valid "./a" = false := by decide
example : Glob.valid "a/b" = true ∧ Glob.valid "a/" = false := by decide
example : Glob.valid "a/b/c" = true ∧ Glob.valid "a//b" = false := by decide
example : Glob.valid "a/..b/c" = true ∧ Glob.valid "a/../b" = false ∧ Glob.valid ".." = false := by decide
example : Glob.validCwd "a/b" = true ∧ Glob.validCwd "a/*" = false := by decide

/-! ## Segments, and the directory a glob starts in -/

theorem segments_ne_nil (g : Chars) : ∃ s rest, segments g = s :: rest := by
  induction g with
  | nil => exact ⟨[], [], rfl⟩
  | cons c cs ih =>
    obtain ⟨s, rest, h⟩ := ih
    by_cases hc : c = '/' <;> simp [segments, h, hc]

theorem segments_noslash (s : Chars) (h : '/' ∉ s) : segments s = [s] := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '/' := fun e => h (by simp [e])
    simp [segments, ih (fun x => h (by simp [x])), hc]

theorem segments_cons_slash (r : Chars) : segments ('/' :: r) = [] :: segments r := by
  obtain ⟨s, rest, h⟩ := segments_ne_nil r
  simp [segments, h]

/-- Splitting at a slash: the segments of the two sides. -/
theorem segments_append (u r : Chars) : segments (u ++ '/' :: r) = segments u ++ segments r := by
  induction u with
  | nil => simp [segments_cons_slash, segments]
  | cons c cs ih =>
    obtain ⟨s, rest, h⟩ := segments_ne_nil cs
    by_cases hc : c = '/' <;> simp [segments, ih, h, hc]

theorem noslash_of_mem (g : Chars) : ∀ s ∈ segments g, '/' ∉ s := by
  induction g with
  | nil => simp [segments]
  | cons c cs ih =>
    obtain ⟨s', rest, h⟩ := segments_ne_nil cs
    rw [h] at ih
    by_cases hc : c = '/'
    · simp only [segments, h, hc, ite_true]
      intro s hs; simp only [List.mem_cons] at hs; rcases hs with rfl | hs
      · simp
      · exact ih s (List.mem_cons.2 hs)
    · simp only [segments, h, hc, ite_false]
      intro s hs; simp only [List.mem_cons] at hs; rcases hs with rfl | hs
      · have := ih s' (by simp); simp [Ne.symm hc, this]
      · exact ih s (List.mem_cons_of_mem _ hs)

theorem mem_of_mem_segments (g : Chars) : ∀ s ∈ segments g, ∀ c ∈ s, c ∈ g := by
  induction g with
  | nil => simp [segments]
  | cons c cs ih =>
    obtain ⟨s', rest, h⟩ := segments_ne_nil cs
    rw [h] at ih
    by_cases hc : c = '/'
    · simp only [segments, h, hc, ite_true]
      intro s hs d hd; simp only [List.mem_cons] at hs; rcases hs with rfl | hs
      · simp at hd
      · exact List.mem_cons_of_mem _ (ih s (List.mem_cons.2 hs) d hd)
    · simp only [segments, h, hc, ite_false]
      intro s hs d hd; simp only [List.mem_cons] at hs; rcases hs with rfl | hs
      · simp only [List.mem_cons] at hd; rcases hd with rfl | hd
        · simp
        · exact List.mem_cons_of_mem _ (ih s' (by simp) d hd)
      · exact List.mem_cons_of_mem _ (ih s (List.mem_cons_of_mem _ hs) d hd)

theorem join_single (s : Chars) : join [s] = s := rfl
theorem join_cons2 (s t : Chars) (r : List Chars) : join (s :: t :: r) = s ++ '/' :: join (t :: r) := rfl

theorem join_segments (g : Chars) : join (segments g) = g := by
  induction g with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨s, rest, h⟩ := segments_ne_nil cs
    rw [h] at ih
    by_cases hc : c = '/'
    · simp only [segments, h, hc, ite_true, join_cons2]; simp [ih]
    · simp only [segments, h, hc, ite_false]
      cases rest with
      | nil => rw [join_single]; simp [join_single] at ih; simp [ih]
      | cons r rs => rw [join_cons2]; rw [join_cons2] at ih; simp [← ih]

theorem join_cons_ne (s : Chars) (t : List Chars) (ht : t ≠ []) : join (s :: t) = s ++ '/' :: join t := by
  cases t with
  | nil => exact absurd rfl ht
  | cons u v => rfl

theorem segments_join (d : List Chars) (hd : d ≠ []) (h : ∀ s ∈ d, '/' ∉ s) : segments (join d) = d := by
  induction d with
  | nil => exact absurd rfl hd
  | cons s t ih =>
    cases t with
    | nil => rw [join_single, segments_noslash s (h s (by simp))]
    | cons u v =>
      rw [join_cons2, segments_append, segments_noslash s (h s (by simp)),
        ih (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      rfl

theorem mem_join (d : List Chars) : ∀ c ∈ join d, c = '/' ∨ ∃ s ∈ d, c ∈ s := by
  induction d with
  | nil => simp [join]
  | cons s t ih =>
    cases t with
    | nil => intro c hc; right; exact ⟨s, by simp, by simpa [join_single] using hc⟩
    | cons u v =>
      intro c hc; rw [join_cons2] at hc; simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | hc
      · right; exact ⟨s, by simp, hc⟩
      · left; rfl
      · rcases ih c hc with h | ⟨x, hx, hc'⟩
        · left; exact h
        · right; exact ⟨x, List.mem_cons_of_mem _ hx, hc'⟩

theorem hds_cons (c : Char) (cs : Chars) :
    hasDoubleSlash (c :: cs) = (decide (c = '/' ∧ cs.head? = some '/') || hasDoubleSlash cs) := by
  cases cs with
  | nil => simp [hasDoubleSlash]
  | cons d ds =>
    by_cases h : c = '/' ∧ d = '/'
    · obtain ⟨rfl, rfl⟩ := h; simp [hasDoubleSlash]
    · have : ¬ (c = '/' ∧ (d :: ds).head? = some '/') := by simpa using h
      simp only [this, decide_false, Bool.false_or]
      by_cases hc : c = '/'
      · subst hc
        have hd : d ≠ '/' := fun e => h ⟨rfl, e⟩
        simp [hasDoubleSlash, hd]
      · simp [hasDoubleSlash, hc]

theorem hasDoubleSlash_iff (l : Chars) : hasDoubleSlash l = true ↔ ∃ u r, l = u ++ '/' :: '/' :: r := by
  induction l with
  | nil => simp [hasDoubleSlash]
  | cons c cs ih =>
    rw [hds_cons]
    constructor
    · intro h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨rfl, h2⟩ | h
      · cases cs with
        | nil => simp at h2
        | cons d ds => simp at h2; subst h2; exact ⟨[], ds, rfl⟩
      · obtain ⟨u, r, e⟩ := ih.1 h; exact ⟨c :: u, r, by simp [e]⟩
    · rintro ⟨u, r, e⟩
      cases u with
      | nil => simp at e; obtain ⟨rfl, rfl, rfl⟩ := e; simp
      | cons d u => simp at e; obtain ⟨rfl, e⟩ := e; simp [ih.2 ⟨u, r, e⟩]

theorem join_append (d rest : List Chars) (hd : d ≠ []) (hr : rest ≠ []) :
    join (d ++ rest) = join d ++ '/' :: join rest := by
  induction d with
  | nil => exact absurd rfl hd
  | cons s t ih =>
    cases t with
    | nil => obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hr; simp [join_cons2, join_single]
    | cons u v =>
      have := ih (by simp)
      simp only [List.cons_append] at this ⊢
      rw [join_cons2, this, join_cons2]; simp

theorem head_empty_seg (g : Chars) (s : Chars) (rest : List Chars) (h : segments g = s :: rest) (hs : s = []) :
    g = [] ∨ g.head? = some '/' := by
  cases g with
  | nil => simp
  | cons c cs =>
    obtain ⟨s', r', h'⟩ := segments_ne_nil cs
    by_cases hc : c = '/' <;> simp_all [segments]

/-- An empty segment after the first means a trailing slash or a `//`. -/
theorem tail_empty (g : Chars) : [] ∈ (segments g).tail → g.getLast? = some '/' ∨ hasDoubleSlash g = true := by
  induction g with
  | nil => simp [segments]
  | cons c cs ih =>
    obtain ⟨s, rest, h⟩ := segments_ne_nil cs
    by_cases hc : c = '/'
    · subst hc
      simp only [segments, h, ite_true, List.tail_cons, List.mem_cons]
      rintro (hs | hr)
      · rcases head_empty_seg cs s rest h hs.symm with e | e
        · subst e; simp
        · cases cs with
          | nil => simp at e
          | cons d ds => simp at e; subst e; simp [hasDoubleSlash]
      · have := ih (by rw [h]; exact hr)
        rcases this with e | e
        · left; cases cs with
          | nil => simp [segments] at h; simp [h] at hr
          | cons d ds => simpa [List.getLast?_cons] using e
        · right; rw [hds_cons]; simp [e]
    · simp only [segments, h, hc, ite_false, List.tail_cons]
      intro hr
      rcases ih (by rw [h]; exact hr) with e | e
      · left; cases cs with
        | nil => simp [segments] at h; simp [h] at hr
        | cons d ds => simpa [List.getLast?_cons] using e
      · right; rw [hds_cons]; simp [e]

theorem refusalChars_none_iff (g : Chars) : refusalChars g = none ↔
    (∀ c ∈ g, forbiddenChar c = false) ∧ ¬ (['.', '/'] <+: g) ∧
    (∀ s ∈ segments g, s ≠ [] ∧ s ≠ ['.', '.']) := by
  obtain ⟨s0, r0, h0⟩ := segments_ne_nil g
  have hne : [] ∈ segments g → g = [] ∨ g.head? = some '/' ∨ g.getLast? = some '/' ∨ hasDoubleSlash g = true := by
    intro hm; rw [h0] at hm
    rcases List.mem_cons.1 hm with e | e
    · rcases head_empty_seg g _ _ h0 e.symm with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    · rcases tail_empty g (by rw [h0]; exact e) with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
  have hem : g = [] ∨ g.head? = some '/' ∨ g.getLast? = some '/' ∨ hasDoubleSlash g = true → [] ∈ segments g := by
    rintro (e | e | e | e)
    · subst e; simp [segments]
    · cases g with
      | nil => simp at e
      | cons c cs => simp at e; subst e; rw [segments_cons_slash]; simp
    · obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.1 e
      rw [hu, show u ++ [('/' : Char)] = u ++ '/' :: [] from rfl, segments_append]; simp [segments]
    · obtain ⟨u, r, hu⟩ := (hasDoubleSlash_iff g).1 e
      rw [hu, segments_append, segments_cons_slash]; simp
  have hnone : refusalChars g = none ↔ ¬ g.isEmpty = true ∧ ¬ g.any forbiddenChar = true ∧ ¬ g.head? = some '/' ∧
      ¬ ['.', '/'].isPrefixOf g = true ∧ ¬ g.getLast? = some '/' ∧ ¬ hasDoubleSlash g = true ∧
      ¬ (segments g).any (· == ['.', '.']) = true := by
    unfold refusalChars; repeat' split
    all_goals simp_all
  rw [hnone]
  have hdot : ['.', '/'].isPrefixOf g = true ↔ ['.', '/'] <+: g := by simp
  have hany : g.any forbiddenChar = true ↔ ¬ ∀ c ∈ g, forbiddenChar c = false := by
    constructor
    · intro h h2; obtain ⟨c, hc, hf⟩ := List.any_eq_true.1 h; simp [h2 c hc] at hf
    · intro h; apply Classical.byContradiction; intro h3
      exact h fun c hc => Classical.byContradiction fun h4 => h3 (List.any_eq_true.2 ⟨c, hc, by simpa using h4⟩)
  have hdd : (segments g).any (· == ['.', '.']) = true ↔ ['.', '.'] ∈ segments g := by simp
  rw [hdot, hany, hdd]
  by_cases hbad : g = [] ∨ g.head? = some '/' ∨ g.getLast? = some '/' ∨ hasDoubleSlash g = true
  · have hm := hem hbad
    have : ¬ (∀ s ∈ segments g, s ≠ [] ∧ s ≠ ['.', '.']) := fun h => (h _ hm).1 rfl
    simp only [this, and_false, iff_false]
    rcases hbad with e | e | e | e
    · subst e; simp
    · simp [e]
    · simp [e]
    · simp [e]
  · simp only [not_or] at hbad
    obtain ⟨b1, b2, b3, b4⟩ := hbad
    have hnm : [] ∉ segments g := fun hm => by
      rcases hne hm with e | e | e | e <;> simp_all
    simp [b1, b2, b3, b4]
    intro _ _
    constructor
    · intro h5 s hs
      exact ⟨fun e => hnm (e ▸ hs), fun e => h5 (e ▸ hs)⟩
    · intro h h5; exact (h _ h5).2 rfl

/-! ## Working directories, `startDir`, `under` -/

/-- A working directory is valid exactly when it is a valid glob with no `*` and no `?`. -/
theorem validCwd_iff (c : String) :
    Glob.validCwd c = true ↔ Glob.valid c = true ∧ (c.toList.any isWild = false) := by
  unfold Glob.validCwd Glob.valid Glob.cwdRefusal
  cases h : Glob.refusal c <;> simp

-- Non-vacuity: `src/lib` is a valid working directory; `src/*` is a glob but not a working directory.
example : Glob.validCwd "src/lib" = true := by decide
example : Glob.validCwd "src/*" = false := by decide
example : Glob.validCwd "../x" = false := by decide

theorem dirSegs_split (l : List Chars) :
    ∃ rest, l = dirSegs l ++ rest ∧ (l ≠ [] → rest ≠ []) ∧ ∀ s ∈ dirSegs l, s.any isWild = false := by
  induction l with
  | nil => exact ⟨[], rfl, by simp, by simp [dirSegs]⟩
  | cons x t ih =>
    cases t with
    | nil => exact ⟨[x], by simp [dirSegs], by simp, by simp [dirSegs]⟩
    | cons y u =>
      by_cases hw : x.any isWild = true
      · exact ⟨x :: y :: u, by simp [dirSegs, hw], by simp, by simp [dirSegs, hw]⟩
      · obtain ⟨r, h1, h2, h3⟩ := ih
        refine ⟨r, ?_, fun _ => h2 (by simp), ?_⟩
        · have hw' : x.any isWild = false := by simpa using hw
          simp only [dirSegs, hw', Bool.false_eq_true, ite_false, List.cons_append]; simp; exact h1
        · have hw' : x.any isWild = false := by simpa using hw
          simp only [dirSegs, hw', Bool.false_eq_true, ite_false]
          intro s hs; rcases List.mem_cons.1 hs with rfl | hs
          · simpa using hw
          · exact h3 s hs

theorem dirSegs_prefix (g : Chars) : ∃ rest, segments g = dirSegs (segments g) ++ rest ∧ rest ≠ [] ∧
    ∀ s ∈ dirSegs (segments g), s.any isWild = false := by
  obtain ⟨s0, r0, h0⟩ := segments_ne_nil g
  obtain ⟨rest, h1, h2, h3⟩ := dirSegs_split (segments g)
  exact ⟨rest, h1, h2 (by rw [h0]; simp), h3⟩

theorem prefix_of_dir (g D : Chars) (d rest : List Chars) (hg : segments g = d ++ rest) (hd : d ≠ []) (hr : rest ≠ [])
    (hD : D = join d) : g = D ++ '/' :: join rest := by
  rw [hD, ← join_append d rest hd hr, ← hg, join_segments]

/-- For a valid glob, the directory it starts in is empty (the root) or a valid working directory (no wildcard) that is followed by `/` in the glob: a directory prefix of the pattern. Rules out a start directory that is not literally the front of the pattern. -/
theorem startDir_prefix (g : String) (h : Glob.valid g = true) :
    Glob.startDir g = "" ∨ (Glob.validCwd (Glob.startDir g) = true ∧
      ∃ rest, g.toList = (Glob.startDir g).toList ++ '/' :: rest) := by
  have hn : refusalChars g.toList = none := of_decide_eq_true h
  obtain ⟨hf, hdot, hs⟩ := (refusalChars_none_iff _).1 hn
  obtain ⟨rest, h1, h2, h3⟩ := dirSegs_prefix g.toList
  generalize hd : dirSegs (segments g.toList) = d at h1 h3
  have hsd : startDir g = String.ofList (join d) := by simp [startDir, hd]
  by_cases hde : d = []
  · left; rw [hsd, hde]; decide
  right
  have hg := prefix_of_dir g.toList (join d) d rest h1 hde h2 rfl
  have hdm : ∀ s ∈ d, s ∈ segments g.toList := fun s hs => by rw [h1]; exact List.mem_append_left _ hs
  have hT : (String.ofList (join d)).toList = join d := by simp
  have hseg : segments (join d) = d := segments_join d hde (fun s hs => noslash_of_mem _ s (hdm s hs))
  have hnone : refusalChars (join d) = none := by
    refine (refusalChars_none_iff _).2 ⟨fun c hc => hf c ?_, fun hp => hdot ?_, ?_⟩
    · rw [hg]; exact List.mem_append_left _ hc
    · rw [hg]; exact hp.trans ⟨_, rfl⟩
    · rw [hseg]; exact fun s hs' => hs s (hdm s hs')
  refine ⟨?_, join rest, by rw [hsd, hT]; exact hg⟩
  have hv : Glob.valid (String.ofList (join d)) = true := by simp [Glob.valid, Glob.refusal, hT, hnone]
  rw [hsd, validCwd_iff]
  refine ⟨hv, ?_⟩
  rw [hT]
  apply Classical.byContradiction; intro hw
  have hw' : (join d).any isWild = true := by simpa using hw
  obtain ⟨c, hc, hwc⟩ := List.any_eq_true.1 hw'
  rcases mem_join d c hc with e | ⟨x, hx, hcx⟩
  · subst e; simp [isWild] at hwc
  · have := h3 x hx; exact absurd (List.any_eq_true.2 ⟨c, hcx, hwc⟩) (by simp [this])

/-- The directory under the root: every path lies under `""`. -/
theorem under_root (p : String) : Glob.under "" p = true := by
  obtain ⟨s, r, h⟩ := segments_ne_nil p.toList
  simp [Glob.under, h, properPrefix]

/-- A path is never under itself (the prefix is proper): rules out a directory enclosing itself. -/
theorem under_irrefl (d : String) (h : d ≠ "") : Glob.under d d = false := by
  have : ∀ l : List Chars, properPrefix l l = false := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => simp [properPrefix, ih]
  simp [Glob.under, h, this]

example : Glob.startDir "src/lib/*" = "src/lib" := by decide
example : Glob.startDir "core/*.py" = "core" := by decide
example : Glob.startDir "docs/*/index.md" = "docs" := by decide
example : Glob.startDir "README.md" = "" := by decide
example : Glob.startDir "*.md" = "" := by decide
example : Glob.under "core/io" "core/iodata.json" = false := by decide
example : Glob.under "core/io" "core/io/x.json" = true := by decide
example : Glob.under "core" "core/io/x.json" = true := by decide
example : Glob.under "core/io" "core/io" = false := by decide
example : Glob.under "" "README.md" = true := by decide

end VbmAreas
