import VbmDecision.Decode
import VbmDecisionProofs.Check
/-! # Decoding questions and answers over `J` (S7a): proofs

W1 `decode-refuses-unknown`: a duplicate key is `duplicateKey` and an extra key `unknownField`, each naming the key; a tag outside the four is `unknownType`. W2 `decode-wellformed`: a decoded answer is well formed for its question (and a decoded question is valid). W4 `decode-total`: a value nested deeper than `maxNestingDepth` is `nestingTooDeep`, and every decoder returns an `ok` or a typed refusal. The decoders are total functions, so W4 is also the build; the theorems state what a caller reads from it. -/
namespace VbmDecision
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The duplicate scan -/

theorem firstDup_count (l : List String) (k : String) (h : firstDup l = some k) : 2 ≤ l.count k := by
  induction l with
  | nil => simp [firstDup] at h
  | cons a ks ih =>
    unfold firstDup at h
    by_cases ha : a ∈ ks
    · simp only [ha, ite_true, Option.some.injEq] at h
      subst h
      have := List.count_pos_iff.2 ha
      rw [List.count_cons_self]; omega
    · simp only [ha, ite_false] at h
      have := ih h
      rw [List.count_cons]; omega

theorem firstDup_eq_none (l : List String) : firstDup l = none ↔ l.Nodup := by
  induction l with
  | nil => simp [firstDup]
  | cons a ks ih =>
    unfold firstDup
    by_cases ha : a ∈ ks
    · simp [ha]
    · simp [ha, ih]

theorem firstDup_exists (l : List String) (h : ¬ l.Nodup) : ∃ k, firstDup l = some k := by
  cases hf : firstDup l with
  | none => exact absurd ((firstDup_eq_none l).1 hf) h
  | some k => exact ⟨k, rfl⟩

/-! ## Objects -/

theorem objOf_dup (path : String) (al : Option (List String)) (kvs : List (String × J)) (k : String)
    (h : firstDup (kvs.map (·.1)) = some k) : objOf path al (.obj kvs) = .error ⟨.duplicateKey, pathKey path k⟩ := by
  simp [objOf, dupCheck, h, refuse, bind, Except.bind]

theorem objOf_ok (path : String) (al : Option (List String)) (kvs : List (String × J))
    (h : (kvs.map (·.1)).Nodup) (hal : ∀ a, al = some a → unknownCheck path a kvs = .ok ()) :
    objOf path al (.obj kvs) = .ok kvs := by
  have hd : firstDup (kvs.map (·.1)) = none := (firstDup_eq_none _).2 h
  cases al with
  | none => simp [objOf, dupCheck, hd, bind, Except.bind, pure, Except.pure]
  | some a => simp [objOf, dupCheck, hd, hal a rfl, bind, Except.bind, pure, Except.pure]

theorem find_unique (ks : List String) (allowed : List String) (k : String) (hk : k ∈ ks) (hn : k ∉ allowed)
    (hu : ∀ k' ∈ ks, k' ∉ allowed → k' = k) : ks.find? (fun k => !allowed.contains k) = some k := by
  induction ks with
  | nil => simp at hk
  | cons a ks ih =>
    by_cases ha : a ∈ allowed
    · have hak : a ≠ k := fun h => hn (h ▸ ha)
      simp only [List.find?_cons, List.contains_iff_mem.2 ha]
      simp only [Bool.not_true]
      apply ih
      · simp at hk; rcases hk with h | h; exact absurd h.symm hak; exact h
      · exact fun k' hk' => hu k' (List.mem_cons_of_mem _ hk')
    · have := hu a (by simp) ha
      subst this
      simp [List.contains_iff_mem, ha]

/-- The check names the one key outside the list. -/
theorem unknownCheck_unique (path : String) (allowed : List String) (kvs : List (String × J)) (k : String)
    (hk : k ∈ kvs.map (·.1)) (hn : k ∉ allowed) (hu : ∀ k' ∈ kvs.map (·.1), k' ∉ allowed → k' = k) :
    unknownCheck path allowed kvs = .error ⟨.unknownField, pathKey path k⟩ := by
  have := find_unique _ _ k hk hn hu
  unfold unknownCheck
  rw [this]; rfl

/-! ## W1: duplicate keys, extra keys, unknown tags -/

/-- The check refuses any key outside the list, naming one that is in the object and outside the list. -/
theorem unknownCheck_extra (path : String) (allowed : List String) (kvs : List (String × J)) (k : String)
    (hk : k ∈ kvs.map (·.1)) (hn : k ∉ allowed) :
    ∃ k', k' ∈ kvs.map (·.1) ∧ k' ∉ allowed ∧ unknownCheck path allowed kvs = .error ⟨.unknownField, pathKey path k'⟩ := by
  unfold unknownCheck
  cases hf : (kvs.map (·.1)).find? (fun k => !allowed.contains k) with
  | none =>
    have := List.find?_eq_none.1 hf k hk
    simp [List.contains_iff_mem, hn] at this
  | some k' =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    refine ⟨k', h1, ?_, rfl⟩
    simpa [List.contains_iff_mem] using h2

/-- W1, any extra key in a question: refused as `unknownField`, naming an extra key. -/
theorem Question.decodeAt_extra (path : String) (kvs : List (String × J)) (kd : Kind) (k : String)
    (hnd : (kvs.map (·.1)).Nodup) (ht : tagOf path kvs = .ok kd) (hk : k ∈ kvs.map (·.1)) (hn : k ∉ qKeys kd) :
    ∃ k', k' ∈ kvs.map (·.1) ∧ k' ∉ qKeys kd ∧ Question.decodeAt path (.obj kvs) = .error ⟨.unknownField, pathKey path k'⟩ := by
  obtain ⟨k', h1, h2, h3⟩ := unknownCheck_extra path (qKeys kd) kvs k hk hn
  have ho := objOf_ok path none kvs hnd (by simp)
  exact ⟨k', h1, h2, by simp [Question.decodeAt, ho, ht, h3, bind, Except.bind]⟩

/-- W1, any extra key in an answer of the question's kind: refused as `unknownField`, naming an extra key. -/
theorem Answer.decodeAt_extra (path : String) (q : Question) (kvs : List (String × J)) (k : String)
    (hnd : (kvs.map (·.1)).Nodup) (ht : tagOf path kvs = .ok q.kindOf) (hk : k ∈ kvs.map (·.1)) (hn : k ∉ aKeys q.kindOf) :
    ∃ k', k' ∈ kvs.map (·.1) ∧ k' ∉ aKeys q.kindOf ∧ Answer.decodeAt path q (.obj kvs) = .error ⟨.unknownField, pathKey path k'⟩ := by
  obtain ⟨k', h1, h2, h3⟩ := unknownCheck_extra path (aKeys q.kindOf) kvs k hk hn
  have ho := objOf_ok path none kvs hnd (by simp)
  exact ⟨k', h1, h2, by simp [Answer.decodeAt, ho, ht, h3, bind, Except.bind]⟩

/-- W1, duplicate key in any object: refused, naming a key that occurs twice. -/
theorem objOf_duplicate (path : String) (al : Option (List String)) (kvs : List (String × J))
    (h : ¬ (kvs.map (·.1)).Nodup) :
    ∃ k, 2 ≤ (kvs.map (·.1)).count k ∧ objOf path al (.obj kvs) = .error ⟨.duplicateKey, pathKey path k⟩ := by
  obtain ⟨k, hk⟩ := firstDup_exists _ h
  exact ⟨k, firstDup_count _ _ hk, objOf_dup path al kvs k hk⟩

/-- W1, duplicate key at the top of a question. -/
theorem Question.decodeAt_duplicate (path : String) (kvs : List (String × J)) (h : ¬ (kvs.map (·.1)).Nodup) :
    ∃ k, 2 ≤ (kvs.map (·.1)).count k ∧ Question.decodeAt path (.obj kvs) = .error ⟨.duplicateKey, pathKey path k⟩ := by
  obtain ⟨k, hc, he⟩ := objOf_duplicate path none kvs h
  exact ⟨k, hc, by simp [Question.decodeAt, he, bind, Except.bind]⟩

/-- W1, duplicate key at the top of an answer. -/
theorem Answer.decodeAt_duplicate (path : String) (q : Question) (kvs : List (String × J)) (h : ¬ (kvs.map (·.1)).Nodup) :
    ∃ k, 2 ≤ (kvs.map (·.1)).count k ∧ Answer.decodeAt path q (.obj kvs) = .error ⟨.duplicateKey, pathKey path k⟩ := by
  obtain ⟨k, hc, he⟩ := objOf_duplicate path none kvs h
  exact ⟨k, hc, by simp [Answer.decodeAt, he, bind, Except.bind]⟩

/-- W1, extra key in a question of kind `kd`: `unknownField` naming it. -/
theorem Question.decodeAt_unknownField (path : String) (kvs : List (String × J)) (kd : Kind) (k : String)
    (hnd : (kvs.map (·.1)).Nodup) (ht : tagOf path kvs = .ok kd)
    (hk : k ∈ kvs.map (·.1)) (hn : k ∉ qKeys kd) (hu : ∀ k' ∈ kvs.map (·.1), k' ∉ qKeys kd → k' = k) :
    Question.decodeAt path (.obj kvs) = .error ⟨.unknownField, pathKey path k⟩ := by
  have ho := objOf_ok path none kvs hnd (by simp)
  simp [Question.decodeAt, ho, ht, unknownCheck_unique path _ kvs k hk hn hu, bind, Except.bind, pure, Except.pure]

/-- W1, extra key in an answer of the question's kind: `unknownField` naming it. -/
theorem Answer.decodeAt_unknownField (path : String) (q : Question) (kvs : List (String × J)) (k : String)
    (hnd : (kvs.map (·.1)).Nodup) (ht : tagOf path kvs = .ok q.kindOf)
    (hk : k ∈ kvs.map (·.1)) (hn : k ∉ aKeys q.kindOf) (hu : ∀ k' ∈ kvs.map (·.1), k' ∉ aKeys q.kindOf → k' = k) :
    Answer.decodeAt path q (.obj kvs) = .error ⟨.unknownField, pathKey path k⟩ := by
  have ho := objOf_ok path none kvs hnd (by simp)
  simp [Answer.decodeAt, ho, ht, unknownCheck_unique path _ kvs k hk hn hu, bind, Except.bind, pure, Except.pure]

/-- W1, a `type` tag outside the four: `unknownType` at the tag. -/
theorem tagOf_unknownType (path : String) (kvs : List (String × J)) (s : String) (h : kvs.lookup "type" = some (.str s))
    (hs : s ≠ "noul" ∧ s ≠ "choice" ∧ s ≠ "score" ∧ s ≠ "box") :
    tagOf path kvs = .error ⟨.unknownType, pathKey path "type"⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  simp [tagOf, h, h1, h2, h3, h4, refuse]

theorem Question.decodeAt_unknownType (path : String) (kvs : List (String × J)) (s : String)
    (hnd : (kvs.map (·.1)).Nodup) (h : kvs.lookup "type" = some (.str s))
    (hs : s ≠ "noul" ∧ s ≠ "choice" ∧ s ≠ "score" ∧ s ≠ "box") :
    Question.decodeAt path (.obj kvs) = .error ⟨.unknownType, pathKey path "type"⟩ := by
  have ho := objOf_ok path none kvs hnd (by simp)
  simp [Question.decodeAt, ho, tagOf_unknownType path kvs s h hs, bind, Except.bind]

theorem Answer.decodeAt_unknownType (path : String) (q : Question) (kvs : List (String × J)) (s : String)
    (hnd : (kvs.map (·.1)).Nodup) (h : kvs.lookup "type" = some (.str s))
    (hs : s ≠ "noul" ∧ s ≠ "choice" ∧ s ≠ "score" ∧ s ≠ "box") :
    Answer.decodeAt path q (.obj kvs) = .error ⟨.unknownType, pathKey path "type"⟩ := by
  have ho := objOf_ok path none kvs hnd (by simp)
  simp [Answer.decodeAt, ho, tagOf_unknownType path kvs s h hs, bind, Except.bind]

/-! ## W2: a decoded value is valid or well formed -/

/-- W2 at a path. -/
theorem Answer.decodeAt_wellFormed (path : String) (q : Question) (j : J) (a : Answer)
    (h : Answer.decodeAt path q j = .ok a) : WellFormed q a := by
  unfold Answer.decodeAt at h
  cases h1 : objOf path none j with
  | error e => simp [h1, bind, Except.bind] at h
  | ok kvs =>
    cases h2 : tagOf path kvs with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok kd =>
      by_cases h3 : kd = q.kindOf
      · subst h3
        cases h4 : unknownCheck path (aKeys q.kindOf) kvs with
        | error e => simp [h1, h2, h4, bind, Except.bind] at h
        | ok u =>
          cases h5 : rawAnswer path q q.kindOf kvs with
          | error e => simp [h1, h2, h4, h5, bind, Except.bind] at h
          | ok a' =>
            simp only [h1, h2, h4, h5, bind, Except.bind, ite_true] at h
            unfold checkedAt at h
            cases h6 : checkAnswer q a' with
            | error e => simp [h6] at h
            | ok u' =>
              simp [h6] at h
              subst h
              exact (checkAnswer_ok_iff q a').1 h6
      · simp [h1, h2, h3, refuse, bind, Except.bind] at h

/-- W2: the root decoder. -/
theorem Answer.decode_wellFormed (q : Question) (j : J) (a : Answer) (h : Answer.decode q j = .ok a) : WellFormed q a := by
  unfold Answer.decode at h
  by_cases hd : J.depth j ≤ maxNestingDepth
  · simp only [hd, ite_true] at h; exact Answer.decodeAt_wellFormed "" q j a h
  · simp [hd, refuse] at h

/-- W2 for questions: a decoded question is valid. -/
theorem Question.decodeAt_valid (path : String) (j : J) (q : Question) (h : Question.decodeAt path j = .ok q) : q.Valid := by
  unfold Question.decodeAt at h
  cases h1 : objOf path none j with
  | error e => simp [h1, bind, Except.bind] at h
  | ok kvs =>
    cases h2 : tagOf path kvs with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok kd =>
      cases h4 : unknownCheck path (qKeys kd) kvs with
      | error e => simp [h1, h2, h4, bind, Except.bind] at h
      | ok u =>
        cases h5 : rawQuestion path kd kvs with
        | error e => simp [h1, h2, h4, h5, bind, Except.bind] at h
        | ok q' =>
          simp only [h1, h2, h4, h5, bind, Except.bind] at h
          cases h6 : q'.check with
          | error e => simp [h6] at h
          | ok u' =>
            simp [h6, pure, Except.pure] at h
            subst h
            exact (question_check_ok_iff q').1 h6

theorem Question.decode_valid (j : J) (q : Question) (h : Question.decode j = .ok q) : q.Valid := by
  unfold Question.decode at h
  by_cases hd : J.depth j ≤ maxNestingDepth
  · simp only [hd, ite_true] at h; exact Question.decodeAt_valid "" j q h
  · simp [hd, refuse] at h

/-! ## W4: totality and the nesting guard -/

/-- W4: a value nested deeper than `maxNestingDepth` is refused by the root question decoder. -/
theorem Question.decode_nestingTooDeep (j : J) (h : maxNestingDepth < J.depth j) :
    Question.decode j = .error ⟨.nestingTooDeep, ""⟩ := by
  have : ¬ J.depth j ≤ maxNestingDepth := by omega
  simp [Question.decode, this, refuse]

/-- W4: the same for the root answer decoder. -/
theorem Answer.decode_nestingTooDeep (q : Question) (j : J) (h : maxNestingDepth < J.depth j) :
    Answer.decode q j = .error ⟨.nestingTooDeep, ""⟩ := by
  have : ¬ J.depth j ≤ maxNestingDepth := by omega
  simp [Answer.decode, this, refuse]

/-- W4: within the depth limit the root decoders are the decoders at the root (no further depth refusal exists). -/
theorem decode_within (q : Question) (j : J) (h : J.depth j ≤ maxNestingDepth) :
    Question.decode j = Question.decodeAt "" j ∧ Answer.decode q j = Answer.decodeAt "" q j := by
  simp [Question.decode, Answer.decode, h]

/-- W4: each root decoder returns an `ok` or a typed refusal, for every `J`. -/
theorem decode_total (q : Question) (j : J) :
    ((∃ x, Question.decode j = .ok x) ∨ ∃ r : Refusal, Question.decode j = .error r) ∧
    ((∃ a, Answer.decode q j = .ok a) ∨ ∃ r : Refusal, Answer.decode q j = .error r) := by
  refine ⟨?_, ?_⟩
  · cases h : Question.decode j with
    | ok x => exact .inl ⟨x, rfl⟩
    | error r => exact .inr ⟨r, rfl⟩
  · cases h : Answer.decode q j with
    | ok x => exact .inl ⟨x, rfl⟩
    | error r => exact .inr ⟨r, rfl⟩

/-! ## Witnesses -/

set_option maxRecDepth 8000

private def p (n : Nat) (h : n ≤ 1000000 := by decide) : Prob := ⟨n, h⟩
private def dec (m : Nat) (e : Int) : J := .num ⟨false, m, e⟩
private def qn : Question := .noul "Is the invoice overdue?" none
private def qc : Question := .choice "Which tone?" [("calm", none), ("angry", some "hostile words")]
private def qs : Question := .score "How urgent?" ["none", "some", "high"]
private def qb : Question := .box "Where?"
private def jn (extra : List (String × J) := []) : J := .obj ([("type", .str "noul"), ("noul", dec 9731 (-4))] ++ extra)
private def jc : J := .obj [("type", .str "choice"), ("choice", .str "calm"),
  ("probabilities", .obj [("calm", dec 8 (-1)), ("angry", dec 2 (-1))]), ("confidence", dec 8 (-1))]
private def jsc : J := .obj [("type", .str "score"), ("score", dec 15 (-1)), ("confidence", dec 7 (-1)),
  ("probabilities", .obj [("0", dec 0 0), ("1", dec 5 (-1)), ("2", dec 5 (-1))]),
  ("legend", .obj [("0", .str "none"), ("1", .str "some"), ("2", .str "high")])]
private def jb : J := .obj [("type", .str "box"), ("box", .obj [("top", dec 2 (-1)), ("bottom", dec 6 (-1)), ("left", dec 1 (-1)), ("right", dec 9 (-1))]),
  ("confidence", dec 8 (-1))]
/-- A value nested `n` arrays deep. -/
private def nest : Nat → J
  | 0 => .null
  | n + 1 => .arr [nest n]

-- W2 witnesses: the four vectors decode.
example : Answer.decode qn (jn) = .ok (.noul (p 973100)) := by rfl
example : Answer.decode qc jc = .ok (.choice "calm" [("calm", p 800000), ("angry", p 200000)] (p 800000)) := by rfl
example : Answer.decode qs jsc = .ok (.score 1500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"]) := by rfl
example : Answer.decode qb jb = .ok (.box ⟨p 200000, p 600000, p 100000, p 900000⟩ (p 800000)) := by rfl
example : Question.decode (Question.encode qc) = .ok qc := by rfl
example : Question.decode (Question.encode qs) = .ok qs := by rfl
example : Question.decode (Question.encode (.noul "i" (some ("yes", "no")))) = .ok (.noul "i" (some ("yes", "no"))) := by rfl
example : Question.decode (Question.encode qb) = .ok qb := by rfl
example : Answer.decode qs (Answer.encode (.score 1500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"])) =
    .ok (.score 1500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"]) := by rfl

-- the vectors of the spec, at their paths.
example : Answer.decodeAt "answers.overdue" qn (.obj [("type", .str "noul"), ("noul", dec 12 (-1))]) = .error ⟨.outOfRange, "answers.overdue.noul"⟩ := by rfl
example : Answer.decodeAt "answers.overdue" qn (.obj [("type", .str "noul"), ("noul", dec 1234567 (-7))]) = .error ⟨.tooPrecise, "answers.overdue.noul"⟩ := by rfl
example : Answer.decodeAt "answers.overdue" qn (.obj [("type", .str "noul"), ("noul", .num ⟨true, 1, -1⟩)]) = .error ⟨.negative, "answers.overdue.noul"⟩ := by rfl
example : Answer.decodeAt "answers.overdue" qn (.obj [("type", .str "noul"), ("noul", .str "0.5")]) = .error ⟨.wrongKind, "answers.overdue.noul"⟩ := by rfl
example : Answer.decodeAt "answers.tone" qc (.obj [("type", .str "choice"), ("choice", .str "calm"),
    ("probabilities", .obj [("calm", dec 7 (-1)), ("angry", dec 1 (-1))]), ("confidence", dec 7 (-1))]) =
    .error ⟨.sumOffOne, "answers.tone.probabilities"⟩ := by rfl
example : Answer.decodeAt "answers.tone" qc (.obj [("type", .str "choice"), ("choice", .str "happy"),
    ("probabilities", .obj [("calm", dec 8 (-1)), ("angry", dec 2 (-1))]), ("confidence", dec 8 (-1))]) =
    .error ⟨.unknownOption, "answers.tone.choice"⟩ := by rfl
example : Answer.decodeAt "answers.overdue" qn (jn [("reasoning", .str "because")]) = .error ⟨.unknownField, "answers.overdue.reasoning"⟩ := by rfl
example : Answer.decodeAt "answers.urgency" qs (.obj [("type", .str "score"), ("score", dec 25 (-1)), ("confidence", dec 7 (-1)),
    ("probabilities", .obj [("0", dec 0 0), ("1", dec 5 (-1)), ("2", dec 5 (-1))]),
    ("legend", .obj [("0", .str "none"), ("1", .str "some"), ("2", .str "high")])]) = .error ⟨.scoreOutOfScale, "answers.urgency.score"⟩ := by rfl
example : Answer.decodeAt "answers.where" qb (.obj [("type", .str "box"), ("box", .obj [("top", dec 6 (-1)), ("bottom", dec 2 (-1)), ("left", dec 1 (-1)), ("right", dec 9 (-1))]),
    ("confidence", dec 8 (-1))]) = .error ⟨.boxInverted, "answers.where.box"⟩ := by rfl
example : Answer.decodeAt "answers.overdue" qn jc = .error ⟨.typeMismatch, "answers.overdue.type"⟩ := by rfl

-- W1: duplicate keys (top level and nested), a missing field, an unknown tag, an extra key in a nested object.
example : Answer.decodeAt "a" qn (jn [("noul", dec 1 0)]) = .error ⟨.duplicateKey, "a.noul"⟩ := by rfl
example : Answer.decodeAt "a" qc (.obj [("type", .str "choice"), ("choice", .str "calm"),
    ("probabilities", .obj [("calm", dec 8 (-1)), ("calm", dec 2 (-1))]), ("confidence", dec 8 (-1))]) = .error ⟨.duplicateKey, "a.probabilities.calm"⟩ := by rfl
example : Answer.decodeAt "a" qb (.obj [("type", .str "box"), ("box", .obj [("top", dec 2 (-1)), ("top", dec 2 (-1))]), ("confidence", dec 8 (-1))]) =
    .error ⟨.duplicateKey, "a.box.top"⟩ := by rfl
example : Answer.decodeAt "a" qb (.obj [("type", .str "box"), ("box", .obj [("top", dec 2 (-1)), ("bottom", dec 6 (-1)), ("left", dec 1 (-1)), ("right", dec 9 (-1)), ("depth", dec 1 0)]),
    ("confidence", dec 8 (-1))]) = .error ⟨.unknownField, "a.box.depth"⟩ := by rfl
example : Answer.decodeAt "a" qn (.obj [("type", .str "yesno"), ("noul", dec 5 (-1))]) = .error ⟨.unknownType, "a.type"⟩ := by rfl
example : Answer.decodeAt "a" qn (.obj [("noul", dec 5 (-1))]) = .error ⟨.missingField, "a.type"⟩ := by rfl
example : Answer.decodeAt "a" qs (.obj [("type", .str "score"), ("score", dec 15 (-1)), ("confidence", dec 7 (-1)),
    ("probabilities", .obj [("0", dec 0 0), ("01", dec 5 (-1)), ("2", dec 5 (-1))]),
    ("legend", .obj [("0", .str "none"), ("1", .str "some"), ("2", .str "high")])]) = .error ⟨.badIndexKey, "a.probabilities.01"⟩ := by rfl
example : Answer.decodeAt "a" qs (.obj [("type", .str "score"), ("score", dec 15 (-1)), ("confidence", dec 7 (-1)),
    ("probabilities", .obj [("0", dec 0 0), ("1", dec 5 (-1))]),
    ("legend", .obj [("0", .str "none"), ("1", .str "some"), ("2", .str "high")])]) = .error ⟨.missingOption, "a.probabilities.2"⟩ := by rfl
example : Question.decodeAt "q" (.obj [("type", .str "choice"), ("instructions", .str "t"), ("criteria", .obj [("a", .null), ("a", .null)])]) = .error ⟨.duplicateKey, "q.criteria.a"⟩ := by rfl
example : Question.decodeAt "q" (.obj [("type", .str "box"), ("instructions", .str "t"), ("criteria", .null)]) = .error ⟨.unknownField, "q.criteria"⟩ := by rfl
example : Question.decodeAt "q" (.obj [("type", .str "noul"), ("instructions", .str "t"), ("extra", .null)]) = .error ⟨.unknownField, "q.extra"⟩ := by rfl
example : Question.decodeAt "q" (.obj [("type", .str "noul"), ("instructions", .str "t"), ("criteria", .obj [("true", .str "a"), ("false", .str "b"), ("maybe", .str "c")])]) =
    .error ⟨.unknownField, "q.criteria.maybe"⟩ := by rfl
example : Question.decodeAt "q" (.obj [("type", .str "choice"), ("instructions", .str "t"), ("criteria", .obj [("a", .null)])]) = .error ⟨.tooFewOptions, "q.criteria"⟩ := by rfl

-- the hypotheses of the W1 theorems can hold: the nested vector's keys are distinct, the extra key is unique.
example : ((jn [("reasoning", .str "x")]) matches .obj kvs) = true := by rfl
example : (["type", "noul", "reasoning"]).Nodup := by decide
example : "reasoning" ∉ aKeys .noul := by decide
example : ∀ k' ∈ ["type", "noul", "reasoning"], k' ∉ aKeys .noul → k' = "reasoning" := by decide
example : tagOf "a" [("type", .str "noul"), ("noul", dec 1 0), ("reasoning", .null)] = .ok .noul := by rfl
example : ¬ (["type", "noul", "noul"]).Nodup := by decide
example : ∃ k', k' ∈ ["type", "noul", "reasoning"] ∧ k' ∉ aKeys .noul := ⟨"reasoning", by decide, by decide⟩

-- W4: a vector nested 33 deep; 32 deep passes the guard.
example : J.depth (nest 33) = 33 := by rfl
example : Question.decode (nest 33) = .error ⟨.nestingTooDeep, ""⟩ := by rfl
example : Answer.decode qn (nest 33) = .error ⟨.nestingTooDeep, ""⟩ := by rfl
example : Answer.decode qn (nest 32) = .error ⟨.wrongKind, ""⟩ := by rfl

end VbmDecision
