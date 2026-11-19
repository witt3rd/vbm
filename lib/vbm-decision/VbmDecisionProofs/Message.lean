import VbmDecision.Message
import VbmDecisionProofs.Decode
import VbmDecisionProofs.Prob
import Std
/-! # Decoding and encoding the request and the response (S7b): proofs

W3 `message-roundtrip`: `Request.decode (Request.encode r) = ok r` for every valid request, and `Response.decode qs (Response.encode r) = ok r` for every response valid for the question set `qs`, the questions and answers in wire order. W4 `decode-total`: the request and response decoders return an `ok` or a typed refusal on every `J`, and refuse a value nested deeper than `maxNestingDepth` as `nestingTooDeep`. The proof goes through the exact round trip of each part: a probability, a position, an indexed object, a question, an answer of each kind, and the depth of what the encoders write. The decoders are total functions, so W4 is also the build. -/
namespace VbmDecision
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem mapM_ok {α β γ : Type} (f : β → Except Refusal γ) (e : α → β) (g : α → γ) :
    ∀ xs : List α, (∀ x ∈ xs, f (e x) = .ok (g x)) → (xs.map e).mapM f = .ok (xs.map g)
  | [], _ => by simp [pure, Except.pure]
  | x :: xs, h => by
    have h1 := h x (by simp)
    have h2 := mapM_ok f e g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [List.mapM_cons, h1, h2, bind, Except.bind, pure, Except.pure]

theorem unknownCheck_ok (path : String) (al : List String) (kvs : List (String × J)) (h : ∀ k ∈ kvs.map (·.1), k ∈ al) :
    unknownCheck path al kvs = .ok () := by
  unfold unknownCheck
  have : (kvs.map (·.1)).find? (fun k => !al.contains k) = none := by
    rw [List.find?_eq_none]; intro k hk; simp [List.contains_iff_mem, h k hk]
  rw [this]

theorem objOf_ok' (path : String) (al : Option (List String)) (kvs : List (String × J))
    (h : (kvs.map (·.1)).Nodup) (hal : ∀ a, al = some a → ∀ k ∈ kvs.map (·.1), k ∈ a) :
    objOf path al (.obj kvs) = .ok kvs :=
  objOf_ok path al kvs h (fun a ha => unknownCheck_ok path a kvs (hal a ha))

theorem lookup_of_mem (kvs : List (String × J)) (h : (kvs.map (·.1)).Nodup) (k : String) (v : J) (hm : (k, v) ∈ kvs) :
    kvs.lookup k = some v := by
  induction kvs with
  | nil => simp at hm
  | cons a ks ih =>
    have hn := List.nodup_cons.1 h
    rcases a with ⟨k0, v0⟩
    simp only [List.lookup_cons]
    by_cases hk : k0 = k
    · subst hk
      simp at hm
      rcases hm with ⟨_, rfl⟩ | hm
      · simp
      · exact absurd (List.mem_map_of_mem (f := (·.1)) hm) (by simpa using hn.1)
    · have : (k == k0) = false := by simpa using Ne.symm hk
      simp only [this]
      rw [List.mem_cons] at hm
      rcases hm with h1 | hm
      · exact absurd (Prod.mk.inj h1).1.symm hk
      · exact ih hn.2 hm

theorem mapM_range' {β : Type} (F : Nat → Except Refusal β) : ∀ (xs : List β) (s : Nat),
    (∀ i (hi : i < xs.length), F (s + i) = .ok xs[i]) → (List.range' s xs.length).mapM F = .ok xs
  | [], s, _ => by simp [pure, Except.pure]
  | x :: xs, s, h => by
    have h0 := h 0 (by simp)
    have h2 := mapM_range' F xs (s + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    simp only [List.length_cons, List.range'_succ, List.mapM_cons]
    simp [h2, bind, Except.bind, pure, Except.pure] at h0 ⊢
    simp [h0, h2]


/-- The members of an index object over the values `xs`, from index `s`. -/
def idxPairs (s : Nat) (xs : List J) : List (String × J) :=
  ((List.range' s xs.length).zip xs).map fun (a, x) => (Nat.repr a, x)

theorem idxPairs_keys (s : Nat) (xs : List J) : (idxPairs s xs).map (·.1) = (List.range' s xs.length).map Nat.repr := by
  induction xs generalizing s with
  | nil => simp [idxPairs]
  | cons x xs ih =>
    have := ih (s + 1)
    simp only [idxPairs, List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons] at this ⊢
    rw [this]

theorem idxPairs_lookup (xs : List J) : ∀ (s i : Nat) (hi : i < xs.length), (idxPairs s xs).lookup (Nat.repr (s + i)) = some xs[i] := by
  induction xs with
  | nil => intro s i hi; simp at hi
  | cons x xs ih =>
    intro s i hi
    cases i with
    | zero => simp [idxPairs, List.range'_succ]
    | succ i =>
      have h1 := ih (s + 1) i (by simpa using hi)
      have hne : (Nat.repr (s + (i + 1)) == Nat.repr s) = false := by
        simp
      simp only [idxPairs, List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.lookup_cons, hne] at h1 ⊢
      have e : s + (i + 1) = s + 1 + i := by omega
      rw [e]; simpa using h1

theorem idxPairs_nodup (s : Nat) (xs : List J) : ((idxPairs s xs).map (·.1)).Nodup := by
  rw [idxPairs_keys]
  exact List.Pairwise.map _ (fun a b h hh => h (Nat.repr_injective hh)) List.nodup_range'


theorem probOf_toJ (path : String) (p : Prob) : probOf path p.toJ = .ok p := by
  unfold probOf Prob.toJ; simp [ofDecimal_toDecimal]

theorem posOf_roundtrip (path : String) (x : Nat) : posOf path (.num ⟨false, x, -6⟩) = .ok x := by
  unfold posOf
  by_cases h : x = 0
  · subst h; simp [Decimal.toScaled]
  · simp [Decimal.toScaled, h, Decimal.maxExponent]

theorem mapM_unit {α : Type} (f : α → Except Refusal Unit) : ∀ xs : List α, (∀ x ∈ xs, f x = .ok ()) → xs.mapM f = .ok (xs.map fun _ => ())
  := fun xs h => by simpa using mapM_ok f id (fun _ => ()) xs (by simpa using h)

theorem indexed_roundtrip {α : Type} (path : String) (f : String → J → Except Refusal α) (enc : α → J)
    (hf : ∀ p x, f p (enc x) = .ok x) (xs : List α) :
    indexed path xs.length f (indexedJ (xs.map enc)) = .ok xs := by
  have hj : indexedJ (xs.map enc) = .obj (idxPairs 0 (xs.map enc)) := by
    simp [indexedJ, idxPairs, List.range_eq_range']
  rw [hj]
  have hn := idxPairs_nodup 0 (xs.map enc)
  have ho : objOf path none (.obj (idxPairs 0 (xs.map enc))) = .ok (idxPairs 0 (xs.map enc)) :=
    objOf_ok' path none _ hn (by simp)
  have hk : ∀ k ∈ (idxPairs 0 (xs.map enc)).map (·.1), k ∈ (List.range xs.length).map Nat.repr := by
    intro k hk
    rw [idxPairs_keys] at hk
    simpa [List.range_eq_range'] using hk
  unfold indexed
  rw [ho]
  simp only [bind, Except.bind]
  have hu := mapM_unit (fun (x : String × J) => match x with
      | (k, _) => if k ∈ (List.range xs.length).map Nat.repr then (pure () : Except Refusal Unit)
        else refuse (if canonIdx k then .unknownOption else .badIndexKey) (pathKey path k)) (idxPairs 0 (xs.map enc))
    (fun x hx => by
      rcases x with ⟨k, v⟩
      have := hk k (List.mem_map_of_mem (f := (·.1)) hx)
      simp [this, pure, Except.pure])
  rw [hu]
  simp only []
  have hl := mapM_range' (fun i : Nat => match (idxPairs 0 (xs.map enc)).lookup (Nat.repr i) with
      | some v => f (pathKey path (Nat.repr i)) v
      | none => refuse RefusalCode.missingOption (pathKey path (Nat.repr i))) xs 0 (fun i hi => by
    have := idxPairs_lookup (xs.map enc) 0 i (by simpa using hi)
    simp only [Nat.zero_add] at this ⊢
    simp [this, hf])
  rw [List.range_eq_range']
  exact hl


theorem strOf_str (path s : String) : strOf path (.str s) = .ok s := rfl


theorem lk_type (a b c : J) : [("type", a), ("instructions", b), ("criteria", c)].lookup "type" = some a := by rfl
theorem lk_instr (a b c : J) : [("type", a), ("instructions", b), ("criteria", c)].lookup "instructions" = some b := by rfl
theorem lk_crit (a b c : J) : [("type", a), ("instructions", b), ("criteria", c)].lookup "criteria" = some c := by rfl

/-- The wire form of an option's description. -/
def descJ (d : Option String) : J := match d with | none => J.null | some s => J.str s

theorem optStr_enc (path : String) (d : Option String) :
    optStr path (descJ d) = .ok d := by
  cases d <;> rfl

theorem zip_range_mapM (cp : String) (ls : List String) :
    ((List.range ls.length).zip (ls.map J.str)).mapM (fun (nx : Nat × J) => strOf (pathKey cp (Nat.repr nx.1)) nx.2) = .ok ls := by
  have h : (List.range ls.length).zip (ls.map J.str) = ((List.range ls.length).zip ls).map (fun (a, b) => (a, J.str b)) := by
    rw [List.zip_map_right]; rfl
  rw [h]
  have := mapM_ok (fun (nx : Nat × J) => strOf (pathKey cp (Nat.repr nx.1)) nx.2) (fun (a, b) => (a, J.str b)) (fun ab => ab.2)
    ((List.range ls.length).zip ls) (fun x hx => by rfl)
  rw [this, List.map_snd_zip (by simp)]

theorem question_roundtrip (path : String) (q : Question) (h : q.Valid) :
    Question.decodeAt path q.encode = .ok q := by
  cases q with
  | noul i c => cases c with
    | none => rfl
    | some tf => rcases tf with ⟨t, f⟩; rfl
  | box i => rfl
  | score i ls =>
    have hc : (Question.score i ls).check = .ok () := (question_check_ok_iff _).2 h
    have hk : (["type", "instructions", "criteria"] : List String).Nodup := by decide
    have ho : objOf path none (Question.encode (.score i ls)) = .ok [("type", .str "score"), ("instructions", .str i), ("criteria", .arr (ls.map .str))] :=
      objOf_ok' path none _ hk (by simp)
    have hr : rawQuestion path .score [("type", .str "score"), ("instructions", .str i), ("criteria", .arr (ls.map .str))] = .ok (.score i ls) := by
      unfold rawQuestion
      simp only [strField, field, lk_type, lk_instr, lk_crit, bind, Except.bind, strOf_str]
      simp [List.length_map, zip_range_mapM, pure, Except.pure, bind, Except.bind]
    have hu : unknownCheck path (qKeys .score) [("type", J.str "score"), ("instructions", .str i), ("criteria", .arr (ls.map .str))] = .ok () :=
      unknownCheck_ok _ _ _ (by simp [qKeys])
    unfold Question.decodeAt
    rw [ho]
    simp only [bind, Except.bind]
    simp [tagOf, hu, hr, hc]
    rfl
  | choice i os =>
    have hc : (Question.choice i os).check = .ok () := (question_check_ok_iff _).2 h
    have hnd : (os.map (·.1)).Nodup := h.2.2.2
    have hkeys : ((os.map fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s)).map (·.1)).Nodup := by
      simpa [List.map_map, Function.comp_def] using hnd
    have hk : (["type", "instructions", "criteria"] : List String).Nodup := by decide
    have hE : Question.encode (.choice i os) = .obj [("type", .str "choice"), ("instructions", .str i), ("criteria", .obj (os.map fun (kd : String × Option String) => (kd.1, descJ kd.2)))] := rfl
    have ho : objOf path none (Question.encode (.choice i os)) = .ok [("type", .str "choice"), ("instructions", .str i),
        ("criteria", .obj (os.map fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s)))] :=
      by rw [hE]; exact objOf_ok' path none _ hk (by simp)
    have hcr : objOf (pathKey path "criteria") none (.obj (os.map fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s))) =
        .ok (os.map fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s)) :=
      objOf_ok' _ none _ hkeys (by simp)
    have hm0 := mapM_ok (fun (kv : String × J) => (match optStr (pathKey (pathKey path "criteria") kv.1) kv.2 with
        | Except.error err => Except.error err
        | Except.ok v => pure (kv.1, v) : Except Refusal (String × Option String)))
      (fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s)) (fun kd => kd) os
      (fun kd _ => by
        rcases kd with ⟨k, d⟩
        cases d <;> rfl)
    have hm : List.mapM (fun (kv : String × J) => (match optStr (pathKey (pathKey path "criteria") kv.1) kv.2 with
        | Except.error err => Except.error err
        | Except.ok v => pure (kv.1, v) : Except Refusal (String × Option String)))
        (os.map fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s)) = .ok os := by
      rw [hm0]; simp
    have hr : rawQuestion path .choice [("type", .str "choice"), ("instructions", .str i),
        ("criteria", .obj (os.map fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s)))] = .ok (.choice i os) := by
      unfold rawQuestion
      simp only [strField, field, lk_type, lk_instr, lk_crit, bind, Except.bind, strOf_str, hcr]
      rw [mapM_ok _ _ (fun kd => kd) os (fun kd _ => by rcases kd with ⟨k, d⟩; cases d <;> rfl)]
      simp only [List.map_id']
      rfl
    have hu : unknownCheck path (qKeys .choice) [("type", J.str "choice"), ("instructions", .str i),
        ("criteria", .obj (os.map fun (kd : String × Option String) => (kd.1, match kd.2 with | none => J.null | some s => J.str s)))] = .ok () :=
      unknownCheck_ok _ _ _ (by simp [qKeys])
    unfold Question.decodeAt
    rw [hE] at ho ⊢
    rw [ho]
    simp only [bind, Except.bind]
    simp [tagOf, hu, hr, hc]
    rfl

theorem decodeAt_of_raw (path : String) (q : Question) (a : Answer) (kvs : List (String × J))
    (hn : (kvs.map (·.1)).Nodup) (hs : ∀ k ∈ kvs.map (·.1), k ∈ aKeys q.kindOf)
    (ht : tagOf path kvs = .ok q.kindOf) (hr : rawAnswer path q q.kindOf kvs = .ok a) (hw : WellFormed q a) :
    Answer.decodeAt path q (.obj kvs) = .ok a := by
  have ho := objOf_ok' path none kvs hn (by simp)
  have hc := (checkAnswer_ok_iff q a).2 hw
  unfold Answer.decodeAt
  rw [ho]
  simp only [bind, Except.bind, ht, ite_true, unknownCheck_ok path _ kvs hs, hr, checkedAt, hc]

theorem tagOf_noul (path : String) (r : List (String × J)) : tagOf path (("type", .str "noul") :: r) = .ok .noul := by
  simp [tagOf]
theorem tagOf_choice (path : String) (r : List (String × J)) : tagOf path (("type", .str "choice") :: r) = .ok .choice := by
  simp [tagOf]
theorem tagOf_score (path : String) (r : List (String × J)) : tagOf path (("type", .str "score") :: r) = .ok .score := by
  simp [tagOf]
theorem tagOf_box (path : String) (r : List (String × J)) : tagOf path (("type", .str "box") :: r) = .ok .box := by
  simp [tagOf]


theorem lk4 (a b c d : J) : ([("top", a), ("bottom", b), ("left", c), ("right", d)] : List (String × J)).lookup "top" = some a ∧
   ([("top", a), ("bottom", b), ("left", c), ("right", d)] : List (String × J)).lookup "bottom" = some b ∧
   ([("top", a), ("bottom", b), ("left", c), ("right", d)] : List (String × J)).lookup "left" = some c ∧
   ([("top", a), ("bottom", b), ("left", c), ("right", d)] : List (String × J)).lookup "right" = some d := ⟨rfl, rfl, rfl, rfl⟩

theorem answer_noul_roundtrip (path i : String) (c : Option (String × String)) (p : Prob) :
    Answer.decodeAt path (.noul i c) (Answer.encode (.noul p)) = .ok (.noul p) := by
  have hw : WellFormed (.noul i c) (.noul p) := trivial
  have hn : ([("type", J.str "noul"), ("noul", p.toJ)].map (·.1)).Nodup := by
    show (["type", "noul"] : List String).Nodup
    decide
  have hs : ∀ k ∈ [("type", J.str "noul"), ("noul", p.toJ)].map (·.1), k ∈ aKeys (Question.noul i c).kindOf := by
    intro k hk
    have hk' : k ∈ (["type", "noul"] : List String) := hk
    have : aKeys (Question.noul i c).kindOf = ["type", "noul"] := rfl
    rw [this]; exact hk'
  have l1 : List.lookup "noul" [("type", J.str "noul"), ("noul", p.toJ)] = some p.toJ := rfl
  have hr : rawAnswer path (.noul i c) .noul [("type", J.str "noul"), ("noul", p.toJ)] = .ok (.noul p) := by
    unfold rawAnswer
    simp only [probField, field, bind, Except.bind, l1, probOf_toJ]
    rfl
  exact decodeAt_of_raw path (.noul i c) _ _ hn hs (tagOf_noul _ _) hr hw


theorem answer_box_roundtrip (path i : String) (b : Box) (c : Prob) (hw : WellFormed (.box i) (.box b c)) :
    Answer.decodeAt path (.box i) (Answer.encode (.box b c)) = .ok (.box b c) := by
  have hn : ([("type", J.str "box"), ("box", J.obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]), ("confidence", c.toJ)].map (·.1)).Nodup := by
    show (["type", "box", "confidence"] : List String).Nodup
    decide
  have hs : ∀ k ∈ [("type", J.str "box"), ("box", J.obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]), ("confidence", c.toJ)].map (·.1), k ∈ aKeys (Question.box i).kindOf := by
    intro k hk
    have hk' : k ∈ (["type", "box", "confidence"] : List String) := hk
    have : aKeys (Question.box i).kindOf = ["type", "box", "confidence"] := rfl
    rw [this]; exact hk'
  have l1 : List.lookup "box" [("type", J.str "box"), ("box", J.obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]), ("confidence", c.toJ)] = some (J.obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]) := rfl
  have l2 : List.lookup "confidence" [("type", J.str "box"), ("box", J.obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]), ("confidence", c.toJ)] = some c.toJ := rfl
  have hb : objOf (pathKey path "box") (some ["top", "bottom", "left", "right"]) (J.obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]) =
      .ok [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)] :=
    objOf_ok' _ _ _ (by show (["top", "bottom", "left", "right"] : List String).Nodup; decide) (by
      intro a ha k hk
      have : a = ["top", "bottom", "left", "right"] := (Option.some.inj ha).symm
      subst this
      exact hk)
  have hr : rawAnswer path (.box i) .box [("type", J.str "box"), ("box", J.obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]), ("confidence", c.toJ)] = .ok (.box b c) := by
    unfold rawAnswer
    simp only [probField, field, bind, Except.bind, l1, l2, hb, probOf_toJ]
    obtain ⟨m1, m2, m3, m4⟩ := lk4 b.top.toJ b.bottom.toJ b.left.toJ b.right.toJ
    simp only [m1, m2, m3, m4, probOf_toJ]
    rcases b with ⟨t, bo, l, r⟩
    rfl
  exact decodeAt_of_raw path (.box i) _ _ hn hs (tagOf_box _ _) hr hw

theorem lkc1 (a b c d : J) : ([("type", a), ("choice", b), ("probabilities", c), ("confidence", d)] : List (String × J)).lookup "choice" = some b := rfl
theorem lkc2 (a b c d : J) : ([("type", a), ("choice", b), ("probabilities", c), ("confidence", d)] : List (String × J)).lookup "probabilities" = some c := rfl
theorem lkc3 (a b c d : J) : ([("type", a), ("choice", b), ("probabilities", c), ("confidence", d)] : List (String × J)).lookup "confidence" = some d := rfl

theorem answer_choice_roundtrip (path i : String) (os : List (String × Option String)) (s : String) (ps : List (String × Prob)) (c : Prob)
    (hw : WellFormed (.choice i os) (.choice s ps c)) :
    Answer.decodeAt path (.choice i os) (Answer.encode (.choice s ps c)) = .ok (.choice s ps c) := by
  have hnd : (ps.map (·.1)).Nodup := hw.1
  have hkeys : ((ps.map fun (kp : String × Prob) => (kp.1, kp.2.toJ)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hnd
  have hn : ([("type", J.str "choice"), ("choice", J.str s), ("probabilities", J.obj (ps.map fun (kp : String × Prob) => (kp.1, kp.2.toJ))), ("confidence", c.toJ)].map (·.1)).Nodup := by
    show (["type", "choice", "probabilities", "confidence"] : List String).Nodup
    decide
  have hs : ∀ k ∈ [("type", J.str "choice"), ("choice", J.str s), ("probabilities", J.obj (ps.map fun (kp : String × Prob) => (kp.1, kp.2.toJ))), ("confidence", c.toJ)].map (·.1), k ∈ aKeys (Question.choice i os).kindOf := by
    intro k hk
    have hk' : k ∈ (["type", "choice", "probabilities", "confidence"] : List String) := hk
    have : aKeys (Question.choice i os).kindOf = ["type", "choice", "probabilities", "confidence"] := rfl
    rw [this]; exact hk'
  have hE : Answer.encode (.choice s ps c) = .obj [("type", J.str "choice"), ("choice", J.str s), ("probabilities", J.obj (ps.map fun (kp : String × Prob) => (kp.1, kp.2.toJ))), ("confidence", c.toJ)] := rfl
  have hp : objOf (pathKey path "probabilities") none (J.obj (ps.map fun (kp : String × Prob) => (kp.1, kp.2.toJ))) = .ok (ps.map fun (kp : String × Prob) => (kp.1, kp.2.toJ)) :=
    objOf_ok' _ _ _ hkeys (by simp)
  have hm := mapM_ok (fun (kv : String × J) => (match probOf (pathKey (pathKey path "probabilities") kv.1) kv.2 with
        | Except.error err => Except.error err
        | Except.ok v => pure (kv.1, v) : Except Refusal (String × Prob)))
      (fun (kp : String × Prob) => (kp.1, kp.2.toJ)) (fun kp => kp) ps
      (fun kp _ => by
        rcases kp with ⟨k, p⟩
        simp [probOf_toJ, pure, Except.pure])
  have hr : rawAnswer path (.choice i os) .choice [("type", J.str "choice"), ("choice", J.str s), ("probabilities", J.obj (ps.map fun (kp : String × Prob) => (kp.1, kp.2.toJ))), ("confidence", c.toJ)] = .ok (.choice s ps c) := by
    unfold rawAnswer
    simp only [strField, probField, field, bind, Except.bind, lkc1, lkc2, lkc3, strOf_str, hp, probOf_toJ]
    rw [mapM_ok _ _ (fun kp => kp) ps (fun kp _ => by rcases kp with ⟨k, p⟩; simp [probOf_toJ, pure, Except.pure])]
    simp only [List.map_id']
    rfl
  rw [hE]
  exact decodeAt_of_raw path (.choice i os) _ _ hn hs (tagOf_choice _ _) hr hw

theorem lks1 (a b c d e : J) : ([("type", a), ("score", b), ("confidence", c), ("probabilities", d), ("legend", e)] : List (String × J)).lookup "score" = some b := rfl
theorem lks2 (a b c d e : J) : ([("type", a), ("score", b), ("confidence", c), ("probabilities", d), ("legend", e)] : List (String × J)).lookup "confidence" = some c := rfl
theorem lks3 (a b c d e : J) : ([("type", a), ("score", b), ("confidence", c), ("probabilities", d), ("legend", e)] : List (String × J)).lookup "probabilities" = some d := rfl
theorem lks4 (a b c d e : J) : ([("type", a), ("score", b), ("confidence", c), ("probabilities", d), ("legend", e)] : List (String × J)).lookup "legend" = some e := rfl

theorem answer_score_roundtrip (path i : String) (ls : List String) (x : Pos) (c : Prob) (ps : List Prob) (lg : List String)
    (hw : WellFormed (.score i ls) (.score x c ps lg)) :
    Answer.decodeAt path (.score i ls) (Answer.encode (.score x c ps lg)) = .ok (.score x c ps lg) := by
  have hpl : ps.length = ls.length := hw.1
  have hlg : lg = ls := hw.2.2.1
  have hn : ([("type", J.str "score"), ("score", J.num ⟨false, x, -6⟩), ("confidence", c.toJ), ("probabilities", indexedJ (ps.map Prob.toJ)), ("legend", indexedJ (lg.map J.str))].map (·.1)).Nodup := by
    show (["type", "score", "confidence", "probabilities", "legend"] : List String).Nodup
    decide
  have hs : ∀ k ∈ [("type", J.str "score"), ("score", J.num ⟨false, x, -6⟩), ("confidence", c.toJ), ("probabilities", indexedJ (ps.map Prob.toJ)), ("legend", indexedJ (lg.map J.str))].map (·.1), k ∈ aKeys (Question.score i ls).kindOf := by
    intro k hk
    have hk' : k ∈ (["type", "score", "confidence", "probabilities", "legend"] : List String) := hk
    have : aKeys (Question.score i ls).kindOf = ["type", "score", "confidence", "probabilities", "legend"] := rfl
    rw [this]; exact hk'
  have hE : Answer.encode (.score x c ps lg) = .obj [("type", J.str "score"), ("score", J.num ⟨false, x, -6⟩), ("confidence", c.toJ), ("probabilities", indexedJ (ps.map Prob.toJ)), ("legend", indexedJ (lg.map J.str))] := rfl
  have h1 : indexed (pathKey path "probabilities") ls.length probOf (indexedJ (ps.map Prob.toJ)) = .ok ps := by
    have := indexed_roundtrip (pathKey path "probabilities") (fun p => probOf p) Prob.toJ (fun p x => probOf_toJ p x) ps
    rw [hpl] at this
    exact this
  have h2 : indexed (pathKey path "legend") ls.length (fun p => strOf p) (indexedJ (lg.map J.str)) = .ok lg := by
    have := indexed_roundtrip (pathKey path "legend") (fun p => strOf p) J.str (fun p x => strOf_str p x) lg
    rw [hlg] at this ⊢
    exact this
  have hr : rawAnswer path (.score i ls) .score [("type", J.str "score"), ("score", J.num ⟨false, x, -6⟩), ("confidence", c.toJ), ("probabilities", indexedJ (ps.map Prob.toJ)), ("legend", indexedJ (lg.map J.str))] = .ok (.score x c ps lg) := by
    unfold rawAnswer
    simp only [strField, probField, field, bind, Except.bind, lks1, lks2, lks3, lks4, posOf_roundtrip, probOf_toJ]
    rw [h1, h2]
    rfl
  rw [hE]
  exact decodeAt_of_raw path (.score i ls) _ _ hn hs (tagOf_score _ _) hr hw

/-! ## The depth of what the encoders write -/

theorem depthKvs_le (n : Nat) : ∀ kvs : List (String × J), (∀ kv ∈ kvs, J.depth kv.2 ≤ n) → J.depthKvs kvs ≤ n
  | [], _ => by simp [J.depthKvs]
  | kv :: kvs, h => by
    have h1 := h kv (by simp)
    have h2 := depthKvs_le n kvs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [J.depthKvs, J.depthPair]
    rcases kv with ⟨k, v⟩
    have e : J.depthPair (k, v) = J.depth v := rfl
    have h1' : J.depthPair (k, v) ≤ n := h1
    omega

theorem depthList_le (n : Nat) : ∀ xs : List J, (∀ x ∈ xs, J.depth x ≤ n) → J.depthList xs ≤ n
  | [], _ => by simp [J.depthList]
  | x :: xs, h => by
    have h1 := h x (by simp)
    have h2 := depthList_le n xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [J.depthList]
    omega

theorem depth_obj_le (n : Nat) (kvs : List (String × J)) (h : ∀ kv ∈ kvs, J.depth kv.2 ≤ n) : J.depth (.obj kvs) ≤ n + 1 := by
  have := depthKvs_le n kvs h
  simp only [J.depth]; omega

theorem depth_arr_le (n : Nat) (xs : List J) (h : ∀ x ∈ xs, J.depth x ≤ n) : J.depth (.arr xs) ≤ n + 1 := by
  have := depthList_le n xs h
  simp only [J.depth]; omega

theorem depth_scalar (d : Decimal) : J.depth (.num d) = 0 := rfl
theorem depth_str (s : String) : J.depth (.str s) = 0 := rfl

theorem prob_depth (p : Prob) : J.depth p.toJ = 0 := rfl

theorem indexedJ_depth (xs : List J) (h : ∀ x ∈ xs, J.depth x = 0) : J.depth (indexedJ xs) ≤ 1 := by
  unfold indexedJ
  apply depth_obj_le 0
  intro kv hkv
  simp only [List.mem_map] at hkv
  obtain ⟨⟨i, x⟩, hx, rfl⟩ := hkv
  have := (List.of_mem_zip hx).2
  have := h x this
  simp [this]

theorem question_depth (q : Question) : J.depth q.encode ≤ 2 := by
  cases q with
  | noul i c =>
    cases c with
    | none => apply depth_obj_le 1; simp [Question.encode, J.depth]
    | some tf =>
      apply depth_obj_le 1
      intro kv hkv
      simp only [Question.encode, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hkv
      rcases hkv with h | h
      · rcases h with rfl | rfl <;> simp [J.depth]
      · subst h; apply depth_obj_le 0; intro kv hkv; simp at hkv; rcases hkv with rfl | rfl <;> simp [J.depth]
  | box i => apply depth_obj_le 1; simp [Question.encode, J.depth]
  | score i ls =>
    apply depth_obj_le 1
    intro kv hkv
    simp only [Question.encode, List.mem_cons, List.mem_nil_iff, or_false] at hkv
    rcases hkv with rfl | rfl | rfl
    · simp [J.depth]
    · simp [J.depth]
    · apply depth_arr_le 0; intro x hx; simp at hx; obtain ⟨s, _, rfl⟩ := hx; simp [J.depth]
  | choice i os =>
    apply depth_obj_le 1
    intro kv hkv
    simp only [Question.encode, List.mem_cons, List.mem_nil_iff, or_false] at hkv
    rcases hkv with rfl | rfl | rfl
    · simp [J.depth]
    · simp [J.depth]
    · apply depth_obj_le 0; intro kv hkv; simp at hkv; obtain ⟨k, d, _, rfl⟩ := hkv; cases d <;> simp [J.depth]

theorem answer_depth (a : Answer) : J.depth a.encode ≤ 2 := by
  cases a with
  | noul p => apply depth_obj_le 1; simp [Answer.encode, J.depth, Prob.toJ]
  | choice s ps c =>
    apply depth_obj_le 1
    intro kv hkv
    simp only [Answer.encode, List.mem_cons, List.mem_nil_iff, or_false] at hkv
    rcases hkv with rfl | rfl | rfl | rfl
    · simp [J.depth]
    · simp [J.depth]
    · apply depth_obj_le 0; intro kv hkv; simp at hkv; obtain ⟨k, p, _, rfl⟩ := hkv; simp [J.depth, Prob.toJ]
    · simp [J.depth, Prob.toJ]
  | score x c ps lg =>
    apply depth_obj_le 1
    intro kv hkv
    simp only [Answer.encode, List.mem_cons, List.mem_nil_iff, or_false] at hkv
    rcases hkv with rfl | rfl | rfl | rfl | rfl
    · simp [J.depth]
    · simp [J.depth]
    · simp [J.depth, Prob.toJ]
    · have := indexedJ_depth (ps.map Prob.toJ) (by intro x hx; simp at hx; obtain ⟨p, _, rfl⟩ := hx; rfl)
      simp only []; omega
    · have := indexedJ_depth (lg.map J.str) (by intro x hx; simp at hx; obtain ⟨p, _, rfl⟩ := hx; rfl)
      simp only []; omega
  | box b c =>
    apply depth_obj_le 1
    intro kv hkv
    simp only [Answer.encode, List.mem_cons, List.mem_nil_iff, or_false] at hkv
    rcases hkv with rfl | rfl | rfl
    · simp [J.depth]
    · apply depth_obj_le 0; intro kv hkv; simp at hkv; rcases hkv with rfl | rfl | rfl | rfl <;> simp [J.depth, Prob.toJ]
    · simp [J.depth, Prob.toJ]

theorem rq1 (a b c : J) : ([("model", a), ("state", b), ("questions", c)] : List (String × J)).lookup "model" = some a := rfl
theorem rq2 (a b c : J) : ([("model", a), ("state", b), ("questions", c)] : List (String × J)).lookup "state" = some b := rfl
theorem rq3 (a b c : J) : ([("model", a), ("state", b), ("questions", c)] : List (String × J)).lookup "questions" = some c := rfl

/-! ## The request -/

theorem allOk_ok_iff {α : Type} (f : α → Except Refusal Unit) : ∀ xs : List α, allOk f xs = .ok () ↔ ∀ x ∈ xs, f x = .ok ()
  | [] => by simp [allOk]
  | x :: xs => by
    have ih := allOk_ok_iff f xs
    unfold allOk
    cases hx : f x with
    | error e => simp [hx]
    | ok u => cases u; simp [hx, ih]

theorem mapError_ok_iff (c : Except Refusal Unit) (g : Refusal → Refusal) : c.mapError g = .ok () ↔ c = .ok () := by
  cases c <;> simp [Except.mapError]

/-- `Request.check` succeeds iff the request is valid. -/
theorem request_check_ok_iff (r : Request) : r.check = .ok () ↔ r.Valid := by
  simp [Request.check, Request.Valid, guardWith_ok, allOk_ok_iff, mapError_ok_iff, question_check_ok_iff, and_assoc]

theorem request_encode_eq (r : Request) (h : r.Valid) :
    r.encode = .ok (.obj [("model", .str r.model), ("state", r.state),
      ("questions", .obj (r.questions.map fun nq => (nq.1, nq.2.encode)))]) := by
  unfold Request.encode
  rw [(request_check_ok_iff r).2 h]

theorem request_encode_depth (r : Request) (h : r.Valid) (j : J) (hj : r.encode = .ok j) : J.depth j ≤ maxNestingDepth := by
  rw [request_encode_eq r h] at hj
  cases hj
  have hs : J.depth r.state ≤ 31 := by have := h.2.2.2.1; unfold maxNestingDepth at this; omega
  apply Nat.le_trans (depth_obj_le 31 _ _) (by decide)
  intro kv hkv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl | rfl
  · simp [J.depth]
  · exact hs
  · have := depth_obj_le 2 (r.questions.map fun nq => (nq.1, nq.2.encode)) (by
      intro kv hkv; simp at hkv; obtain ⟨n, q, _, rfl⟩ := hkv; exact question_depth q)
    simp only []; omega

/-- W3 for requests: a valid request decodes back from its encoding. -/
theorem request_roundtrip (r : Request) (h : r.Valid) : ∃ j, r.encode = .ok j ∧ Request.decode j = .ok r := by
  have he := request_encode_eq r h
  refine ⟨_, he, ?_⟩
  have hd := request_encode_depth r h _ he
  unfold Request.decode
  simp only [hd, ite_true]
  unfold Request.decodeAt
  have hnames : (r.questions.map (·.1)).Nodup := h.2.2.2.2.2.2.2.1
  have hqk : ((r.questions.map fun nq => (nq.1, nq.2.encode)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hnames
  have hk : (["model", "state", "questions"] : List String).Nodup := by decide
  have ho : objOf "" (some ["model", "state", "questions"]) (.obj [("model", .str r.model), ("state", r.state),
      ("questions", .obj (r.questions.map fun nq => (nq.1, nq.2.encode)))]) = .ok [("model", .str r.model), ("state", r.state),
      ("questions", .obj (r.questions.map fun nq => (nq.1, nq.2.encode)))] :=
    objOf_ok' _ _ _ hk (by
      intro a ha k hk
      have : a = ["model", "state", "questions"] := (Option.some.inj ha).symm
      subst this
      exact hk)
  have hq : objOf "questions" none (.obj (r.questions.map fun nq => (nq.1, nq.2.encode))) = .ok (r.questions.map fun nq => (nq.1, nq.2.encode)) :=
    objOf_ok' _ _ _ hqk (by simp)
  have hv : ∀ nq ∈ r.questions, nq.2.Valid := h.2.2.2.2.2.2.2.2
  have hc := (request_check_ok_iff r).2 h
  rcases r with ⟨m, st, qs⟩
  simp only [] at hc hv ⊢
  simp only [strField, field, bind, Except.bind, rq1, rq2, rq3, strOf_str, ho, hq]
  rw [mapM_ok readQuestion (fun nq => (nq.1, nq.2.encode)) (fun nq => nq) qs (by
    intro nq hnq
    rcases nq with ⟨n, q⟩
    simp [readQuestion, question_roundtrip _ q (hv (n, q) hnq), pure, Except.pure, bind, Except.bind])]
  simp only [List.map_id']
  simp only [hc]
  rfl

/-! ## The response -/

theorem answer_roundtrip (path : String) (q : Question) (a : Answer) (h : WellFormed q a) :
    Answer.decodeAt path q a.encode = .ok a := by
  cases q <;> cases a <;> first
    | exact False.elim h
    | exact answer_noul_roundtrip _ _ _ _
    | exact answer_choice_roundtrip _ _ _ _ _ _ h
    | exact answer_score_roundtrip _ _ _ _ _ _ _ h
    | exact answer_box_roundtrip _ _ _ _ h

theorem natOf_natJ (path : String) (n : Nat) : natOf path (natJ n) = .ok n := by
  unfold natOf natJ
  by_cases h : n = 0
  · subst h; simp [Decimal.toScaled, scale]
  · have e : n * 10 ^ ((0 : Int) + 6).toNat = n * scale := by simp [scale]
    simp only [Decimal.toScaled, h, Decimal.maxExponent, e]
    simp [Nat.mul_mod_left, Nat.mul_div_cancel _ (show 0 < scale by decide)]

theorem costOf_ok (path : String) (d : Decimal) (h1 : ¬ (d.neg = true ∧ d.mantissa ≠ 0)) (h2 : d.exp.natAbs ≤ Decimal.maxExponent) :
    costOf path (.num d) = .ok d := by
  unfold costOf
  have : ¬ Decimal.maxExponent < d.exp.natAbs := by omega
  simp [h1, this]

theorem response_encode_depth (r : Response) : J.depth r.encode ≤ maxNestingDepth := by
  unfold Response.encode
  apply Nat.le_trans (depth_obj_le 3 _ _) (by decide)
  intro kv hkv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl | rfl | rfl | rfl
  · simp [J.depth]
  · simp [J.depth]
  · simp [J.depth]
  · have := depth_obj_le 2 (r.answers.map fun na => (na.1, na.2.encode)) (by
      intro kv hkv; simp at hkv; obtain ⟨n, a, _, rfl⟩ := hkv; exact answer_depth a)
    simp only []; omega
  · have := depth_obj_le 0 [("input_tokens", natJ r.usage.inputTokens), ("output_tokens", natJ r.usage.outputTokens), ("cost", .num r.usage.cost)]
      (by intro kv hkv; simp at hkv; rcases hkv with rfl | rfl | rfl <;> simp [J.depth, natJ])
    simp only []; omega

theorem rs1 (a b c d e : J) : ([("id", a), ("model", b), ("provider", c), ("answers", d), ("usage", e)] : List (String × J)).lookup "id" = some a := rfl
theorem rs2 (a b c d e : J) : ([("id", a), ("model", b), ("provider", c), ("answers", d), ("usage", e)] : List (String × J)).lookup "model" = some b := rfl
theorem rs3 (a b c d e : J) : ([("id", a), ("model", b), ("provider", c), ("answers", d), ("usage", e)] : List (String × J)).lookup "provider" = some c := rfl
theorem rs4 (a b c d e : J) : ([("id", a), ("model", b), ("provider", c), ("answers", d), ("usage", e)] : List (String × J)).lookup "answers" = some d := rfl
theorem rs5 (a b c d e : J) : ([("id", a), ("model", b), ("provider", c), ("answers", d), ("usage", e)] : List (String × J)).lookup "usage" = some e := rfl
theorem us1 (a b c : J) : ([("input_tokens", a), ("output_tokens", b), ("cost", c)] : List (String × J)).lookup "input_tokens" = some a := rfl
theorem us2 (a b c : J) : ([("input_tokens", a), ("output_tokens", b), ("cost", c)] : List (String × J)).lookup "output_tokens" = some b := rfl
theorem us3 (a b c : J) : ([("input_tokens", a), ("output_tokens", b), ("cost", c)] : List (String × J)).lookup "cost" = some c := rfl

/-- W3 for responses: a response valid for the question set decodes back from its encoding. -/
theorem response_roundtrip (qs : List (String × Question)) (r : Response) (h : r.Valid qs) :
    Response.decode qs r.encode = .ok r := by
  obtain ⟨hnd, hfit, hall, hc1, hc2⟩ := h
  unfold Response.decode
  simp only [response_encode_depth r, ite_true]
  unfold Response.decodeAt
  have hk : (["id", "model", "provider", "answers", "usage"] : List String).Nodup := by decide
  have ho : objOf "" (some ["id", "model", "provider", "answers", "usage"]) r.encode = .ok [("id", .str r.id), ("model", .str r.model), ("provider", .str r.provider),
      ("answers", .obj (r.answers.map fun na => (na.1, na.2.encode))),
      ("usage", .obj [("input_tokens", natJ r.usage.inputTokens), ("output_tokens", natJ r.usage.outputTokens), ("cost", .num r.usage.cost)])] :=
    objOf_ok' _ _ _ hk (by
      intro a ha k hk
      have : a = ["id", "model", "provider", "answers", "usage"] := (Option.some.inj ha).symm
      subst this
      exact hk)
  have hqk : ((r.answers.map fun na => (na.1, na.2.encode)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hnd
  have hq : objOf "answers" none (.obj (r.answers.map fun na => (na.1, na.2.encode))) = .ok (r.answers.map fun na => (na.1, na.2.encode)) :=
    objOf_ok' _ _ _ hqk (by simp)
  have hu : objOf "usage" (some ["input_tokens", "output_tokens", "cost"]) (.obj [("input_tokens", natJ r.usage.inputTokens), ("output_tokens", natJ r.usage.outputTokens), ("cost", .num r.usage.cost)]) =
      .ok [("input_tokens", natJ r.usage.inputTokens), ("output_tokens", natJ r.usage.outputTokens), ("cost", .num r.usage.cost)] :=
    objOf_ok' _ _ _ (by show (["input_tokens", "output_tokens", "cost"] : List String).Nodup; decide) (by
      intro a ha k hk
      have : a = ["input_tokens", "output_tokens", "cost"] := (Option.some.inj ha).symm
      subst this
      exact hk)
  have hm : (r.answers.map fun na => (na.1, na.2.encode)).mapM (readAnswer qs) = .ok r.answers := by
    have := mapM_ok (readAnswer qs) (fun na : String × Answer => (na.1, na.2.encode)) (fun na => na) r.answers (by
        intro na hna
        rcases na with ⟨n, a⟩
        have hf := hfit (n, a) hna
        simp only [AnswerFits] at hf
        cases hl : qs.lookup n with
        | none => simp [hl] at hf
        | some q =>
          simp only [hl] at hf
          simp [readAnswer, hl, answer_roundtrip _ q a hf, pure, Except.pure, bind, Except.bind])
    simpa using this
  have hmiss : qs.find? (fun nq => !(r.answers.map (·.1)).contains nq.1) = none := by
    rw [List.find?_eq_none]
    intro nq hnq
    simp [List.contains_iff_mem, hall nq hnq]
  rcases r with ⟨i, m, pv, ans, ⟨ti, to, cost⟩⟩
  simp only [] at hc1 hc2 hm hmiss ⊢
  simp only [strField, field, bind, Except.bind, rs1, rs2, rs3, rs4, rs5, us1, us2, us3, strOf_str, ho, hq, hu, natOf_natJ, costOf_ok _ cost hc1 hc2]
  rw [hm]
  simp only [hmiss]
  rfl

/-- W3 for requests, as a composition: a valid request encodes, and the encoding decodes back to it. -/
theorem request_encode_decode (r : Request) (h : r.Valid) : (Request.encode r).bind Request.decode = .ok r := by
  obtain ⟨j, he, hd⟩ := request_roundtrip r h
  simp [he, hd, Except.bind]

/-- W3 for responses, as a composition with the encoder. -/
theorem response_encode_decode (qs : List (String × Question)) (r : Response) (h : r.Valid qs) :
    Response.decode qs (Response.encode r) = .ok r := response_roundtrip qs r h

/-- An invalid request is refused by the encoder (the encoder never writes a request the decoder would refuse). -/
theorem request_encode_refuses (r : Request) (h : ¬ r.Valid) : ∃ e, r.encode = .error e := by
  unfold Request.encode
  cases hc : r.check with
  | ok u => exact absurd ((request_check_ok_iff r).1 (by cases u; exact hc)) h
  | error e => exact ⟨e, rfl⟩

/-! ## W4: totality and the nesting guard -/

/-- W4: a value nested deeper than `maxNestingDepth` is refused by the root request decoder. -/
theorem Request.decode_nestingTooDeep (j : J) (h : maxNestingDepth < J.depth j) :
    Request.decode j = .error ⟨.nestingTooDeep, ""⟩ := by
  have : ¬ J.depth j ≤ maxNestingDepth := by omega
  simp [Request.decode, this, refuse]

/-- W4: the same for the root response decoder. -/
theorem Response.decode_nestingTooDeep (qs : List (String × Question)) (j : J) (h : maxNestingDepth < J.depth j) :
    Response.decode qs j = .error ⟨.nestingTooDeep, ""⟩ := by
  have : ¬ J.depth j ≤ maxNestingDepth := by omega
  simp [Response.decode, this, refuse]

/-- W4: each root decoder of this slice returns an `ok` or a typed refusal, for every `J`. -/
theorem message_decode_total (qs : List (String × Question)) (j : J) :
    ((∃ r, Request.decode j = .ok r) ∨ ∃ e : Refusal, Request.decode j = .error e) ∧
    ((∃ r, Response.decode qs j = .ok r) ∨ ∃ e : Refusal, Response.decode qs j = .error e) := by
  refine ⟨?_, ?_⟩
  · cases h : Request.decode j with
    | ok x => exact .inl ⟨x, rfl⟩
    | error e => exact .inr ⟨e, rfl⟩
  · cases h : Response.decode qs j with
    | ok x => exact .inl ⟨x, rfl⟩
    | error e => exact .inr ⟨e, rfl⟩

/-- A decoded request is valid: the decoder ends in `Request.check`. -/
theorem Request.decodeAt_valid (j : J) (r : Request) (h : Request.decodeAt j = .ok r) : r.Valid := by
  unfold Request.decodeAt at h
  cases h1 : objOf "" (some ["model", "state", "questions"]) j with
  | error e => simp [h1, bind, Except.bind] at h
  | ok kvs =>
    cases h2 : strField "" kvs "model" with
    | error e => simp [h1, h2, bind, Except.bind] at h
    | ok m =>
      cases h3 : field "" kvs "state" with
      | error e => simp [h1, h2, h3, bind, Except.bind] at h
      | ok st =>
        cases h4 : field "" kvs "questions" with
        | error e => simp [h1, h2, h3, h4, bind, Except.bind] at h
        | ok qj =>
          cases h5 : objOf "questions" none qj with
          | error e => simp [h1, h2, h3, h4, h5, bind, Except.bind] at h
          | ok qs =>
            cases h6 : qs.mapM readQuestion with
            | error e => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind] at h
            | ok qs' =>
              simp only [h1, h2, h3, h4, h5, h6, bind, Except.bind] at h
              cases h7 : Request.check ⟨m, st, qs'⟩ with
              | error e => simp [h7] at h
              | ok u =>
                simp [h7, pure, Except.pure] at h
                subst h
                exact (request_check_ok_iff _).1 (by cases u; exact h7)

theorem Request.decode_valid (j : J) (r : Request) (h : Request.decode j = .ok r) : r.Valid := by
  unfold Request.decode at h
  by_cases hd : J.depth j ≤ maxNestingDepth
  · simp only [hd, ite_true] at h; exact Request.decodeAt_valid j r h
  · simp [hd, refuse] at h

/-! ## W1 for the request and response objects -/

/-- A duplicate key in a request object is refused, naming it. -/
theorem Request.decodeAt_duplicate (kvs : List (String × J)) (h : ¬ (kvs.map (·.1)).Nodup) :
    ∃ k, 2 ≤ (kvs.map (·.1)).count k ∧ Request.decodeAt (.obj kvs) = .error ⟨.duplicateKey, pathKey "" k⟩ := by
  obtain ⟨k, hc, he⟩ := objOf_duplicate "" (some ["model", "state", "questions"]) kvs h
  exact ⟨k, hc, by simp [Request.decodeAt, he, bind, Except.bind]⟩

/-- A key outside the three of a request is refused as `unknownField`, naming it. -/
theorem Request.decodeAt_unknownField (kvs : List (String × J)) (k : String)
    (hnd : (kvs.map (·.1)).Nodup) (hk : k ∈ kvs.map (·.1)) (hn : k ∉ ["model", "state", "questions"])
    (hu : ∀ k' ∈ kvs.map (·.1), k' ∉ ["model", "state", "questions"] → k' = k) :
    Request.decodeAt (.obj kvs) = .error ⟨.unknownField, pathKey "" k⟩ := by
  have hd : firstDup (kvs.map (·.1)) = none := (firstDup_eq_none _).2 hnd
  simp [Request.decodeAt, objOf, dupCheck, hd, unknownCheck_unique "" _ kvs k hk hn hu, bind, Except.bind]

/-- A duplicate key in a response object is refused, naming it. -/
theorem Response.decodeAt_duplicate (qs : List (String × Question)) (kvs : List (String × J)) (h : ¬ (kvs.map (·.1)).Nodup) :
    ∃ k, 2 ≤ (kvs.map (·.1)).count k ∧ Response.decodeAt qs (.obj kvs) = .error ⟨.duplicateKey, pathKey "" k⟩ := by
  obtain ⟨k, hc, he⟩ := objOf_duplicate "" (some ["id", "model", "provider", "answers", "usage"]) kvs h
  exact ⟨k, hc, by simp [Response.decodeAt, he, bind, Except.bind]⟩

/-- A key outside the five of a response is refused as `unknownField`, naming it. -/
theorem Response.decodeAt_unknownField (qs : List (String × Question)) (kvs : List (String × J)) (k : String)
    (hnd : (kvs.map (·.1)).Nodup) (hk : k ∈ kvs.map (·.1)) (hn : k ∉ ["id", "model", "provider", "answers", "usage"])
    (hu : ∀ k' ∈ kvs.map (·.1), k' ∉ ["id", "model", "provider", "answers", "usage"] → k' = k) :
    Response.decodeAt qs (.obj kvs) = .error ⟨.unknownField, pathKey "" k⟩ := by
  have hd : firstDup (kvs.map (·.1)) = none := (firstDup_eq_none _).2 hnd
  simp [Response.decodeAt, objOf, dupCheck, hd, unknownCheck_unique "" _ kvs k hk hn hu, bind, Except.bind]

/-! ## Witnesses: the vectors V1 and V2 of the spec -/

set_option maxRecDepth 8000

private def p (n : Nat) (h : n ≤ 1000000 := by decide) : Prob := ⟨n, h⟩
private def dec (m : Nat) (e : Int) : J := .num ⟨false, m, e⟩
private def v1 : Request := ⟨"acme/alpha-2026", .arr [.str "The invoice is overdue."],
  [("overdue", .noul "Is the invoice overdue?" none),
   ("tone", .choice "Which tone?" [("calm", none), ("angry", some "hostile words")]),
   ("urgency", .score "How urgent?" ["none", "some", "high"])]⟩
private def v2 : Response := ⟨"r1", "alpha-2026-11-01", "acme-cloud",
  [("overdue", .noul (p 973100)),
   ("tone", .choice "calm" [("calm", p 800000), ("angry", p 200000)] (p 800000)),
   ("urgency", .score 1500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"])],
  ⟨12, 3, ⟨false, 4, -4⟩⟩⟩
private def v2j : J := .obj [("id", .str "r1"), ("model", .str "alpha-2026-11-01"), ("provider", .str "acme-cloud"),
  ("answers", .obj [("overdue", .obj [("type", .str "noul"), ("noul", dec 9731 (-4))]),
    ("tone", .obj [("type", .str "choice"), ("choice", .str "calm"),
      ("probabilities", .obj [("calm", dec 8 (-1)), ("angry", dec 2 (-1))]), ("confidence", dec 8 (-1))]),
    ("urgency", .obj [("type", .str "score"), ("score", dec 15 (-1)), ("confidence", dec 7 (-1)),
      ("probabilities", .obj [("0", dec 0 0), ("1", dec 5 (-1)), ("2", dec 5 (-1))]),
      ("legend", .obj [("0", .str "none"), ("1", .str "some"), ("2", .str "high")])])]),
  ("usage", .obj [("input_tokens", dec 12 0), ("output_tokens", dec 3 0), ("cost", dec 4 (-4))])]
/-- A value nested `n` arrays deep. -/
private def nest : Nat → J
  | 0 => .null
  | n + 1 => .arr [nest n]

-- the hypotheses of W3 can hold: V1 is a valid request and V2 a valid response for its questions.
example : v1.Valid := by decide +kernel
example : v2.Valid v1.questions := by decide +kernel
example : v1.check = .ok () := by rfl
-- W3: the vectors round trip, and V2 decodes from its wire form (wire order kept).
example : (Request.encode v1).bind Request.decode = .ok v1 := by rfl
example : Response.decode v1.questions (Response.encode v2) = .ok v2 := by rfl
example : Response.decode v1.questions v2j = .ok v2 := by rfl
-- the refusals of the spec's response rules.
example : Response.decode v1.questions (.obj [("id", .str "r1"), ("model", .str "m"), ("provider", .str "p"),
    ("answers", .obj []), ("usage", .obj [("input_tokens", dec 1 0), ("output_tokens", dec 1 0), ("cost", dec 1 (-4))])]) =
    .error ⟨.missingAnswer, "answers.overdue"⟩ := by rfl
example : Response.decode [] (.obj [("id", .str "r1"), ("model", .str "m"), ("provider", .str "p"),
    ("answers", .obj [("x", .obj [("type", .str "noul"), ("noul", dec 5 (-1))])]),
    ("usage", .obj [("input_tokens", dec 1 0), ("output_tokens", dec 1 0), ("cost", dec 1 (-4))])]) =
    .error ⟨.unexpectedAnswer, "answers.x"⟩ := by rfl
example : Response.decode [] (.obj [("id", .str "r1"), ("model", .str "m"), ("provider", .str "p"), ("answers", .obj []),
    ("usage", .obj [("input_tokens", dec 1 0), ("output_tokens", dec 1 0), ("cost", dec 1 (-4))]), ("created", dec 1 0)]) =
    .error ⟨.unknownField, "created"⟩ := by rfl
example : Response.decode [] (.obj [("id", .str "r1"), ("model", .str "m"), ("provider", .str "p"), ("answers", .obj []),
    ("usage", .obj [("input_tokens", dec 5 (-1)), ("output_tokens", dec 1 0), ("cost", dec 1 (-4))])]) =
    .error ⟨.notNatural, "usage.input_tokens"⟩ := by rfl
example : Request.decode (.obj [("model", .str "acme"), ("state", .arr [.str "s"]), ("questions", .obj [("a", Question.encode (.box "i"))])]) =
    .error ⟨.badModelName, "model"⟩ := by rfl
example : Request.decode (.obj [("model", .str "acme/x"), ("state", .arr [.str "s"]), ("questions", .obj [])]) =
    .error ⟨.noQuestions, "questions"⟩ := by rfl
example : Request.decode (.obj [("model", .str "acme/x"), ("state", .arr []), ("questions", .obj [("a", Question.encode (.box "i"))])]) =
    .error ⟨.badState, "state"⟩ := by rfl
example : Request.decode (.obj [("model", .str "acme/x"), ("model", .str "acme/y"), ("state", .arr [.str "s"])]) =
    .error ⟨.duplicateKey, "model"⟩ := by rfl
example : Request.decode (.obj [("model", .str "acme/x"), ("state", .arr [.str "s"]), ("questions", .obj [("a", Question.encode (.box "i"))]), ("extra", .null)]) =
    .error ⟨.unknownField, "extra"⟩ := by rfl
example : Request.encode ⟨"acme/x", .arr [.str "s"], []⟩ = .error ⟨.noQuestions, "questions"⟩ := by rfl
example : Request.decode (.obj [("model", .str "acme/x"), ("state", .arr [.str "s"]), ("questions", .obj [("a", .obj [("type", .str "choice"), ("instructions", .str "t"), ("criteria", .obj [("x", .null)])])])]) =
    .error ⟨.tooFewOptions, "questions.a.criteria"⟩ := by rfl
-- the hypotheses of the W1 theorems for requests can hold.
example : (["model", "state", "extra"]).Nodup := by decide
example : "extra" ∉ ["model", "state", "questions"] := by decide
example : ¬ (["model", "model"]).Nodup := by decide
-- W4: a vector nested 33 deep is refused by both decoders; 32 deep passes the guard.
example : J.depth (nest 33) = 33 := by rfl
example : Request.decode (nest 33) = .error ⟨.nestingTooDeep, ""⟩ := by rfl
example : Response.decode v1.questions (nest 33) = .error ⟨.nestingTooDeep, ""⟩ := by rfl
example : Request.decode (nest 32) = .error ⟨.wrongKind, ""⟩ := by rfl
example : Response.decode v1.questions (nest 32) = .error ⟨.wrongKind, ""⟩ := by rfl

end VbmDecision
