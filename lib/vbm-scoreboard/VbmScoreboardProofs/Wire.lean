import VbmScoreboardWire
import VbmScoreboardProofs.Direction
/-! # The wire formats, proved

Every theorem about `VbmScoreboardWire.Format`, each with a non-vacuity witness (an `example` whose hypothesis holds). The definitions are in `VbmScoreboardWire/Format.lean`; the types (`Reading`, `Floor`, `Entry`, `Baseline`) are the core's.

**What is proved and what is trusted.** `Lean.Json.parse` and `Lean.Json.compress` are opaque to the kernel, so the text round trips cannot be proved of them. They are proved of ANY parser and renderer that are faithful on the objects the encoder writes (`LineOK`: the parser reads back what the renderer wrote, the written line has no newline and is not blank); the faithfulness of the real pair is the one trusted fact (a boundary), checked below by `#guard` on the real pair for concrete values. Everything else (the objects, the keys, the refusals, the line numbers, the order) is proved. The round trips at the object level (`readingOfJson_readingJson`, `floorOfJson_floorJson`, `entryOfJson_entryJson`) need no hypothesis.

Theorems (each has a witness, an `example` whose hypothesis holds):

* `decode_encode_readings`, `decode_encode_baseline`, `decode_encode_history`: the round trips, for every value the encoder produces (readings and floors with distinct metrics; the baseline comes back SORTED).
* `decodeReadings_refuses_duplicate` (a repeated metric is refused, naming the line of the second), `dupCheck_refuses_any` (any list with a repeated key is refused).
* `decodeReadings_refuses_unknown_version` (a line whose `v` is not 1 is refused with that number).
* `decodeReadings_names_line` (a bad line after good ones is refused with its own 1-based number; witness: a bad third line).
* `encodeBaseline_sorted` (the encoding is in metric order, so the file is diff-friendly), `sortFloors_perm` (and loses no floor).

Not proved: that `Lean.Json.parse` reads back `Lean.Json.compress` (see above), and nothing is said about `String` functions for general strings. -/
namespace VbmScoreboardWire

open Lean
open VbmScoreboard (Reading Floor Entry Baseline Direction Event)

/-! ## Lines -/

theorem splitAux_line (l : List Char) (cur rest : List Char) (h : '\n' ∉ l) :
    splitAux (l ++ '\n' :: rest) cur = String.ofList (cur.reverse ++ l) :: splitAux rest [] := by
  induction l generalizing cur with
  | nil => simp [splitAux]
  | cons c cs ih =>
    have hc : c ≠ '\n' := fun e => h (e ▸ List.mem_cons_self)
    have hcs : '\n' ∉ cs := fun e => h (List.mem_cons_of_mem _ e)
    simp [splitAux, hc, ih _ hcs]

theorem splitLines_joinLines (ls : List String) (h : ∀ l ∈ ls, '\n' ∉ l.toList) :
    splitLines (joinLines ls) = ls ++ [""] := by
  unfold splitLines
  induction ls with
  | nil => simp [joinLines, splitAux]
  | cons l ls ih =>
    have h1 : '\n' ∉ l.toList := h l List.mem_cons_self
    have h2 : ∀ x ∈ ls, '\n' ∉ x.toList := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have e : (joinLines (l :: ls)).toList = l.toList ++ '\n' :: (joinLines ls).toList := by
      simp [joinLines]
    rw [e, splitAux_line _ _ _ h1]
    simp [ih h2]

/-! ## Decoding lines -/

theorem decodeLine_error_line {α : Type} (p : String → Except String Json)
    (f : Json → Except Why α) (n : Nat) (l : String) (e : Refusal)
    (h : decodeLine p f n l = .error e) : e.line = n := by
  unfold decodeLine at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h

theorem decodeLines_append {α : Type} (p : String → Except String Json) (f : Json → Except Why α) :
    ∀ (n : Nat) (ls₁ ls₂ : List String) (xs : List (Nat × α)),
      decodeLines p f n ls₁ = .ok xs →
      decodeLines p f n (ls₁ ++ ls₂) =
        (match decodeLines p f (n + ls₁.length) ls₂ with
         | .error e => .error e
         | .ok r => .ok (xs ++ r))
  | n, [], ls₂, xs, h => by
    simp only [decodeLines] at h
    cases h
    cases hd : decodeLines p f n ls₂ <;> simp [hd]
  | n, l :: ls₁, ls₂, xs, h => by
    simp only [decodeLines] at h
    simp only [List.cons_append, decodeLines]
    have e : n + (l :: ls₁).length = (n + 1) + ls₁.length := by simp; omega
    rw [e]
    cases hl : decodeLine p f n l with
    | error e => rw [hl] at h; cases h
    | ok o =>
      rw [hl] at h
      cases o with
      | none => exact decodeLines_append p f (n + 1) ls₁ ls₂ xs h
      | some a =>
        cases hr : decodeLines p f (n + 1) ls₁ with
        | error e => rw [hr] at h; cases h
        | ok r =>
          rw [hr] at h
          cases h
          have := decodeLines_append p f (n + 1) ls₁ ls₂ r hr
          rw [this]
          cases decodeLines p f ((n + 1) + ls₁.length) ls₂ <;> simp

/-- A bad line after good ones is refused with ITS OWN number: the first line's number plus the lines before it. -/
theorem decodeReadings_names_line_general {α : Type} (p : String → Except String Json)
    (f : Json → Except Why α) (n : Nat) (ls₁ : List String) (l : String) (rest : List String)
    (xs : List (Nat × α)) (e : Refusal)
    (hgood : decodeLines p f n ls₁ = .ok xs)
    (hbad : decodeLine p f (n + ls₁.length) l = .error e) :
    decodeLines p f n (ls₁ ++ l :: rest) = .error e ∧ e.line = n + ls₁.length := by
  refine ⟨?_, decodeLine_error_line p f _ l e hbad⟩
  rw [decodeLines_append p f n ls₁ (l :: rest) xs hgood]
  simp [decodeLines, hbad]

theorem decodeLines_blank {α : Type} (p : String → Except String Json)
    (f : Json → Except Why α) (n : Nat) :
    decodeLines p f n [""] = .ok [] := by
  simp [decodeLines, decodeLine, isBlank]

theorem decodeLines_append_blank {α : Type} (p : String → Except String Json)
    (f : Json → Except Why α) :
    ∀ (n : Nat) (ls : List String), decodeLines p f n (ls ++ [""]) = decodeLines p f n ls
  | n, [] => by simp [decodeLines_blank]; rfl
  | n, l :: ls => by
    simp only [List.cons_append, decodeLines]
    rw [decodeLines_append_blank p f (n + 1) ls]

theorem dupCheck_refuses_seen {α : Type} (key : α → String) (seen : List String) (n : Nat)
    (a : α) (rest : List (Nat × α)) (h : key a ∈ seen) :
    dupCheck key seen ((n, a) :: rest) = .error ⟨n, .duplicate (key a)⟩ := by
  simp [dupCheck, h]

theorem dupCheck_ok {α : Type} (key : α → String) :
    ∀ (as : List α) (seen : List String) (n : Nat),
      (∀ a ∈ as, key a ∉ seen) → (as.map key).Nodup →
      dupCheck key seen (indexed n as) = .ok as
  | [], seen, n, _, _ => by simp [indexed, dupCheck]
  | a :: as, seen, n, h1, h2 => by
    have ha : key a ∉ seen := h1 a List.mem_cons_self
    have h2' : (key a :: as.map key).Nodup := h2
    have hnd := List.nodup_cons.mp h2'
    have h1' : ∀ b ∈ as, key b ∉ (key a :: seen) := by
      intro b hb hm
      rcases List.mem_cons.mp hm with e | e
      · exact hnd.1 (List.mem_map.mpr ⟨b, hb, e⟩)
      · exact h1 b (List.mem_cons_of_mem _ hb) e
    have := dupCheck_ok key as (key a :: seen) (n + 1) h1' hnd.2
    simp [indexed, dupCheck, ha, this]

/-- Any list with a repeated key is refused (by whichever occurrence comes second). -/
theorem dupCheck_refuses_any {α : Type} (key : α → String) :
    ∀ (as : List α) (seen : List String) (n : Nat),
      seen.Nodup → ¬ ((as.map key) ++ seen).Nodup →
      ∃ e, dupCheck key seen (indexed n as) = .error e
  | [], seen, n, hs, h => absurd (by simpa using hs) h
  | a :: as, seen, n, hs, h => by
    by_cases ha : key a ∈ seen
    · exact ⟨_, dupCheck_refuses_seen key seen n a _ ha⟩
    · have hs' : (key a :: seen).Nodup := List.nodup_cons.mpr ⟨ha, hs⟩
      have h' : ¬ ((as.map key) ++ (key a :: seen)).Nodup := by
        intro hn
        apply h
        have hp : ((as.map key) ++ (key a :: seen)).Perm ((key a :: as.map key) ++ seen) := by
          simp
        simp only [List.map_cons]
        exact hp.nodup_iff.mp hn
      obtain ⟨e, he⟩ := dupCheck_refuses_any key as (key a :: seen) (n + 1) hs' h'
      refine ⟨e, ?_⟩
      simp [indexed, dupCheck, ha, he]

/-! ## Objects of the three formats -/

theorem readingOfJson_readingJson (r : Reading) : readingOfJson (readingJson r) = .ok r := by
  obtain ⟨m, v⟩ := r
  rfl

theorem floorOfJson_floorJson (f : Floor) : floorOfJson (floorJson f) = .ok f := by
  obtain ⟨m, d, n⟩ := f
  cases d <;> rfl

theorem eventOf_eventWord (ev : Event) :
    eventOf (eventWord ev) (reasonOf ev) (authorOf ev) = .ok ev := by
  cases ev <;> rfl

theorem entryOfJson_entryJson (e : Entry) : entryOfJson (entryJson e) = .ok e := by
  obtain ⟨t, m, b, a, ev⟩ := e
  have hv : natField (entryJson ⟨t, m, b, a, ev⟩) "v" = .ok 1 := rfl
  have ht : natField (entryJson ⟨t, m, b, a, ev⟩) "at" = .ok t := rfl
  have hm : strField (entryJson ⟨t, m, b, a, ev⟩) "metric" = .ok m := rfl
  have he : strField (entryJson ⟨t, m, b, a, ev⟩) "event" = .ok (eventWord ev) := rfl
  have hb : optNatField (entryJson ⟨t, m, b, a, ev⟩) "before" = .ok b := by cases b <;> rfl
  have ha : optNatField (entryJson ⟨t, m, b, a, ev⟩) "after" = .ok a := by cases a <;> rfl
  have hr : optStrField (entryJson ⟨t, m, b, a, ev⟩) "reason" = .ok (reasonOf ev) := by
    cases ev <;> rfl
  have hu : optStrField (entryJson ⟨t, m, b, a, ev⟩) "author" = .ok (authorOf ev) := by
    cases ev <;> rfl
  simp only [entryOfJson, checkVersion, hv, ht, hm, he, hb, ha, hr, hu, version,
    eventOf_eventWord]
  simp

/-! ## The order of a baseline -/

theorem mem_insertFloor (x y : Floor) :
    ∀ l : List Floor, y ∈ insertFloor x l → y = x ∨ y ∈ l
  | [], h => by simp [insertFloor] at h; exact Or.inl h
  | g :: gs, h => by
    unfold insertFloor at h
    split at h
    · simpa using h
    · rcases List.mem_cons.mp h with e | e
      · exact Or.inr (e ▸ List.mem_cons_self)
      · rcases mem_insertFloor x y gs e with e' | e'
        · exact Or.inl e'
        · exact Or.inr (List.mem_cons_of_mem _ e')

def Ordered (l : List Floor) : Prop := l.Pairwise (fun f g => f.metric ≤ g.metric)

theorem insertFloor_ordered (x : Floor) :
    ∀ l : List Floor, Ordered l → Ordered (insertFloor x l)
  | [], _ => by simp [insertFloor, Ordered]
  | g :: gs, h => by
    have hp := List.pairwise_cons.mp h
    unfold insertFloor
    split
    · rename_i hx
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro y hy
      rcases List.mem_cons.mp hy with e | e
      · exact e ▸ hx
      · exact String.le_trans hx (hp.1 y e)
    · rename_i hx
      have hgx : g.metric ≤ x.metric := by
        rcases String.le_total x.metric g.metric with h1 | h1
        · exact absurd h1 hx
        · exact h1
      refine List.pairwise_cons.mpr ⟨?_, insertFloor_ordered x gs hp.2⟩
      intro y hy
      rcases mem_insertFloor x y gs hy with e | e
      · exact e ▸ hgx
      · exact hp.1 y e

theorem insertFloor_perm (x : Floor) :
    ∀ l : List Floor, (insertFloor x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | g :: gs => by
    unfold insertFloor
    split
    · exact List.Perm.refl _
    · exact ((insertFloor_perm x gs).cons g).trans (List.Perm.swap x g gs)

theorem sortFloors_perm : ∀ l : List Floor, (sortFloors l).Perm l
  | [] => List.Perm.refl _
  | f :: fs => (insertFloor_perm f (sortFloors fs)).trans ((sortFloors_perm fs).cons f)

theorem sortFloors_ordered : ∀ l : List Floor, Ordered (sortFloors l)
  | [] => by simp [sortFloors, Ordered]
  | f :: fs => insertFloor_ordered f _ (sortFloors_ordered fs)

/-- The encoding of a baseline is in the order of the metrics' names: a file is diff-friendly. -/
theorem encodeBaseline_sorted (b : Baseline) :
    (sortFloors b).Pairwise (fun f g => f.metric ≤ g.metric) :=
  sortFloors_ordered b

example : (sortFloors [⟨"b", .lower, 2⟩, ⟨"a", .higher, 1⟩]).map (·.metric) = ["a", "b"] := by
  decide +kernel

/-! ## The three formats, over any parser and renderer -/

theorem decodeWith_encodeWith {α : Type} (p : String → Except String Json)
    (render : Json → String) (f : Json → Except Why α) (toJ : α → Json) (as : List α)
    (hf : ∀ a ∈ as, f (toJ a) = .ok a)
    (hl : ∀ a ∈ as, LineOK p render (toJ a)) :
    decodeText p f (encodeWith render toJ as) = .ok (indexed 1 as) := by
  have hnl : ∀ l ∈ as.map (fun a => render (toJ a)), '\n' ∉ l.toList := by
    intro l hl'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl'
    exact (hl a ha).2.1
  unfold decodeText encodeWith
  rw [splitLines_joinLines _ hnl, decodeLines_append_blank]
  have key : ∀ (n : Nat) (as : List α), (∀ a ∈ as, f (toJ a) = .ok a) →
      (∀ a ∈ as, LineOK p render (toJ a)) →
      decodeLines p f n (as.map (fun a => render (toJ a))) = .ok (indexed n as) := by
    intro n as
    induction as generalizing n with
    | nil => intro _ _; simp [decodeLines, indexed]
    | cons a as ih =>
      intro h1 h2
      have ha := h2 a List.mem_cons_self
      have := ih (n + 1) (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
        (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
      simp only [List.map_cons, decodeLines, decodeLine, ha.2.2, ha.1,
        h1 a List.mem_cons_self, this, indexed]
      simp
  exact key 1 as hf hl

/-! ### The provider protocol -/

/-- The round trip: any parser and renderer faithful on the lines written give the readings back (their metrics distinct). -/
theorem decode_encode_readings (p : String → Except String Json) (render : Json → String)
    (rs : List Reading) (hok : ∀ r ∈ rs, LineOK p render (readingJson r))
    (hnd : (rs.map Reading.metric).Nodup) :
    decodeReadingsWith p (encodeReadingsWith render rs) = .ok rs := by
  unfold decodeReadingsWith encodeReadingsWith
  rw [decodeWith_encodeWith p render readingOfJson readingJson rs
    (fun r _ => readingOfJson_readingJson r) hok]
  exact dupCheck_ok _ rs [] 1 (by simp) hnd

/-- The same for the real parser and renderer, given their faithfulness on these lines. -/
theorem decode_encode_readings_real (rs : List Reading)
    (hok : ∀ r ∈ rs, LineOK Json.parse Json.compress (readingJson r))
    (hnd : (rs.map Reading.metric).Nodup) :
    decodeReadings (encodeReadings rs) = .ok rs :=
  decode_encode_readings Json.parse Json.compress rs hok hnd

/-- A repeated metric is refused, naming the line of the second. -/
theorem decodeReadings_refuses_duplicate (p : String → Except String Json)
    (render : Json → String) (r r' : Reading) (hm : r'.metric = r.metric)
    (h1 : LineOK p render (readingJson r)) (h2 : LineOK p render (readingJson r')) :
    decodeReadingsWith p (encodeReadingsWith render [r, r']) = .error ⟨2, .duplicate r.metric⟩ := by
  unfold decodeReadingsWith encodeReadingsWith
  have := decodeWith_encodeWith p render readingOfJson readingJson [r, r']
    (fun r _ => readingOfJson_readingJson r)
    (by
      intro a ha
      rcases List.mem_cons.mp ha with e | e
      · exact e ▸ h1
      · simp at e; exact e ▸ h2)
  rw [this]
  simp [indexed, dupCheck, hm]

/-- A line whose version is not 1 is refused with the version it names (the first line here). -/
theorem decodeReadings_refuses_unknown_version (p : String → Except String Json) (text : String)
    (l : String) (rest : List String) (j : Json) (v : Nat)
    (hsplit : splitLines text = l :: rest) (hb : isBlank l = false) (hp : p l = .ok j)
    (hv : natField j "v" = .ok v) (hne : v ≠ version) :
    decodeReadingsWith p text = .error ⟨1, .unknownVersion v⟩ := by
  unfold decodeReadingsWith decodeText
  rw [hsplit]
  simp [decodeLines, decodeLine, hb, hp, readingOfJson, checkVersion, hv, hne]

/-- A bad line after good ones is refused with its own 1-based number. -/
theorem decodeReadings_names_line (p : String → Except String Json) (ls₁ : List String)
    (l : String) (rest : List String) (xs : List (Nat × Reading)) (e : Refusal)
    (hgood : decodeLines p readingOfJson 1 ls₁ = .ok xs)
    (hbad : decodeLine p readingOfJson (1 + ls₁.length) l = .error e) :
    decodeLines p readingOfJson 1 (ls₁ ++ l :: rest) = .error e ∧ e.line = 1 + ls₁.length :=
  decodeReadings_names_line_general p readingOfJson 1 ls₁ l rest xs e hgood hbad

/-! ### The baseline file -/

/-- The round trip: the floors come back in the order of their metrics (the metrics distinct). -/
theorem decode_encode_baseline (p : String → Except String Json) (render : Json → String)
    (b : Baseline) (hok : ∀ f ∈ b, LineOK p render (floorJson f))
    (hnd : (b.map Floor.metric).Nodup) :
    decodeBaselineWith p (encodeBaselineWith render b) = .ok (sortFloors b) := by
  unfold decodeBaselineWith encodeBaselineWith
  have hperm := sortFloors_perm b
  rw [decodeWith_encodeWith p render floorOfJson floorJson (sortFloors b)
    (fun f _ => floorOfJson_floorJson f) (fun f hf => hok f (hperm.subset hf))]
  exact dupCheck_ok _ _ [] 1 (by simp) ((hperm.map Floor.metric).nodup_iff.mpr hnd)

/-! ### The history file -/

theorem indexed_map_snd {α : Type} :
    ∀ (n : Nat) (as : List α), (indexed n as).map (·.2) = as
  | _, [] => rfl
  | n, a :: as => by simp [indexed, indexed_map_snd (n + 1) as]

/-- The round trip, for every history (a metric appears many times in a series). -/
theorem decode_encode_history (p : String → Except String Json) (render : Json → String)
    (h : List Entry) (hok : ∀ e ∈ h, LineOK p render (entryJson e)) :
    decodeHistoryWith p (encodeHistoryWith render h) = .ok h := by
  unfold decodeHistoryWith encodeHistoryWith
  rw [decodeWith_encodeWith p render entryOfJson entryJson h
    (fun e _ => entryOfJson_entryJson e) hok]
  simp [indexed_map_snd]

/-! ## Witnesses

The hypotheses of the round trips are met: a TABLE parser and renderer (a toy pair faithful on the lines it lists) satisfy `LineOK` for concrete readings, floors and entries; and the real pair reads back what it writes, checked by `#guard` on concrete values (the trusted fact above). -/

/-- A toy renderer: a line named by an object's metric and its number (`value`, `at` or `floor`). -/
def tableRender (j : Json) : String :=
  (match (j.getObjValD "metric").getStr? with | .ok m => m | .error _ => "?") ++ "#" ++
  (match (j.getObjValD "value").getNat? with
   | .ok n => toString n
   | .error _ =>
     match (j.getObjValD "at").getNat? with
     | .ok n => toString n
     | .error _ =>
       match (j.getObjValD "floor").getNat? with
       | .ok n => toString n
       | .error _ => "?")

/-- A toy parser: the object of the table whose line this is. -/
def tableParse (t : List Json) (s : String) : Except String Json :=
  match t.find? (fun x => tableRender x == s) with
  | some x => .ok x
  | none => .error "unknown line"

def wR1 : Reading := { metric := "cov", value := 91 }
def wR2 : Reading := { metric := "size", value := 4096 }
def wF1 : Floor := { metric := "size", direction := .lower, value := 4000 }
def wF2 : Floor := { metric := "cov", direction := .higher, value := 90 }
def wE1 : Entry :=
  { time := 7, metric := "cov", before := some 90, after := some 91, event := .banked }
def wE2 : Entry :=
  { time := 9, metric := "cov", before := some 91, after := some 85,
    event := .reset "rewrite" "ann" }

def wTable : List Json :=
  [readingJson wR1, readingJson wR2, floorJson wF1, floorJson wF2, entryJson wE1, entryJson wE2,
   readingJson { wR2 with metric := "cov" },
   Json.mkObj [("v", natJ 2), ("metric", Json.str "cov"), ("value", natJ 1)]]

theorem wReadingsOK : ∀ r ∈ [wR1, wR2], LineOK (tableParse wTable) tableRender (readingJson r) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨rfl, by decide, rfl⟩

theorem wFloorsOK : ∀ f ∈ [wF1, wF2], LineOK (tableParse wTable) tableRender (floorJson f) := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> exact ⟨rfl, by decide, rfl⟩

theorem wEntriesOK : ∀ e ∈ [wE1, wE2], LineOK (tableParse wTable) tableRender (entryJson e) := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact ⟨rfl, by decide, rfl⟩

/-- Witness: `decode_encode_readings` on the toy pair. -/
example : decodeReadingsWith (tableParse wTable) (encodeReadingsWith tableRender [wR1, wR2]) =
    .ok [wR1, wR2] :=
  decode_encode_readings _ _ _ wReadingsOK (by decide)

/-- Witness: `decode_encode_baseline` on the toy pair (`wF1` is written first and read back after `wF2`). -/
example : decodeBaselineWith (tableParse wTable) (encodeBaselineWith tableRender [wF1, wF2]) =
    .ok [wF2, wF1] := by
  have := decode_encode_baseline (tableParse wTable) tableRender [wF1, wF2] wFloorsOK (by decide)
  rw [this]
  rfl

/-- Witness: `decode_encode_history` on the toy pair. -/
example : decodeHistoryWith (tableParse wTable) (encodeHistoryWith tableRender [wE1, wE2]) =
    .ok [wE1, wE2] :=
  decode_encode_history _ _ _ wEntriesOK

/-- Witness: `decodeReadings_refuses_duplicate`: the second `cov` is refused at line 2. -/
example : decodeReadingsWith (tableParse wTable)
    (encodeReadingsWith tableRender [wR1, { wR2 with metric := "cov" }]) =
    .error ⟨2, .duplicate "cov"⟩ :=
  decodeReadings_refuses_duplicate _ _ wR1 { wR2 with metric := "cov" } rfl
    ⟨rfl, by decide, rfl⟩ ⟨rfl, by decide, rfl⟩

/-- Witness: `decodeReadings_refuses_unknown_version` on a line of version 2 (the line `cov#1` of the table). -/
example : decodeReadingsWith (tableParse wTable) "cov#1\ncov#91\n" =
    .error ⟨1, .unknownVersion 2⟩ :=
  decodeReadings_refuses_unknown_version _ _ "cov#1" ["cov#91", ""]
    (Json.mkObj [("v", natJ 2), ("metric", Json.str "cov"), ("value", natJ 1)]) 2
    rfl rfl rfl rfl (by decide)

/-- Witness: `decodeReadings_names_line`: lines 1 and 2 are good (`cov#91`, a blank), line 3 is bad (`nope`): refused at 3. -/
example : decodeLines (tableParse wTable) readingOfJson 1 (["cov#91", ""] ++ "nope#0" :: []) =
    .error ⟨3, .notJson "unknown line"⟩ ∧
    (Refusal.mk 3 (.notJson "unknown line")).line = 1 + ["cov#91", ""].length :=
  decodeReadings_names_line (tableParse wTable) ["cov#91", ""] "nope#0" [] [(1, wR1)]
    ⟨3, .notJson "unknown line"⟩ rfl rfl

/-- Witness: `dupCheck_refuses_any`. -/
example : ∃ e, dupCheck Reading.metric [] (indexed 1 [wR1, wR2, { wR1 with value := 3 }]) =
    .error e :=
  dupCheck_refuses_any _ _ _ _ (by decide) (by decide)

/-- Witness: `splitLines_joinLines`. -/
example : splitLines (joinLines ["a", "b c"]) = ["a", "b c", ""] :=
  splitLines_joinLines _ (by decide)

/-! ### The real parser and renderer (the boundary, checked on concrete values) -/

/-- A result is exactly this value (for `#guard`: `Except` has no `BEq`). -/
def okIs {α : Type} [BEq α] (r : Except Refusal α) (a : α) : Bool :=
  match r with
  | .ok x => x == a
  | .error _ => false

/-- A result is exactly this refusal. -/
def refusedIs {α : Type} (r : Except Refusal α) (e : Refusal) : Bool :=
  match r with
  | .ok _ => false
  | .error x => x == e

#guard okIs (decodeReadings (encodeReadings [wR1, wR2])) [wR1, wR2]
#guard okIs (decodeBaseline (encodeBaseline [wF1, wF2])) [wF2, wF1]
#guard okIs (decodeHistory (encodeHistory [wE1, wE2])) [wE1, wE2]
#guard encodeReading wR2 == "{\"metric\":\"size\",\"v\":1,\"value\":4096}"
#guard okIs (decodeReadings "{\"v\": 1, \"metric\": \"a\", \"value\": 1}\n\n{\"v\": 1, \"metric\": \"b\", \"value\": 2, \"unit\": \"ms\"}\n")
  [{ metric := "a", value := 1 }, { metric := "b", value := 2 }]
#guard refusedIs (decodeReadings "{\"v\": 1, \"metric\": \"a\", \"value\": 1}\n\n{\"v\": 1, \"metric\": \"a\", \"value\": \"x\"}\n")
  ⟨3, .wrongType "value"⟩
#guard refusedIs (decodeReadings "{\"v\": 1, \"metric\": \"a\", \"value\": 1}\n{\"v\": 1, \"metric\": \"a\", \"value\": 2}\n")
  ⟨2, .duplicate "a"⟩
#guard refusedIs (decodeReadings "{\"v\": 2, \"metric\": \"a\", \"value\": 1}\n") ⟨1, .unknownVersion 2⟩
#guard refusedIs (decodeReadings "{\"metric\": \"a\", \"value\": 1}\n") ⟨1, .missingKey "v"⟩
#guard refusedIs (decodeReadings "{\"v\": 1, \"value\": 1}\n") ⟨1, .missingKey "metric"⟩
#guard refusedIs (decodeReadings "{\"v\": 1, \"metric\": \"a\", \"value\": 1}\n{\"v\": 1, \"metric\": \"b\", \"value\": 2}\n[1]\n")
  ⟨3, .notObject⟩
#guard refusedIs (decodeBaseline "{\"v\": 1, \"metric\": \"a\", \"direction\": \"up\", \"floor\": 1}\n")
  ⟨1, .unknownWord "direction" "up"⟩
#guard refusedIs (decodeHistory "{\"v\": 1, \"at\": 1, \"metric\": \"a\", \"event\": \"reset\", \"before\": 2, \"after\": 1}\n")
  ⟨1, .missingKey "reason"⟩

end VbmScoreboardWire
