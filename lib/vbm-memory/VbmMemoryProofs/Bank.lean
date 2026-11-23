import VbmMemory

/-! # Proofs of the bank: append-only retain, concurrent writers, eligibility, distinct ids

* **Retain is append-only and monotone** (`retain_notes`, `retain_prefix`, `retain_keeps`, `retain_has`, `retain_length`): the notes after retaining are the notes before plus the new one, the notes before are a prefix of the notes after, a retained note is never lost, the note retained is there, and each retain adds exactly one note.
* **Concurrent writers need no merge** (`retain_comm`): two instances retaining at once leave the same notes in either order — the two results are permutations of each other, not equal lists; the notes held are the same either way (`retain_comm_mem`).
* **A recall returns only what was retained, in the scopes asked for, and misses nothing eligible** (`eligible_sound`, `eligible_complete`). Ranking, choosing how many hits to
  return, and any further selection belong to the implementation; this is what a hit can be.
* **A derived note derives from at least one note the bank already holds** (`retainDerived_cites`, `retainDerived_cites_any`).
* **Distinct ids** (`retain_ids`, `retain_idsUnique`): the ids of a bank after retaining are the ids before plus the new one, and retaining a note whose id the bank does not hold keeps the ids distinct. In a bank whose ids are distinct, a derived note's citation names exactly one held note (`retainDerived_cites_unique`), and two notes of the bank are equal when their ids are (`.IdsUnique.eq_of_id_eq`).

The `id`s of a bank are not distinct unless a writer keeps them so: `retain` does not refuse a note whose `id` the bank already holds, and `Bank.IdsUnique` is the property a bank has when no two of its notes share an `id`. A bank without it may hold two notes with one `id`, and a citation of that `id` then names both.

A theorem with a hypothesis carries a witness beside it that its hypothesis can hold. -/
namespace VbmMemory

/-! ## Witness values: notes in one domain scope, banks holding them, one empty bank -/

/-- One note, in one domain scope, deriving from nothing. -/
def n0 : Note := { id := 0, scope := Scope.domain "d", source := "s", cites := [] }

/-- A second note, distinct from `n0` (its own id, scope and source), deriving from nothing. -/
def n1 : Note := { id := 1, scope := Scope.cls "x", source := "t", cites := [] }

/-- The bank holding exactly `n0`. -/
def one : Bank := { notes := [n0] }

/-- The empty bank. -/
def empty : Bank := { notes := [] }

/-! ## Retain is monotone and append-only -/

/-- **Retaining appends**: the notes after retaining a note are the notes before it plus that note. -/
theorem retain_notes (b : Bank) (n : Note) : (b.retain n).notes = b.notes ++ [n] := rfl

/-- **Nothing retained is rewritten, reordered or dropped**: the notes held before are a prefix of the notes held after (the same notes, in the same order, at the front). -/
theorem retain_prefix (b : Bank) (n : Note) : b.notes <+: (b.retain n).notes :=
  retain_notes b n ▸ List.prefix_append ..

/-- The note retained is the last note of the bank after retaining it: it is held. -/
theorem retain_has (b : Bank) (n : Note) : n ∈ (b.retain n).notes := by
  simp [Bank.retain]

/-- **Nothing retained is ever lost.** -/
theorem retain_keeps (b : Bank) (n m : Note) (h : m ∈ b.notes) : m ∈ (b.retain n).notes := by
  simp [Bank.retain, h]

/-- Retaining adds exactly one note. -/
theorem retain_length (b : Bank) (n : Note) : (b.retain n).notes.length = b.notes.length + 1 := by
  simp [Bank.retain]

/-! ## Witnesses that the hypotheses of the monotone laws can hold -/

/-- Witness: one retain on a bank of one note gives a bank of two notes, so a bank can hold more than one and the laws are not about the empty bank only. -/
example : (one.retain n1).notes.length = 2 := by decide

/-- Witness: `retain_keeps` keeps a note a bank already holds when another note is retained. -/
example : n0 ∈ (one.retain n1).notes :=
  retain_keeps one _ n0 (by decide)

/-- Witness: `retain_notes` holds of a bank that already holds a note: the note already there keeps its place, first. -/
example : (one.retain n1).notes = [n0, n1] := by decide

/-- Witness: `retain_prefix` holds of a bank that already holds a note: the two notes in order are a prefix of the three. -/
example : (one.retain n1).notes <+: ((one.retain n1).retain n0).notes :=
  retain_prefix _ _

/-! ## Concurrent writers need no merge -/

/-- **Concurrent writers need no merge**: two writers retaining at once leave the same notes in either order — the two results hold the same notes, as a permutation of each other (a different order, not the same list). -/
theorem retain_comm (b : Bank) (n m : Note) :
    List.Perm ((b.retain n).retain m).notes ((b.retain m).retain n).notes := by
  simp only [Bank.retain, List.append_assoc, List.singleton_append]
  exact List.Perm.append_left b.notes (List.Perm.swap' m n List.Perm.nil)

/-- **The notes held are the same whichever retain lands first**: the membership form of `retain_comm`. -/
theorem retain_comm_mem (b : Bank) (n m x : Note) :
    x ∈ ((b.retain n).retain m).notes ↔ x ∈ ((b.retain m).retain n).notes :=
  (retain_comm b n m).mem_iff

/-- Witness: two distinct writers retaining two distinct notes on one bank leave the same notes in either order, and those notes are exactly the two of them (so neither order loses one and the orders differ). -/
example : ((empty.retain n0).retain n1).notes = [n0, n1] ∧
    ((empty.retain n1).retain n0).notes = [n1, n0] ∧
    List.Perm ((empty.retain n0).retain n1).notes ((empty.retain n1).retain n0).notes :=
  ⟨by decide, by decide, retain_comm empty n0 n1⟩

/-- Witness: the membership form holds of two distinct writers retaining two distinct notes. -/
example : n1 ∈ ((empty.retain n0).retain n1).notes ∧ n0 ∈ ((empty.retain n1).retain n0).notes :=
  ⟨(retain_comm_mem empty n0 n1 n1).mpr (by decide), (retain_comm_mem empty n1 n0 n0).mpr (by decide)⟩

/-! ## Eligibility: what a recall may consider -/

/-- **Every hit was retained, in a scope asked for.** -/
theorem eligible_sound (b : Bank) (ss : List Scope) (h : Note) (hh : h ∈ b.eligible ss) :
    h ∈ b.notes ∧ h.scope ∈ ss := by
  simpa [Bank.eligible] using hh

/-- **Nothing eligible is missed.** -/
theorem eligible_complete (b : Bank) (ss : List Scope) (n : Note) (h : n ∈ b.notes) (hs : n.scope ∈ ss) :
    n ∈ b.eligible ss := by
  simp [Bank.eligible, h, hs]

/-! ## Witnesses that the hypotheses of the eligibility laws can hold -/

/-- Witness: a retained note in a scope asked for is eligible, and no note is eligible for a scope it is not in. -/
example : n0 ∈ one.eligible [Scope.domain "d"] ∧ (one.eligible [Scope.cls "x"]).length = 0 := by decide

/-- Witness: the hypothesis of `eligible_sound` can be met (a hit exists). -/
example : ∃ (b : Bank) (ss : List Scope) (h : Note), h ∈ b.eligible ss :=
  ⟨one, [Scope.domain "d"], n0, by decide⟩

/-- Witness: the hypotheses of `eligible_complete` can be met together (a retained note in a scope asked for). -/
example : n0 ∈ one.notes ∧ n0.scope ∈ [Scope.domain "d"] := by decide

/-! ## Derived notes cite notes the bank holds -/

/-- **A derived note derives from notes the bank already holds, and from at least one.** -/
theorem retainDerived_cites (b : Bank) (n : Note) (b' : Bank) (h : b.retainDerived n = some b') :
    n.cites ≠ [] ∧ ∀ c ∈ n.cites, ∃ m ∈ b.notes, m.id = c := by
  unfold Bank.retainDerived at h
  split at h
  · assumption
  · simp at h

/-- **Every citation of a retained derived note names a note the bank held before it was retained** (the second half of `retainDerived_cites`, as a law of its own): one `id` of the bank equals the citation — not yet that it names exactly one note, which `retainDerived_cites_unique` adds under `Bank.IdsUnique`. -/
theorem retainDerived_cites_any (b : Bank) (n : Note) (b' : Bank) (h : b.retainDerived n = some b')
    (c : Nat) (hc : c ∈ n.cites) : ∃ m ∈ b.notes, m.id = c :=
  (retainDerived_cites b n b' h).2 c hc

/-- Witness: retaining a derived note that derives from a note the bank holds is accepted, so the hypothesis of `retainDerived_cites` can be met. -/
example : (one.retainDerived ⟨2, .cls "x", "t", [0]⟩).isSome = true := by decide

/-- Witness: a derived note that derives from nothing is refused (there the hypothesis is not met, as intended). -/
example : (one.retainDerived ⟨2, .cls "x", "t", []⟩).isSome = false := by decide

/-! ## Distinct ids: what a citation can name -/

/-- The ids of a bank after retaining a note are the ids before plus that note's. -/
theorem retain_ids (b : Bank) (n : Note) : (b.retain n).Ids = b.Ids ++ [n.id] := by
  simp [Bank.Ids, Bank.retain]

/-- **Retaining a note whose id the bank does not hold keeps the ids distinct.** -/
theorem retain_idsUnique (b : Bank) (n : Note) (h : b.IdsUnique) (hn : b.IdFresh n.id) :
    (b.retain n).IdsUnique := by
  unfold Bank.IdsUnique at *
  rw [retain_ids]
  refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
  intro a ha b hb
  have hb' : b = n.id := by simpa using hb
  subst hb'
  intro hab
  exact hn (hab ▸ ha)

/-- Witness: the hypothesis of `retain_idsUnique` can hold (a bank with distinct ids — `n0` and `n1` differ — and an id it does not hold), and the bank it yields has distinct ids: three notes, three ids. -/
example : ((one.retain n1).retain ⟨2, .cls "y", "u", []⟩).IdsUnique := by
  apply retain_idsUnique
  · apply retain_idsUnique
    · show (Note.id n0 :: []).Nodup
      exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · show (1 : Nat) ∉ [Note.id n0]
      intro h
      exact absurd (List.mem_singleton.mp h) (by decide)
  · show (2 : Nat) ∉ [0, 1]
    intro h
    exact absurd (List.mem_cons.mp h) (by
      intro h'
      rcases h' with h' | h'
      · exact absurd h' (by decide)
      · exact absurd (List.mem_singleton.mp h') (by decide))

/-- Witness: two notes of a bank can share an id, so retaining alone does not make the ids distinct: there the hypothesis of `retain_idsUnique` does not hold. -/
example : ¬ (one.retain n0).IdsUnique ∧ ¬ one.IdFresh n0.id :=
  ⟨fun h => (List.nodup_cons.mp h).1 (by decide), fun h => h (by decide)⟩

/-- **In a bank whose ids are distinct, two notes with one id are the same note.** -/
theorem Bank.IdsUnique.eq_of_id_eq (b : Bank) (h : b.IdsUnique) (m₁ : Note) (h₁ : m₁ ∈ b.notes)
    (m₂ : Note) (h₂ : m₂ ∈ b.notes) (hid : m₁.id = m₂.id) : m₁ = m₂ := by
  obtain ⟨i, hi, hil⟩ := List.getElem_of_mem h₁
  obtain ⟨j, hj, hjl⟩ := List.getElem_of_mem h₂
  have hlen : (b.notes.map Note.id).length = b.notes.length := List.length_map ..
  have he : (b.notes.map Note.id)[i]'(by omega) = (b.notes.map Note.id)[j]'(by omega) := by
    simp only [List.getElem_map, hil, hjl, hid]
  have hij : i = j := (List.Nodup.getElem_inj h).mp he
  have hsub : b.notes[i] = b.notes[j] := by
    cases hij
    rfl
  have h2 : m₂ = m₁ := (hjl.symm.trans hsub.symm).trans hil
  exact h2.symm

/-- **In a bank whose ids are distinct, a derived note's citation names exactly one held note**: some held note has that `id`, and every held note that has it is that note. -/
theorem retainDerived_cites_unique (b : Bank) (n : Note) (b' : Bank) (h : b.retainDerived n = some b')
    (hu : b.IdsUnique) (c : Nat) (hc : c ∈ n.cites) :
    ∃ m : Note, (m ∈ b.notes ∧ m.id = c) ∧ ∀ m₂ : Note, m₂ ∈ b.notes → m₂.id = c → m₂ = m := by
  obtain ⟨m, hm, hmid⟩ := retainDerived_cites_any b n b' h c hc
  refine ⟨m, ⟨hm, hmid⟩, ?_⟩
  intro m₂ hm₂ hid₂
  exact Bank.IdsUnique.eq_of_id_eq b hu m₂ hm₂ m hm (hid₂.trans hmid.symm)

/-- Witness: the hypotheses of `retainDerived_cites_unique` can hold together — the bank's ids are distinct (`retain_idsUnique` above) and a note deriving from `n0` (`id` 0) is accepted — and its conclusion names one note: `n0`, since `n1` has another `id`. -/
example : ∃ (m : Note), (m ∈ (one.retain n1).notes ∧ m.id = 0) ∧
    ∀ m₂ : Note, m₂ ∈ (one.retain n1).notes → m₂.id = 0 → m₂ = m := by
  have h0 : one.IdsUnique := by
    show (Note.id n0 :: []).Nodup
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  have h1 : one.IdFresh n1.id := by
    show (1 : Nat) ∉ [Note.id n0]
    intro h
    exact absurd (List.mem_singleton.mp h) (by decide)
  have hu : (one.retain n1).IdsUnique := retain_idsUnique one n1 h0 h1
  have acc : (one.retain n1).retainDerived ⟨2, .cls "x", "t", [0]⟩ =
      some ((one.retain n1).retain ⟨2, .cls "x", "t", [0]⟩) := by
    unfold Bank.retainDerived
    split
    · rfl
    · next hne =>
      refine absurd ⟨by simp, ?_⟩ hne
      intro c hc
      show ∃ m ∈ [n0, n1], m.id = c
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨n0, List.mem_cons_self .., rfl⟩
  exact retainDerived_cites_unique (one.retain n1) _ _ acc hu 0 (by decide)

end VbmMemory
