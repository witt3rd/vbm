import VbmMemory

/-! # Proofs of the bank: append-only retain and eligibility

* **Retain is monotone** (`retain_keeps`, `retain_has`, `retain_length`): a retained note is never lost, the note retained is there, and each retain adds exactly one note.
* **Concurrent writers need no merge** (`retain_comm`): two instances retaining at once leave the same notes whichever lands first.
* **A recall returns only what was retained, in the scopes asked for, and misses nothing eligible** (`eligible_sound`, `eligible_complete`). Ranking, choosing how many hits to
  return, and any further selection belong to the implementation; this is what a hit can be.
* **A derived note derives from at least one note the bank already holds** (`retainDerived_cites`).

A theorem with a hypothesis carries a witness beside it that its hypothesis can hold. -/
namespace VbmMemory

/-! ## Witness values: one note in one scope, one bank holding it, one empty bank -/

/-- One note, in one domain scope, deriving from nothing. -/
def n0 : Note := { id := 0, scope := Scope.domain "d", source := "s", cites := [] }

/-- The bank holding exactly `n0`. -/
def one : Bank := { notes := [n0] }

/-- The empty bank. -/
def empty : Bank := { notes := [] }

/-! ## Retain is monotone and append-only -/

/-- The note retained is in the bank after retaining it. -/
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
example : (one.retain { id := 1, scope := Scope.cls "x", source := "t", cites := [] }).notes.length = 2 := by
  decide

/-- Witness: `retain_keeps` keeps a note a bank already holds when another note is retained. -/
example : n0 ∈ (one.retain { id := 1, scope := Scope.cls "x", source := "t", cites := [] }).notes :=
  retain_keeps one _ n0 (by decide)


/-! ## Concurrent writers need no merge -/

/-- **Concurrent writers need no merge**: the notes held do not depend on which of two retains lands first. -/
theorem retain_comm (b : Bank) (n m x : Note) :
    x ∈ ((b.retain n).retain m).notes ↔ x ∈ ((b.retain m).retain n).notes := by
  simp [Bank.retain]
  exact or_congr_right or_comm

/-- Witness: both sides of `retain_comm` hold at once (a note one writer retains is held in either order of the two retains). -/
example : (n0 ∈ ((empty.retain n0).retain n0).notes) ∧ (n0 ∈ ((empty.retain n0).retain n0).notes) :=
  ⟨(retain_comm empty n0 n0 n0).mpr (by simp [empty, Bank.retain, n0]),
   by simp [empty, Bank.retain, n0]⟩

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

/-- Witness: retaining a derived note that derives from a note the bank holds is accepted, so the hypothesis of `retainDerived_cites` can be met. -/
example : (one.retainDerived ⟨1, .cls "x", "t", [0]⟩).isSome = true := by decide

/-- Witness: a derived note that derives from nothing is refused (there the hypothesis is not met, as intended). -/
example : (one.retainDerived ⟨1, .cls "x", "t", []⟩).isSome = false := by decide

end VbmMemory
