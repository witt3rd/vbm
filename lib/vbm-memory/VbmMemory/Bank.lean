import VbmMemory.Note

/-! # Bank: the notes retained so far

A bank is the memory itself: a finite list of notes, in the order they were retained, and the operations a writer performs on it. Retaining appends; it never rewrites or drops what is already there, and the notes already retained stay a prefix of the notes the bank then holds, so no two writers need to merge. Two writers retaining at once leave the same notes in either order: the two results are permutations of each other, not equal lists. A recall considers exactly the notes eligible for it: those whose scope is one of the scopes asked for. Retaining a derived note is allowed only when it derives from notes the bank already holds, and a citation names a note by its `id`, so it names exactly one held note only in a bank whose notes have distinct `id`s (`Bank.IdsUnique`); where two notes share an `id` a citation is ambiguous, and the specification says nothing about which of them an implementation must resolve it to. -/

namespace VbmMemory

/-- The notes retained so far, oldest first. -/
structure Bank where
  notes : List Note
  deriving Repr

/-- The `id`s of the notes a bank holds, oldest first. -/
def Bank.Ids (b : Bank) : List Nat :=
  b.notes.map Note.id

/-- **A bank whose notes have distinct `id`s**: no two of its notes share one, so an `id` names at most one note of it. -/
def Bank.IdsUnique (b : Bank) : Prop :=
  b.Ids.Nodup

/-- An `id` no note of the bank carries: a note retained with it keeps the `id`s distinct. -/
def Bank.IdFresh (b : Bank) (i : Nat) : Prop :=
  i ∉ b.Ids

/-- Retain a note: append it. Every note already retained stays, in its order, as a prefix. -/
def Bank.retain (b : Bank) (n : Note) : Bank :=
  { notes := b.notes ++ [n] }

/-- The notes a recall may consider: those retained in one of the scopes asked for, oldest first. -/
def Bank.eligible (b : Bank) (ss : List Scope) : List Note :=
  b.notes.filter fun n => decide (n.scope ∈ ss)

/-- Retain a derived note (a consolidation): it must derive from at least one note, and from notes the bank already holds. A citation matches a note by its `id`; where two notes of the bank share an `id` the citation names either of them, and only in a bank whose `id`s are distinct (`Bank.IdsUnique`) does it name exactly one held note. -/
def Bank.retainDerived (b : Bank) (n : Note) : Option Bank :=
  if n.cites ≠ [] ∧ ∀ c ∈ n.cites, ∃ m ∈ b.notes, m.id = c then some (b.retain n) else none

end VbmMemory
