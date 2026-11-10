import VbmMemory.Note

/-! # Bank: the notes retained so far, mono

A bank is the memory itself: a finite list of notes, and the operations a writer performs on it. Retaining appends; it never rewrites, reorders or drops what is already there, so no two writers need to merge. A recall considers exactly the notes eligible for it: those whose scope is one of the scopes asked for. Retaining a derived note is allowed only when it derives from notes the bank already holds. -/

namespace VbmMemory

/-- The notes retained so far. -/
structure Bank where
  notes : List Note
  deriving Repr

/-- Retain a note: append it. -/
def Bank.retain (b : Bank) (n : Note) : Bank :=
  { notes := b.notes ++ [n] }

/-- The notes a recall may consider: those retained in one of the scopes asked for. -/
def Bank.eligible (b : Bank) (ss : List Scope) : List Note :=
  b.notes.filter fun n => decide (n.scope ∈ ss)

/-- Retain a derived note (a consolidation): it must derive from at least one note, and from notes the bank already holds. -/
def Bank.retainDerived (b : Bank) (n : Note) : Option Bank :=
  if n.cites ≠ [] ∧ ∀ c ∈ n.cites, ∃ m ∈ b.notes, m.id = c then some (b.retain n) else none

end VbmMemory
