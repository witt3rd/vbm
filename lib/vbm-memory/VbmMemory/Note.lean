import VbmMemory.Scope

/-! # Note: one retained item of memory

A note is what a memory keeps: where it belongs (its scope), where it came from (an item, a journal, a line: recorded as a string, uninterpreted here), and the notes it derives from. An
**experience** note derives from nothing (`cites` is empty); a **derived** note (a consolidation) derives from other notes. The text itself is verbatim and belongs to the implementation; this
module gives a note its identity (`id`) and its place, and says nothing about how a note is written. -/

namespace VbmMemory

/-- A retained note: its identifier, its scope, where it came from, and the `id`s of the notes it derives from (none for an experience note). -/
structure Note where
  id : Nat
  scope : Scope
  source : String
  cites : List Nat
  deriving DecidableEq, Repr

end VbmMemory
