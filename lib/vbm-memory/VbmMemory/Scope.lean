/-! # Scope: whose memory a note belongs to

A memory is partitioned into scopes. An agent reads from, and writes to, the scopes it is attached to: a **class** (general knowledge of being, say, a worker), a **domain** (a
project, a tool, a system, a person) and, only for an agent that bears one, an **identity**. This is the first slice; the notes, the recall contract and supersession follow. -/
namespace VbmMemory

/-- A scope of memory. -/
inductive Scope where
  | cls (id : String)
  | domain (id : String)
  | identity (id : String)
  deriving DecidableEq, Repr

end VbmMemory
