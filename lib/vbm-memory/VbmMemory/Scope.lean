/-! # Scope: whose memory a note belongs to

A memory is partitioned into scopes. An agent reads from, and writes to, the scopes it is attached to: a **class** (general knowledge of the kind of agent it is), a **domain** (a project, a tool, a system, a person) and, only for an agent that bears one, an **identity**. A class, a domain and an identity are distinct kinds of scope even under one name. This is the first slice; the notes, the bank, the recall contract and supersession follow (docs/decisions/0001-vbm-memory.md). -/
namespace VbmMemory

/-- A scope of memory, named by a string. -/
inductive Scope where
  | cls (id : String)
  | domain (id : String)
  | identity (id : String)
  deriving DecidableEq, Repr

end VbmMemory
