import VbmMemory.Bank

/-! # Attach: the scopes an instance is attached to

An agent runs as an instance, and an instance is attached to a set of scopes: its class (always), the domains it works in, and an identity if it bears one. What it is attached to is all it
reads from and all it may write to, and it writes nowhere else. An agent without an identity has no identity scope and cannot write one. There is deliberately no field for what an
instance is oriented around: that is disposition, recorded in its instructions, not structure. -/

namespace VbmMemory

/-- What an instance is attached to: its class, the domains it works in, and an identity if it has one. -/
structure Attach where
  profile : String
  identity : Option String := none
  domains : List String := []

/-- The scopes an instance reads from and writes to. -/
def Attach.scopes (a : Attach) : List Scope :=
  Scope.cls a.profile :: (a.domains.map Scope.domain ++ (a.identity.map Scope.identity).toList)

/-- Retain a note into a bank, but only in a scope the instance is attached to. -/
def Attach.retain (a : Attach) (b : Bank) (n : Note) : Option Bank :=
  if n.scope ∈ a.scopes then some (b.retain n) else none

end VbmMemory
