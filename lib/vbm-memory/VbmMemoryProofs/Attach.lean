import VbmMemory

/-! # Proofs of attachment: writes are confined to the attached scopes

* **An instance with no identity has no identity scope** (`worker_no_identity_scope`) and cannot write an identity's memory (`worker_cannot_write_identity`).
* **An identity-bearing instance has its identity's scope** (`identity_scope_of_some`).
* **Writes are confined to the attached scopes** (`write_confined`).

A theorem with a hypothesis carries a witness beside it that its hypothesis can hold. -/
namespace VbmMemory

/-- **An instance with no identity has no identity scope.** -/
theorem worker_no_identity_scope (a : Attach) (h : a.identity = none) (i : String) :
    Scope.identity i ∉ a.scopes := by
  simp [Attach.scopes, h]

/-- Witness: an instance with no identity exists, so the hypothesis of `worker_no_identity_scope` can hold. -/
example : (⟨"x", none, ["d"]⟩ : Attach).identity = none := rfl

/-- An instance whose identity is `some i` has `i`'s scope among its scopes. -/
theorem identity_scope_of_some (a : Attach) (i : String) (h : a.identity = some i) :
    Scope.identity i ∈ a.scopes := by
  simp [Attach.scopes, h]

/-- Witness: an instance that bears an identity exists, so the hypothesis of `identity_scope_of_some` can hold. -/
example : ∃ (a : Attach) (i : String), a.identity = some i ∧ Scope.identity i ∈ a.scopes :=
  ⟨⟨"x", some "i", []⟩, "i", rfl, identity_scope_of_some _ _ rfl⟩

/-- **Writes are confined to the attached scopes.** -/
theorem write_confined (a : Attach) (b : Bank) (n : Note) (b' : Bank) (h : a.retain b n = some b') :
    n.scope ∈ a.scopes := by
  unfold Attach.retain at h
  split at h
  · assumption
  · simp at h

/-- Witness: the hypothesis of `write_confined` can hold: an instance attached to a domain retains a note in that domain, and the bank it yields is the old one with the note appended. -/
example : ∃ (a : Attach) (b b' : Bank) (n : Note),
    a.retain b n = some b' ∧ n.scope ∈ a.scopes ∧ b'.notes = b.notes ++ [n] :=
  ⟨⟨"x", none, ["d"]⟩, ⟨[]⟩, Bank.retain ⟨[]⟩ ⟨0, Scope.domain "d", "s", []⟩,
    ⟨0, Scope.domain "d", "s", []⟩, by rfl, by decide, rfl⟩

/-- **An instance with no identity cannot write an identity's memory.** -/
theorem worker_cannot_write_identity (a : Attach) (b : Bank) (n : Note) (i : String)
    (hw : a.identity = none) (hn : n.scope = Scope.identity i) : a.retain b n = none := by
  cases h : a.retain b n with
  | none => rfl
  | some b' =>
    have := write_confined a b n b' h
    rw [hn] at this
    exact absurd this (worker_no_identity_scope a hw i)

/-- Witness: the hypotheses of `worker_cannot_write_identity` can hold, and the write is refused. -/
example : (⟨"x", none, ["d"]⟩ : Attach).retain ⟨[]⟩ ⟨0, .identity "i", "s", []⟩ =
    none := by decide

end VbmMemory
