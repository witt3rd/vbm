/-! # Named limits, the size of a number, and the key carrier

The limits that protect the machine (`docs/spec.md`, "Named limits"): each is a field and a parameter of the entry points that take external data, never a hidden constant. `Rat.bits` measures an input number against `maxBits`. `Key` is the carrier of atom keys: a strict total order with a decidable `<`, with instances for `Nat`, `Int` and `Rat`. -/
namespace VbmProb

/-- The bounds a caller states for external data. -/
structure Limits where
  /-- The most atoms of a distribution. -/
  maxAtoms : Nat
  /-- The most bits (numerator plus denominator) of an input rational. -/
  maxBits : Nat
  /-- The largest fixed-point scale. -/
  maxScale : Nat
  deriving DecidableEq, Repr

/-- The defaults: 1024 atoms, 512 bits, scale 10^18. -/
def Limits.default : Limits where
  maxAtoms := 1024
  maxBits := 512
  maxScale := 1000000000000000000

/-- The number of binary digits of `n`: 0 for 0, else `log2 n + 1`. -/
def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- The size of a rational: the bits of its numerator's magnitude plus the bits of its denominator. -/
def _root_.Rat.bits (q : Rat) : Nat :=
  bitLength q.num.natAbs + bitLength q.den

/-! ## The carrier of atom keys -/
/-- A strict total order with decidable `<`, the carrier of the keys of a distribution. -/
class Key (α : Type) extends LT α where
  /-- `<` is decidable. -/
  decLt : DecidableRel (α := α) (· < ·)
  /-- No key is below itself. -/
  lt_irrefl : ∀ a : α, ¬ a < a
  /-- `<` is transitive. -/
  lt_trans : ∀ {a b c : α}, a < b → b < c → a < c
  /-- Any two keys are comparable. -/
  lt_trichotomy : ∀ a b : α, a < b ∨ a = b ∨ b < a

/-- The decision procedure of a key's `<`. -/
instance Key.instDecidableLt {α : Type} [Key α] : DecidableRel (α := α) (· < ·) := Key.decLt

/-- `a ≤ b` on keys means `¬ b < a`. -/
def Key.le {α : Type} [Key α] (a b : α) : Prop := ¬ b < a

instance : Key Nat where
  decLt := fun a b => inferInstanceAs (Decidable (a < b))
  lt_irrefl := Nat.lt_irrefl
  lt_trans := Nat.lt_trans
  lt_trichotomy := Nat.lt_trichotomy

instance : Key Int where
  decLt := fun a b => inferInstanceAs (Decidable (a < b))
  lt_irrefl := Int.lt_irrefl
  lt_trans := Int.lt_trans
  lt_trichotomy := Int.lt_trichotomy

instance : Key Rat where
  decLt := fun a b => inferInstanceAs (Decidable (a < b))
  lt_irrefl := fun _ => Rat.lt_irrefl
  lt_trans := fun {a b c} hab hbc => Rat.not_le.mp (fun h =>
    Rat.not_le.mpr hab (Rat.le_trans (Rat.le_of_lt hbc) h))
  lt_trichotomy := fun a b => by
    cases Rat.le_total (a := a) (b := b) with
    | inl h => cases Rat.le_iff_lt_or_eq.mp h with
      | inl h => exact .inl h
      | inr h => exact .inr (.inl h)
    | inr h => cases Rat.le_iff_lt_or_eq.mp h with
      | inl h => exact .inr (.inr h)
      | inr h => exact .inr (.inl h.symm)

end VbmProb
