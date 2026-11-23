import VbmProb.Refusal
/-! # Apportionment: the largest-remainder method over natural numbers

`apportion n ws` splits `n` units in proportion to the weights `ws`: each index gets the floor of its exact share, and the units left over go one each to the indices with the largest remainders, the EARLIEST index first among equal remainders (`docs/spec.md`, "Fixed point"). Integers only, total, and the only refusal is a total weight of 0. The scale is passed as its unit count (`Scale.n`), so this module needs no `Prob` and no `Scale`. -/
namespace VbmProb

namespace Apportion

/-- The award order on indices: a larger remainder first; among equal remainders the earlier index first. -/
def before (r : Nat → Nat) (a b : Nat) : Bool := decide (r b < r a) || (r a == r b && decide (a ≤ b))

/-- The floor of the exact share of index `i`: `wᵢ·n / W`. -/
def floorAt (n : Nat) (ws : List Nat) (i : Nat) : Nat := ws.getD i 0 * n / ws.sum

/-- The remainder of the exact share of index `i`: `wᵢ·n % W`. -/
def remAt (n : Nat) (ws : List Nat) (i : Nat) : Nat := ws.getD i 0 * n % ws.sum

/-- All indices of `ws` in award order (the sort is `List.mergeSort`). -/
def order (n : Nat) (ws : List Nat) : List Nat := (List.range ws.length).mergeSort (before (remAt n ws))

/-- The number of units left after every floor: `n − Σ floor`. -/
def extra (n : Nat) (ws : List Nat) : Nat := n - ((List.range ws.length).map (floorAt n ws)).sum

/-- The indices that receive one more unit: the first `extra` of the award order. -/
def chosen (n : Nat) (ws : List Nat) : List Nat := (order n ws).take (extra n ws)

/-- The result when the total weight is not 0: the floor of each share, plus one for each chosen index. -/
def units (n : Nat) (ws : List Nat) : List Nat :=
  (List.range ws.length).map fun i => floorAt n ws i + if i ∈ chosen n ws then 1 else 0

end Apportion

/-- Largest remainder: `n` units shared in proportion to `ws`, the same length as `ws` and summing to `n`.
Refuses `zeroTotalWeight` when every weight is 0 (or there are none). -/
def apportion (n : Nat) (ws : List Nat) : Except Refusal (List Nat) :=
  if ws.sum = 0 then .error .zeroTotalWeight
  else .ok (Apportion.units n ws)

end VbmProb
