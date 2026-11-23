import VbmRng.Below
/-! # Shuffle (S7)

`shuffleWith fuel xs st` is Fisher-Yates from the back: for `i = L - 1` down to `1` it draws `j` below `i + 1` with `uniformBelowWith fuel` and swaps the elements at `i` and `j`. A refusal of any draw is the shuffle's refusal and no partial list is returned. The empty list and singletons consume no word. The properties S1-S4 are proved in `VbmRngProofs/Shuffle.lean`; the uniformity of the permutation (S5) is not claimed. -/
namespace VbmRng

/-- The loop: `shuffleGo fuel i a st` shuffles the positions `i, i - 1, ..., 1` of `a` (the draw at position `i` is below `i + 1`). -/
def shuffleGo {α : Type} (fuel : Nat) : Nat → Array α → Stream → DrawWith Stream (Array α)
  | 0, a, st => .ok (a, st)
  | i + 1, a, st =>
    match uniformBelowWith fuel (i + 2) st with
    | .error e => .error e
    | .ok (j, st') => shuffleGo fuel i (a.swapIfInBounds (i + 1) j) st'

/-- A shuffled list from the stream with at most `fuel` words per draw, or the first refusal. -/
def shuffleWith {α : Type} (fuel : Nat) (xs : List α) (st : Stream) : DrawWith Stream (List α) :=
  match shuffleGo fuel (xs.length - 1) xs.toArray st with
  | .error e => .error e
  | .ok (a, st') => .ok (a.toList, st')

/-- A shuffled list with the default fuel `rejectionFuel`. -/
def shuffle {α : Type} (xs : List α) (st : Stream) : DrawWith Stream (List α) := shuffleWith rejectionFuel xs st

end VbmRng
