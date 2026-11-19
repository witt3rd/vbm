import VbmProb.Limits
/-! # Canonical weight lists: sort and merge (`canon`)

`canon` puts a list of keyed weights in canonical form: the keys are sorted by `List.mergeSort` (the only sort, from `Init`), then neighbours with equal keys are merged by adding their weights. The merge is structural recursion on the tail. Only `Key` is needed: equal neighbours are those where the earlier key is not below the later one (after the sort, that means the keys are equal). The properties (DS4) are proved in `VbmProbProofs.Dist.Canon`. -/
namespace VbmProb

/-- `a ≤ b` on keys as a `Bool`, the order the sort uses: `¬ b < a`. -/
def keyLe {α : Type} [Key α] (a b : α) : Bool := !decide (b < a)

/-- Merge the equal-keyed neighbours of a sorted list, carrying the current atom. -/
def canonMerge {α : Type} [Key α] (cur : α × Rat) : List (α × Rat) → List (α × Rat)
  | [] => [cur]
  | y :: ys =>
    if cur.1 < y.1 then cur :: canonMerge y ys
    else canonMerge (cur.1, cur.2 + y.2) ys

/-- Merge the equal-keyed neighbours of a sorted list. -/
def canonMergeAll {α : Type} [Key α] : List (α × Rat) → List (α × Rat)
  | [] => []
  | x :: xs => canonMerge x xs

/-- The canonical form of keyed weights: sorted by key, equal keys merged by adding their weights. -/
def canon {α : Type} [Key α] (ws : List (α × Rat)) : List (α × Rat) :=
  canonMergeAll (ws.mergeSort (fun a b => keyLe a.1 b.1))

end VbmProb
