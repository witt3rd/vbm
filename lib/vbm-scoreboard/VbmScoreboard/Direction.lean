/-! # Which way is better

A metric is better when it is higher or when it is lower; a floor is the worst value a metric may ever have again. `better d a b` says that the value `a` is at least as good as the value `b` in direction `d`. -/
namespace VbmScoreboard

inductive Direction where
  | higher
  | lower
  deriving DecidableEq, Repr

/-- `a` is at least as good as `b`. -/
def Direction.better (d : Direction) (a b : Nat) : Bool :=
  match d with
  | .higher => decide (b ≤ a)
  | .lower => decide (a ≤ b)

end VbmScoreboard
