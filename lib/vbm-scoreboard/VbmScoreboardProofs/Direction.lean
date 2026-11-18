import VbmScoreboard.Direction
/-! # The direction order, proved -/
namespace VbmScoreboard

/-- A value is at least as good as itself. -/
theorem Direction.better_refl (d : Direction) (a : Nat) : d.better a a = true := by
  cases d <;> simp [Direction.better]

/-- Of two values, one is at least as good as the other: the order is total, so a floor can always be compared with a reading. -/
theorem Direction.better_total (d : Direction) (a b : Nat) : (d.better a b || d.better b a) = true := by
  cases d <;> simp [Direction.better] <;> omega

/-- The order is transitive: a floor that held against a floor holds against what that floor held against. -/
theorem Direction.better_trans (d : Direction) (a b c : Nat) (h1 : d.better a b = true) (h2 : d.better b c = true) : d.better a c = true := by
  cases d <;> simp [Direction.better] at * <;> omega

/-- The two directions are opposite: a strictly better value in one direction is strictly worse in the other. -/
theorem Direction.better_opposite (a b : Nat) : (Direction.higher.better a b = true ∧ Direction.lower.better a b = false) ↔ b < a := by
  simp [Direction.better]; omega

-- Non-vacuity witnesses: the hypotheses of the theorems above can hold, and each direction means what it says.
example : Direction.higher.better 3 2 = true := by decide
example : Direction.lower.better 2 3 = true := by decide
example : Direction.higher.better 2 3 = false := by decide
example : Direction.lower.better 3 2 = false := by decide
example : Direction.higher.better 4 4 = true ∧ Direction.lower.better 4 4 = true := by decide

end VbmScoreboard
