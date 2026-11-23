import VbmDecision.Prob
/-! # The types (S2)

Types only, no logic: the decoded wire value `J`, the questions and answers, the request and response, the thresholds and their binding, and the outcomes. The kind tags and the three one-line tag maps are the only functions. -/
namespace VbmDecision

/-- A position on a score scale: millionths of a level index. Its bound depends on the number of levels. -/
abbrev Pos := Nat

/-- A decoded JSON value. An object is an ordered list: order and duplicates are kept from the bytes. -/
inductive J where
  | null
  | bool (b : Bool)
  | num (d : Decimal)
  | str (s : String)
  | arr (xs : List J)
  | obj (kvs : List (String × J))
  deriving Repr

/-- A state is opaque to the library. -/
abbrev State := J

/-- A box, as fractions of the image's height (top, bottom) and width (left, right) from the top-left corner. -/
structure Box where
  top : Prob
  bottom : Prob
  left : Prob
  right : Prob
  deriving DecidableEq, Repr

/-- The four kinds of question. -/
inductive Kind where
  | noul | choice | score | box
  deriving DecidableEq, Repr

/-- A typed question. -/
inductive Question where
  | noul (instructions : String) (criteria : Option (String × String))
  | choice (instructions : String) (options : List (String × Option String))
  | score (instructions : String) (levels : List String)
  | box (instructions : String)
  deriving DecidableEq, Repr

/-- A typed answer, with its probabilities. -/
inductive Answer where
  | noul (p : Prob)
  | choice (selected : String) (probs : List (String × Prob)) (confidence : Prob)
  | score (x : Pos) (confidence : Prob) (probs : List Prob) (legend : List String)
  | box (b : Box) (confidence : Prob)
  deriving DecidableEq, Repr

/-- The kind of a question. -/
def Question.kindOf : Question → Kind
  | .noul .. => .noul
  | .choice .. => .choice
  | .score .. => .score
  | .box .. => .box

/-- The kind of an answer. -/
def Answer.kindOf : Answer → Kind
  | .noul .. => .noul
  | .choice .. => .choice
  | .score .. => .score
  | .box .. => .box

/-- What a model's answers cost; the cost is an exact decimal, never converted. -/
structure Usage where
  inputTokens : Nat
  outputTokens : Nat
  cost : Decimal
  deriving DecidableEq, Repr

/-- A response; `model` is the dated snapshot name. -/
structure Response where
  id : String
  model : String
  provider : String
  answers : List (String × Answer)
  usage : Usage
  deriving DecidableEq, Repr

/-- A request: the model string as sent, the state, and the named questions in wire order. -/
structure Request where
  model : String
  state : State
  questions : List (String × Question)
  deriving Repr

/-- Thresholds, one shape per kind. -/
inductive Thresholds where
  | noul (no yes : Prob)
  | choice (minProb minMargin : Prob)
  | score (lo hi : Pos) (minConfidence : Prob)
  | box (minConfidence : Prob)
  deriving DecidableEq, Repr

/-- The kind of a set of thresholds. -/
def Thresholds.kindOf : Thresholds → Kind
  | .noul .. => .noul
  | .choice .. => .choice
  | .score .. => .score
  | .box .. => .box

/-- Thresholds bound to one model string and, optionally, the snapshot they were calibrated on. -/
structure Binding where
  model : String
  snapshot : Option String
  thresholds : Thresholds
  deriving DecidableEq, Repr

/-- What was sent and what the response says. -/
structure Context where
  requested : String
  snapshot : String
  deriving DecidableEq, Repr

/-- A decision of the truth table. -/
inductive Decision where
  | yes | no
  | option (name : String)
  | below | within | above
  | found (b : Box)
  deriving DecidableEq, Repr

/-- Why the model was heard and did not clear the bar. -/
inductive AbstainReason where
  | uncertainBand | lowProbability | lowMargin | lowConfidence
  deriving DecidableEq, Repr

/-- The outcome of a decision, over the type `ρ` of refusals (the spec's `Refusal`, which lands with the refusal codes). -/
inductive Outcome (ρ : Type) where
  | decided (d : Decision)
  | abstain (r : AbstainReason)
  | refused (r : ρ)
  deriving DecidableEq, Repr

end VbmDecision
