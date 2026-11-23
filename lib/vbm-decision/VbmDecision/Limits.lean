import VbmDecision.Prob
/-! # Named limits (S1b)

Only limits that protect the machine or the money, or that prevent a named harm (spec section 8). `scale`, `Prob.entryError` and `Decimal.maxExponent` are defined with the probability type (`VbmDecision/Prob`); the proofs state their values with the rest. -/
namespace VbmDecision

/-- Questions in one request: a request that bills for dozens of questions at once by accident. -/
def maxQuestions : Nat := 32

/-- Options of a `choice` question: unbounded work and an epsilon that grows until the sum rule checks nothing. -/
def maxOptions : Nat := 64

/-- Levels of a `score` question: the same harm, for a score scale. -/
def maxLevels : Nat := 64

/-- Parts of a request's state: a state that is an unbounded list of parts (money, memory). -/
def maxStateParts : Nat := 256

/-- Nesting depth of a decoded value: a deeply nested value exhausting the stack in a decoder. -/
def maxNestingDepth : Nat := 32

/-- Cases in a calibration sample, at least: a threshold tuned on a handful of cases is noise. -/
def minSample : Nat := 100

/-- Cases of each label, at least: a one-sided sample meets every target at every threshold. -/
def minPerClass : Nat := 10

/-- Cases at or above a threshold, at least: a threshold chosen because the top two cases happened to be right. -/
def minSupport : Nat := 30

/-- Cases in a calibration sample, at most: the reference definition is quadratic, so unbounded work. -/
def maxSample : Nat := 10000

end VbmDecision
