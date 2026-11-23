/-! # vbm-decision: the skeleton (S0)

A typed decision-model layer: the wire contract of a decisions API (choice, noul, score and box questions), the typed answers with their probabilities, a threshold truth table that fails closed, and per-model calibration of thresholds. This file is the module root; the specification (`docs/spec.md`) is written first, and the first real definitions land in S1. -/
namespace VbmDecision

/-- The library's name, as the registry and the scorecard spell it. -/
def libraryName : String := "vbm-decision"

end VbmDecision
