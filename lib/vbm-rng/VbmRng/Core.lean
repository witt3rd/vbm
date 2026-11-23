/-! # vbm-rng: the skeleton (S0)

Deterministic, splittable pseudo-random generators with specified streams: the same seed always gives the same bytes, and exactly reproducible sampling primitives (uniform integers in a range, uniform fractions in exact arithmetic) for simulation and experiments. This file is the module root; the specification (`docs/spec.md`) is written first, and the first real definitions land in S1. -/
namespace VbmRng

/-- The library's name, as the registry and the scorecard spell it. -/
def libraryName : String := "vbm-rng"

end VbmRng
