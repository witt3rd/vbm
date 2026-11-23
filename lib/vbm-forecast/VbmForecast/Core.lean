/-! # vbm-forecast: the skeleton (S0)

Forecast verification: proper scoring rules (Brier, logarithmic, pinball and interval scores), calibration and reliability, and the comparison of two probabilistic forecasts, in exact arithmetic or within a stated epsilon. This file is the module root; the specification (`docs/spec.md`) is written first, and the first real definitions land in S1. -/
namespace VbmForecast

/-- The library's name, as the registry and the scorecard spell it. -/
def libraryName : String := "vbm-forecast"

end VbmForecast
