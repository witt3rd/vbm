import VbmRng.Core
/-! # The skeleton's one claim, proved, with its witness -/
namespace VbmRng

/-- The library has a name. -/
theorem libraryName_nonempty : libraryName ≠ "" := by decide

-- Non-vacuity witness: the name is the repository's.
example : libraryName = "vbm-rng" := rfl

end VbmRng
