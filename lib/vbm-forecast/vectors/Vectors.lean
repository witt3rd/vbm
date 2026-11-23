import VbmForecast
/-! # S7: the known-answer vectors (`docs/spec.md`, section 10)

Each vector is an `example` over the real functions, checked when this file is compiled, and printed by `main` as `ID KEY VALUE` lines.
`scripts/test_vectors.sh` re-derives the same lines with an independent reference (shell integer arithmetic, not this library) and compares them. -/
open VbmForecast

/-- The limits of the vectors; `minEvents` is set per vector. -/
def lim (minEvents : Nat) : Limits :=
  { maxEvents := 1000000, maxOutcomes := 1024, maxBins := 1024, maxResamples := 10000, minEvents := minEvents, logBits := 24, tol := 0 }

/-- `x` is `ok a` (`Except` has no decidable equality). -/
def okIs {α : Type} [BEq α] (x : Except Refusal α) (a : α) : Bool :=
  match x with
  | .ok v => v == a
  | .error _ => false

/-- V9's sample: forecasts and outcomes at `s = 10`. -/
def v9 : List BinaryEvent :=
  [⟨2, false⟩, ⟨3, true⟩, ⟨4, false⟩, ⟨7, true⟩, ⟨8, true⟩, ⟨9, false⟩, ⟨10, true⟩]

/-- V12's differences, their draws, and a pair of loss lists with those differences. -/
def v12d : List Int := [2, -1, 3]
def v12draws : List Nat := [0, 0, 0, 1, 1, 1, 2, 2, 2, 0, 1, 2]
def v12a : List Int := [2, 0, 3]
def v12b : List Int := [0, 1, 0]

-- V1, V2: binary Brier
example : brierBinary 10 ⟨7, true⟩ = 9 := by decide
example : brierBinary 10 ⟨7, false⟩ = 49 := by decide
example : okIs (brierBinaryV 10 ⟨7, true⟩) 9 = true := by decide +kernel
-- V3: categorical Brier
example : brierCategorical 10 [5, 3, 2] 0 = 38 := by decide
-- V4: propriety
example : expBrierBinary 10 7 5 = 250 := by decide
example : expBrierBinary 10 7 7 = 210 := by decide
example : expBrierBinary 10 7 5 - expBrierBinary 10 7 7 = 10 * ((5 - 7) * (5 - 7)) := by decide
-- V5: RPS
example : rps 10 ⟨[1, 2, 3], [5, 3, 2], 2⟩ = 29 := by decide
-- V6: pinball
example : pinball 10 ⟨9, 5, 8⟩ = 27 := by decide
example : pinball 10 ⟨9, 5, 3⟩ = 2 := by decide
-- V7: interval
example : intervalScore 10 ⟨1, 2, 6, 9⟩ = 68 := by decide
example : 2 * (pinball 10 ⟨1, 2, 9⟩ + pinball 10 ⟨9, 6, 9⟩) = 68 := by decide
-- V8: log comparison and the enclosure of log2 (1/2)
example : natProd [5, 8] = 40 := by decide
example : natProd [6, 4] = 24 := by decide
example : logCompare [5, 8] [6, 4] = .gt := by decide
example : okIs (log2Enclosure 1 2 3) (-8, -8) = true := by decide +kernel
-- V9: reliability
example : table [0, 5, 10] v9 = [⟨0, 5, 3, 1, 9⟩, ⟨5, 10, 4, 3, 34⟩] := by decide +kernel
-- V10: calibration error 5/70
example : calibNum 10 (table [0, 5, 10] v9) = 5 := by decide
-- V11: calibration in the large
example : sumInt (v9.map (·.p)) = 43 := by decide
example : (v9.map wHit).sum = 4 := by decide
-- V12: bootstrap, sort, interval
example : okIs (bootstrapSums (lim 3) v12d 4 v12draws) [6, -3, 9, 4] = true := by decide +kernel
example : sortInts [6, -3, 9, 4] = [-3, 4, 6, 9] := by simp [sortInts, List.mergeSort]
-- V13, V14: the verdict
example : verdict (lim 30) 3 4 (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩) = .refused 3 30 := by decide
example : verdict (lim 3) 3 4 (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩) = .inconclusive := by decide

/-- Print a ratio as `num/den`. -/
def showRatio (r : Ratio) : String := s!"{r.num}/{r.den}"

/-- Print an `Except` result through a printer. -/
def showEx {α : Type} (f : α → String) : Except Refusal α → String
  | .ok a => f a
  | .error _ => "refused"

def showV : Verdict → String
  | .better => "better"
  | .worse => "worse"
  | .inconclusive => "inconclusive"
  | .refused n m => s!"refused {n} {m}"

def showOrd : Ordering → String
  | .lt => "lt"
  | .eq => "eq"
  | .gt => "gt"

def showRows (rs : List Row) : String := " ".intercalate (rs.map fun r => s!"{r.lo},{r.hi},{r.n},{r.hits},{r.sumP}")

def showCi (c : Ratio × Ratio) : String := s!"{showRatio c.1} {showRatio c.2}"

def main : IO Unit := do
  IO.println s!"V1 brier {brierBinary 10 ⟨7, true⟩}"
  IO.println s!"V2 brier {brierBinary 10 ⟨7, false⟩}"
  IO.println s!"V3 brier {brierCategorical 10 [5, 3, 2] 0}"
  IO.println s!"V4 e57 {expBrierBinary 10 7 5}"
  IO.println s!"V4 e77 {expBrierBinary 10 7 7}"
  IO.println s!"V5 rps {rps 10 ⟨[1, 2, 3], [5, 3, 2], 2⟩}"
  IO.println s!"V6 pinball {pinball 10 ⟨9, 5, 8⟩} {pinball 10 ⟨9, 5, 3⟩}"
  IO.println s!"V7 interval {intervalScore 10 ⟨1, 2, 6, 9⟩} {2 * (pinball 10 ⟨1, 2, 9⟩ + pinball 10 ⟨9, 6, 9⟩)}"
  IO.println s!"V8 products {natProd [5, 8]} {natProd [6, 4]} {showOrd (logCompare [5, 8] [6, 4])}"
  IO.println s!"V8 enclosure {showEx (fun (p : Int × Int) => s!"{p.1} {p.2}") (log2Enclosure 1 2 3)}"
  IO.println s!"V9 rows {showEx showRows (reliability 10 (lim 3) [0, 5, 10] v9)} N={v9.length}"
  IO.println s!"V10 calib {showEx showRatio (calibrationError 10 (lim 3) [0, 5, 10] v9)}"
  IO.println s!"V11 citl {showEx (fun (t : Ratio × Ratio × Ratio) => s!"{showRatio t.1} {showRatio t.2.1} {showRatio t.2.2}") (citl 10 (lim 3) v9)}"
  IO.println s!"V12 sums {showEx toString (bootstrapSums (lim 3) v12d 4 v12draws)}"
  IO.println s!"V12 sorted {sortInts [6, -3, 9, 4]}"
  IO.println s!"V12 ci {showEx showCi (ci [6, -3, 9, 4] 3 2 10)}"
  IO.println s!"V12 mean {showEx showRatio (diffMean v12d)}"
  let cmp (m : Nat) := showEx (fun (t : Verdict × Ratio × Option (Ratio × Ratio)) =>
    s!"{showV t.1} {showRatio t.2.1} {match t.2.2 with | some c => showCi c | none => "none"}")
    (compareForecasters (lim m) 10 2 4 v12a v12b v12draws)
  IO.println s!"V13 verdict {showV (verdict (lim 30) 3 4 (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩))}"
  IO.println s!"V13 compare {cmp 30}"
  IO.println s!"V14 verdict {showV (verdict (lim 3) 3 4 (⟨-3, 3, by decide⟩, ⟨9, 3, by decide⟩))}"
  IO.println s!"V14 compare {cmp 3}"
