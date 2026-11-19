import VbmForecast.Rep
/-! # S5: calibration

Reliability bins, the reliability table, the calibration error and calibration in the large (`docs/spec.md`, section 4). All counts are exact `Nat`; all rates are unreduced `Ratio`s. Bin `j` is `[e_j, e_{j+1})`, the last bin also contains `s`. -/
namespace VbmForecast

/-- The bin search from bin index `j` over the upper edges `ups`: the first bin whose upper edge is above `p`; the last bin also takes `p` equal to its upper edge. -/
def binFrom : Nat → List Nat → Int → Option Nat
  | _, [], _ => none
  | j, [e], p => if p ≤ (e : Int) then some j else none
  | j, e :: r :: rs, p => if p < (e : Int) then some j else binFrom (j + 1) (r :: rs) p

/-- The bin of a probability numerator `p` over `edges = e_0 :: ups`: `none` below `e_0` or above the last edge. -/
def binOf (edges : List Nat) (p : Int) : Option Nat :=
  match edges with
  | [] => none
  | e :: ups => if (e : Int) ≤ p then binFrom 0 ups p else none

/-- Bin `k` over the lower edge `prev` and the upper edges `ups` is `[prev, u_0)` for `k = 0`; the last bin also contains its upper edge. -/
def InB : Nat → List Nat → Int → Nat → Prop
  | _, [], _, _ => False
  | prev, u :: us, p, 0 => (prev : Int) ≤ p ∧ (p < (u : Int) ∨ (us = [] ∧ p = (u : Int)))
  | _, u :: us, p, k + 1 => InB u us p k

/-- `p` lies in bin `j` of `edges`. -/
def InBin (edges : List Nat) (j : Nat) (p : Int) : Prop :=
  match edges with
  | [] => False
  | e :: ups => InB e ups p j

/-- One row of the reliability table: bin `[lo, hi)`, its event count, hit count and the sum of forecast numerators. -/
structure Row where
  lo : Nat
  hi : Nat
  n : Nat
  hits : Nat
  sumP : Nat
  deriving DecidableEq, Repr

/-- The weight of an event in the hit count. -/
def wHit (e : BinaryEvent) : Nat := if e.hit then 1 else 0

/-- The weight of an event in the sum of forecast numerators. -/
def wProb (e : BinaryEvent) : Nat := e.p.toNat

/-- The total weight of the events that fall in bin `j`. -/
def wBin (edges : List Nat) (j : Nat) (w : BinaryEvent → Nat) : List BinaryEvent → Nat
  | [] => 0
  | e :: es => (if binOf edges e.p = some j then w e else 0) + wBin edges j w es

/-- The reliability row of bin `j`. -/
def rowAt (edges : List Nat) (es : List BinaryEvent) (j : Nat) : Row :=
  { lo := edges.getD j 0, hi := edges.getD (j + 1) 0, n := wBin edges j (fun _ => 1) es,
    hits := wBin edges j wHit es, sumP := wBin edges j wProb es }

/-- The table: one row per bin, empty bins included with `n = 0`. -/
def table (edges : List Nat) (es : List BinaryEvent) : List Row :=
  (List.range (edges.length - 1)).map (rowAt edges es)

/-- A forecast outside `[0, s]` is `badEdges` (no bin holds it). -/
def checkRange (s : Scale) (es : List BinaryEvent) : Except Refusal Unit :=
  if es.all (fun e => decide (0 ≤ e.p ∧ e.p ≤ (s : Int))) then .ok () else .error .badEdges

/-- The reliability table: scale, edges, sample size and forecast range are checked first. -/
def reliability (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) : Except Refusal (List Row) := do
  checkScale s
  checkEdges lim s edges
  checkSample lim es.length
  checkRange s es
  pure (table edges es)

/-- The ratio `num / den`; a zero denominator is `empty` (it cannot arise after the checks above). -/
def ratioOf (num : Int) (den : Nat) : Except Refusal Ratio :=
  if h : 0 < den then .ok ⟨num, den, h⟩ else .error .empty

/-- The numerator of the calibration error: `Σ_j |hits_j * s - sumP_j|`. -/
def calibNum (s : Scale) (rows : List Row) : Nat :=
  (rows.map fun r => (((r.hits * s : Nat) : Int) - (r.sumP : Int)).natAbs).sum

/-- The calibration error (absolute form) `{num := Σ_j |hits_j * s - sumP_j|, den := N * s}`. -/
def calibrationError (s : Scale) (lim : Limits) (edges : List Nat) (es : List BinaryEvent) : Except Refusal Ratio := do
  let rows ← reliability s lim edges es
  ratioOf (calibNum s rows) (es.length * s)

/-- Calibration in the large: (mean forecast `Σ p / (N s)`, observed frequency `H / N`, gap `(H s - Σ p) / (N s)`). -/
def citl (s : Scale) (lim : Limits) (es : List BinaryEvent) : Except Refusal (Ratio × Ratio × Ratio) := do
  checkScale s
  checkSample lim es.length
  checkProbs s (es.map (·.p))
  let sp := sumInt (es.map (·.p))
  let h : Nat := (es.map wHit).sum
  let m ← ratioOf sp (es.length * s)
  let o ← ratioOf h es.length
  let g ← ratioOf ((h : Int) * s - sp) (es.length * s)
  pure (m, o, g)

end VbmForecast
