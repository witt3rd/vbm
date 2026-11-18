import VbmScoreboard.Direction
/-! # Scoreboard: the ratchet as pure functions

The scoreboard core, stated as pure functions over typed data, generically: **a metric is a name and a number**, with a direction (which way is better, `Direction`). No binary, project, language or vendor is named here; the unit of a number is the provider's, said in the metric's name (a share in hundredths, a ratio in permille).

* `check` gives ONE verdict per floor, in baseline order: `held`, `regressed`, or `unmeasured` (the metric has no reading: FAIL CLOSED). `passes` is true exactly when every verdict is `held`.
* `bank` moves a floor to its reading only when the reading is better, never to a worse one, and adds a floor (direction from the declared `Metric`s) for a declared metric that has a reading and no floor yet. The floor ratchet: it only moves toward better.
* `reset` is the ONLY way to move a floor toward worse. It requires a non-empty reason and author and yields the history entry. A reset to a value that is at least as good as the floor is refused (that is `bank`); a metric with no floor is refused too.
* `record` appends an entry to a history; a history is append-only.
* `progress` is the permille of the distance from floor to target covered by `now`.

Choices, stated: the first reading of a name wins and the first floor of a name is the one a reset reads (a well-formed baseline has one of each); a reading for a metric that is neither in the baseline nor declared is ignored by `bank` (and `check` looks only at floors); the entry's time field is named `time` (`at` is a reserved word in Lean).

The theorems and their non-vacuity witnesses are in `VbmScoreboardProofs.Core`. -/
namespace VbmScoreboard

/-- A metric: a name and the direction that is better. -/
structure Metric where
  name : String
  direction : Direction
  deriving DecidableEq, Repr

/-- A reading: a provider's integer for a metric (the unit is the provider's, said in the name). -/
structure Reading where
  metric : String
  value : Nat
  deriving DecidableEq, Repr

/-- A floor: the worst value ever allowed again for a metric. -/
structure Floor where
  metric : String
  direction : Direction
  value : Nat
  deriving DecidableEq, Repr

/-- A baseline: the floors, in order. -/
abbrev Baseline := List Floor

/-- The verdict on one floor. -/
inductive Verdict where
  | held
  | regressed (metric : String) (floor now : Nat)
  | unmeasured (metric : String)
  deriving DecidableEq, Repr

/-- The first reading of a metric, if any. -/
def lookup (rs : List Reading) (m : String) : Option Nat :=
  match rs with
  | [] => none
  | r :: rest => if r.metric = m then some r.value else lookup rest m

/-- The verdict on one floor. -/
def verdictOf (rs : List Reading) (f : Floor) : Verdict :=
  match lookup rs f.metric with
  | none => .unmeasured f.metric
  | some v => if Direction.better f.direction v f.value then .held else .regressed f.metric f.value v

/-- ONE verdict per floor, in baseline order. -/
def check (b : Baseline) (rs : List Reading) : List Verdict := b.map (verdictOf rs)

/-- Is the verdict `held`? -/
def Verdict.isHeld : Verdict → Bool
  | .held => true
  | _ => false

/-- Every verdict is held. -/
def passes (vs : List Verdict) : Bool := vs.all Verdict.isHeld

/-- Move a floor to its reading when the reading is better; otherwise leave it. -/
def bankFloor (rs : List Reading) (f : Floor) : Floor :=
  match lookup rs f.metric with
  | none => f
  | some v => if Direction.better f.direction v f.value then { f with value := v } else f

/-- Does the baseline have a floor for the metric? -/
def hasFloor (b : Baseline) (m : String) : Bool := b.any (fun f => f.metric == m)

/-- Add a floor, at its reading, for each declared metric that has a reading and no floor yet. -/
def addNew (rs : List Reading) : List Metric → Baseline → Baseline
  | [], b => b
  | m :: rest, b =>
    match lookup rs m.name with
    | none => addNew rs rest b
    | some v =>
      if hasFloor b m.name then addNew rs rest b
      else addNew rs rest (b ++ [{ metric := m.name, direction := m.direction, value := v }])

/-- Bank the readings: improvements only, plus a floor for a declared metric measured for the first time. -/
def bank (ms : List Metric) (b : Baseline) (rs : List Reading) : Baseline :=
  addNew rs ms (b.map (bankFloor rs))

/-- What happened to a floor. -/
inductive Event where
  | banked
  | reset (reason author : String)
  | added
  deriving DecidableEq, Repr

/-- One line of the series. -/
structure Entry where
  time : Nat
  metric : String
  before : Option Nat
  after : Option Nat
  event : Event
  deriving DecidableEq, Repr

/-- The history: append-only. -/
abbrev History := List Entry

/-- The only way to change a history: add an entry at the end. -/
def record (h : History) (e : Entry) : History := h ++ [e]

/-- Why a hand reset was refused. -/
inductive Refusal where
  | emptyReason
  | emptyAuthor
  | noFloor
  | notLooser
  deriving DecidableEq, Repr

/-- The first floor of a metric. -/
def floorOf (b : Baseline) (m : String) : Option Floor := b.find? (fun f => f.metric == m)

/-- A hand reset: the ONLY way to move a floor toward worse. -/
def reset (b : Baseline) (metric : String) (value : Nat) (reason author : String) (time : Nat) :
    Except Refusal (Baseline × Entry) :=
  if reason = "" then .error .emptyReason
  else if author = "" then .error .emptyAuthor
  else
    match floorOf b metric with
    | none => .error .noFloor
    | some f =>
      if Direction.better f.direction value f.value then .error .notLooser
      else .ok (b.map (fun g => if g.metric = metric then { g with value := value } else g),
                { time := time, metric := metric, before := some f.value, after := some value,
                  event := .reset reason author })

/-- A target: where the project wants a metric to be. -/
structure Target where
  metric : String
  value : Nat
  deriving DecidableEq, Repr

/-- How much better `a` is than `b` (0 when it is not). -/
def gain (d : Direction) (a b : Nat) : Nat :=
  match d with
  | .higher => a - b
  | .lower => b - a

/-- Permille of the distance from `floor` to `target` covered by `now`: 0 when the target is not ahead of the floor, 1000 when reached or passed. Total. -/
def progress (d : Direction) (floor target now : Nat) : Nat :=
  let total := gain d target floor
  if total = 0 then 0 else min (gain d now floor) total * 1000 / total

end VbmScoreboard
