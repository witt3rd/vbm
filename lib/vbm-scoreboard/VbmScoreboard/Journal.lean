import VbmScoreboard.Core
/-! # Scoreboard: the journal of a change

What a command-line tool needs from the core so that it decides nothing itself, as pure functions over typed data (proved in `VbmScoreboardProofs.Journal`):

* `bankIfPassing` is banking that is refused unless every floor held (a regressed or unmeasured floor refuses it, with the verdicts).
* `bankEntries` is the history lines of a banking: ONE `banked` line for each floor whose value changed, none for a floor that did not change.
* `addMetric` is the explicit addition of a metric with its first floor: refused for an empty name and for a metric that already has a floor; otherwise the new baseline and the `added` entry.
* `startOf` is where a floor started: the earliest recorded value of the metric in the history (the value before its first change, or its first floor), or the floor itself when the history never mentions it. `progressOf` is the `progress` of a floor, from its start to the target named for its metric, if any. -/
namespace VbmScoreboard

/-- Bank, but only when every floor held: otherwise the verdicts that say why not. -/
def bankIfPassing (ms : List Metric) (b : Baseline) (rs : List Reading) :
    Except (List Verdict) Baseline :=
  if passes (check b rs) then .ok (bank ms b rs) else .error (check b rs)

/-- The history lines that turn the baseline `old` into the baseline `new` (floors in the same order) by banking: a `banked` line for each changed floor. -/
def bankEntries (time : Nat) : Baseline → Baseline → List Entry
  | f :: fs, g :: gs =>
    (if f.value = g.value then [] else [⟨time, g.metric, some f.value, some g.value, .banked⟩])
      ++ bankEntries time fs gs
  | _, _ => []

/-- Why an addition was refused. -/
inductive AddRefusal where
  | emptyName
  | alreadyThere
  deriving DecidableEq, Repr

/-- Add a metric with its first floor, and the entry that records it. -/
def addMetric (b : Baseline) (metric : String) (d : Direction) (value time : Nat) :
    Except AddRefusal (Baseline × Entry) :=
  if metric = "" then .error .emptyName
  else if hasFloor b metric then .error .alreadyThere
  else .ok (b ++ [⟨metric, d, value⟩], ⟨time, metric, none, some value, .added⟩)

/-- The earliest recorded value of a metric: the value before its first change, or the value it was first given. -/
def origin (h : History) (m : String) : Option Nat :=
  match h.find? (fun e => e.metric == m) with
  | none => none
  | some e => match e.before with
    | some v => some v
    | none => e.after

/-- Where a floor started: its earliest recorded value, or itself when the history never mentions its metric. -/
def startOf (h : History) (f : Floor) : Nat := (origin h f.metric).getD f.value

/-- The `progress` of a floor from its start to the target named for its metric; none when no target names it. -/
def progressOf (h : History) (ts : List Target) (f : Floor) : Option Nat :=
  (ts.find? (fun t => t.metric == f.metric)).map
    (fun t => progress f.direction (startOf h f) t.value f.value)

end VbmScoreboard
