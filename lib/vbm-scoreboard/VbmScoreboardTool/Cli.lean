import VbmScoreboard
import VbmScoreboardWire
/-! # The command line: words in, words out

The pure half of the tool `vbm-scoreboard`: the arguments read into a command, and the typed results of the libraries written as text. It decides nothing about a scoreboard: every verdict, refusal and number is a value of `VbmScoreboard` or `VbmScoreboardWire`, and this module only names it. The half that touches the machine is `VbmScoreboardTool.Main`.

Exit codes: 0 done; 1 the scoreboard says no (a regression, an unmeasured metric, a refused reset, add or bank); 2 usage; 3 the provider was refused (it failed, it was stopped, or its output is malformed); 4 a file could not be read, written or understood. -/
namespace VbmScoreboardTool

open VbmScoreboard VbmScoreboardWire

/-- The default limit, in seconds, on a provider: it protects the machine from a provider that never exits, which would hold its process, its memory and the caller forever. -/
def defaultTimeout : Nat := 300

/-- The flags each subcommand accepts (and `none` for a word that is no subcommand). -/
def allowed : String → Option (List String)
  | "check" => some ["provider", "baseline", "timeout"]
  | "show" => some ["provider", "baseline", "timeout"]
  | "bank" => some ["provider", "baseline", "history", "author", "reason", "timeout", "at"]
  | "reset" => some ["baseline", "history", "to", "reason", "author", "at"]
  | "progress" => some ["baseline", "history", "target"]
  | "add" => some ["baseline", "history", "direction", "floor", "at"]
  | _ => none

/-- A command line read into its subcommand, its positional words and its `--flag value` pairs (in order). -/
structure Parsed where
  command : String
  positional : List String
  flags : List (String × String)

def parseWords (allow : List String) : List String → List String → List (String × String) →
    Except String (List String × List (String × String))
  | [], pos, fl => .ok (pos.reverse, fl.reverse)
  | w :: rest, pos, fl =>
    if w.startsWith "--" then
      let k := (w.drop 2).toString
      if !(allow.contains k) then .error s!"unknown flag {w}"
      else match rest with
        | [] => .error s!"flag {w} needs a value"
        | v :: rest' =>
          if k != "target" && (fl.any (·.1 == k)) then .error s!"flag {w} is given twice"
          else parseWords allow rest' pos ((k, v) :: fl)
    else parseWords allow rest (w :: pos) fl

def parseArgs : List String → Except String Parsed
  | [] => .error "no subcommand"
  | c :: rest =>
    match allowed c with
    | none => .error s!"unknown subcommand {c}"
    | some allow =>
      match parseWords allow rest [] [] with
      | .error e => .error e
      | .ok (pos, fl) => .ok { command := c, positional := pos, flags := fl }

def usage : String :=
  "usage: vbm-scoreboard SUBCOMMAND ...\n" ++
  "  check    --provider CMD --baseline FILE [--timeout SECONDS]\n" ++
  "  show     --provider CMD --baseline FILE [--timeout SECONDS]\n" ++
  "  bank     --provider CMD --baseline FILE --history FILE [--author A] [--reason R] [--timeout SECONDS] [--at SECONDS]\n" ++
  "  reset    METRIC --to N --reason R --author A --baseline FILE --history FILE [--at SECONDS]\n" ++
  "  progress --baseline FILE --history FILE [--target METRIC=N ...]\n" ++
  "  add      METRIC --direction higher|lower --floor N --baseline FILE --history FILE [--at SECONDS]\n" ++
  s!"The provider is run with sh -c and stopped after --timeout seconds (default {defaultTimeout}).\n" ++
  "Exit: 0 done, 1 the scoreboard says no, 2 usage, 3 provider refused, 4 file error."

/-! ## Words for the libraries' typed results -/

def whyText : Why → String
  | .notJson m => s!"not JSON ({m})"
  | .notObject => "not an object"
  | .missingKey k => s!"missing key {k}"
  | .wrongType k => s!"wrong type for key {k}"
  | .unknownVersion v => s!"unknown version {v}"
  | .unknownWord k w => s!"unknown {k} {w}"
  | .duplicate m => s!"metric {m} repeated"

def refusalText (r : VbmScoreboardWire.Refusal) : String := s!"line {r.line}: {whyText r.why}"

def providerText : ProviderRefusal → String
  | .failed c => s!"provider failed: exit code {c}"
  | .timedOut s => s!"provider stopped: still running after {s} seconds"
  | .malformed r => s!"provider output refused: {refusalText r}"

def resetText : VbmScoreboard.Refusal → String
  | .emptyReason => "a reset needs a reason"
  | .emptyAuthor => "a reset needs an author"
  | .noFloor => "no such metric in the baseline"
  | .notLooser => "that is not looser than the floor: use bank"

def addText : AddRefusal → String
  | .emptyName => "a metric needs a name"
  | .alreadyThere => "the metric already has a floor"

def better (d : Direction) : String := directionWord d ++ " is better"

/-- The failing verdicts, one line each; the verdicts are the library's, in baseline order. -/
def verdictLines (b : Baseline) (vs : List Verdict) : List String :=
  vs.filterMap fun
    | .held => none
    | .regressed m f n =>
      let d := match floorOf b m with | some g => s!" ({better g.direction})" | none => ""
      some s!"scoreboard: regressed: {m}: reading {n} is worse than floor {f}{d}"
    | .unmeasured m => some s!"scoreboard: unmeasured: {m}: no reading (a floor with no reading fails)"

def padRight (s : String) (n : Nat) : String := s.pushn ' ' (n - s.length)

/-- The table of `show`: metric, direction, floor, reading (`-` when the provider gave none). -/
def showLines (b : Baseline) (rs : List Reading) : List String :=
  let w := b.foldl (fun m f => max m f.metric.length) 6
  let row (f : Floor) : String :=
    padRight f.metric w ++ "  " ++ padRight (directionWord f.direction) 9 ++ "  " ++
      padRight (toString f.value) 8 ++ "  " ++ (match lookup rs f.metric with | some v => toString v | none => "-")
  (padRight "metric" w ++ "  " ++ padRight "direction" 9 ++ "  " ++ padRight "floor" 8 ++ "  reading") :: b.map row

/-- The lines of `progress`: where each floor started, where it is, its target and its permille of the way. -/
def progressLines (h : History) (ts : List Target) (b : Baseline) : List String :=
  let w := b.foldl (fun m f => max m f.metric.length) 6
  let row (f : Floor) : String :=
    let t := (ts.find? (fun t => t.metric == f.metric)).map (toString ·.value) |>.getD "-"
    let p := (progressOf h ts f).map toString |>.getD "-"
    padRight f.metric w ++ "  " ++ padRight (directionWord f.direction) 9 ++ "  " ++
      padRight (toString (startOf h f)) 8 ++ "  " ++ padRight (toString f.value) 8 ++ "  " ++ padRight t 8 ++ "  " ++ p
  (padRight "metric" w ++ "  " ++ padRight "direction" 9 ++ "  " ++ padRight "start" 8 ++ "  " ++ padRight "floor" 8 ++ "  " ++
    padRight "target" 8 ++ "  permille") :: b.map row

def entryLine (e : Entry) : String :=
  let n := fun (o : Option Nat) => match o with | some v => toString v | none => "-"
  let w := match e.event with | .banked => "banked" | .added => "added" | .reset _ _ => "reset"
  s!"{w} {e.metric}: {n e.before} -> {n e.after}"

end VbmScoreboardTool
