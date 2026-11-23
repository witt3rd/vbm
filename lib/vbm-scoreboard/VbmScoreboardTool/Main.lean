import Std.Time
import VbmScoreboardTool.Cli
/-! # vbm-scoreboard: the command-line tool

THE BOUNDARY. This module reads files and the output of a provider command, calls the specified functions of `VbmScoreboard` and `VbmScoreboardWire`, prints their typed results and sets the exit code. It decides nothing: no comparison, no ranking, no refusal rule is written here. What it trusts is marked in `docs/trust-ledger.md` (the file reads and writes, the clock, the process spawn).

What the machine itself needs, and the library cannot know, is the only limit: a provider that never exits is stopped after `--timeout` seconds (`defaultTimeout`; the harm is a hung caller, a held process and its memory).

Writes are whole-file: a new file beside the old, then a rename over it, so a reader never sees half a file. `bank` and `add` and `reset` change the baseline and the history together: both new files are written first, then renamed in; if the second rename fails the first is put back. A crash between the two renames is the one window this does not close (stated in the trust ledger). -/
namespace VbmScoreboardTool

open VbmScoreboard VbmScoreboardWire

/-- A failure of the boundary: the exit code and what to say on the error stream. -/
structure Fail where
  code : UInt32
  message : String

abbrev M := ExceptT Fail IO

def fail {α : Type} (code : UInt32) (message : String) : M α := throw ⟨code, message⟩

def flag (p : Parsed) (k : String) : Option String := (p.flags.find? (·.1 == k)).map (·.2)

def need (p : Parsed) (k : String) : M String :=
  match flag p k with
  | some v => pure v
  | none => fail 2 s!"missing --{k}\n{usage}"

def needNat (p : Parsed) (k : String) : M Nat := do
  let v ← need p k
  match v.toNat? with
  | some n => pure n
  | none => fail 2 s!"--{k} must be a natural number, not {v}"

/-- A flag that is a natural number, or the default. -/
def natOr (p : Parsed) (k : String) (d : Nat) : M Nat :=
  match flag p k with
  | none => pure d
  | some _ => needNat p k

/-! ## The file system (trusted: T3) -/

def readText (path : String) : M String := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .ok s => pure s
  | .error e => fail 4 s!"cannot read {path}: {e}"

def writeNew (path tmp : String) (text : String) : M Unit := do
  match ← (IO.FS.writeFile tmp text).toBaseIO with
  | .ok _ => pure ()
  | .error e => fail 4 s!"cannot write {tmp} (for {path}): {e}"

def renameTo (tmp path : String) : M Unit := do
  match ← (IO.FS.rename tmp path).toBaseIO with
  | .ok _ => pure ()
  | .error e => fail 4 s!"cannot replace {path}: {e}"

/-- Put two files in place together: both new files are written beside the old, then renamed; a failure of the second rename puts the first back. -/
def replaceBoth (bPath bText hPath hText oldB : String) : M Unit := do
  let pid ← IO.Process.getPID
  let bt := s!"{bPath}.tmp{pid}"
  let ht := s!"{hPath}.tmp{pid}"
  let rt := s!"{bPath}.undo{pid}"
  let cleanup : IO Unit := do
    for f in [bt, ht, rt] do
      if ← System.FilePath.pathExists f then (IO.FS.removeFile f).toBaseIO *> pure ()
  try
    writeNew bPath bt bText
    writeNew hPath ht hText
    renameTo bt bPath
    let r : Except Fail Unit ← (renameTo ht hPath).run
    match r with
    | .ok _ => pure ()
    | .error e =>
      writeNew bPath rt oldB
      renameTo rt bPath
      throw ⟨e.code, e.message ++ s!"\nnothing changed: {bPath} was put back"⟩
  finally
    cleanup

/-- Seconds since the epoch, from the clock (trusted: T3), unless `--at` gives them. -/
def timeOf (p : Parsed) : M Nat := do
  match flag p "at" with
  | some _ => needNat p "at"
  | none =>
    let t ← Std.Time.Timestamp.now
    pure t.toSecondsSinceUnixEpoch.val.toNat

/-! ## The provider (trusted: T4) -/

abbrev ProviderCfg : IO.Process.StdioConfig := ⟨.null, .piped, .inherit⟩
abbrev ProviderChild := IO.Process.Child ProviderCfg

/-- Stop a provider: its whole process group, then the shell itself. -/
def stopProvider (child : ProviderChild) :
    IO Unit := do
  let _ ← (IO.Process.output { cmd := "kill", args := #["-KILL", "--", s!"-{child.pid}"] }).toBaseIO
  let _ ← child.kill.toBaseIO

/-- Wait for the exit of the provider until `deadline` (milliseconds on the monotonic clock). -/
partial def waitProvider (child : ProviderChild)
    (deadline : Nat) : IO (Option UInt32) := do
  match ← child.tryWait with
  | some c => pure (some c)
  | none =>
    if (← IO.monoMsNow) ≥ deadline then pure none
    else do IO.sleep 10; waitProvider child deadline

/-- Run `sh -c cmd`: its standard output and exit code, or the stop after `seconds`. -/
def runProvider (cmd : String) (seconds : Nat) : IO Outcome := do
  let child ← IO.Process.spawn { toStdioConfig := ProviderCfg, cmd := "sh", args := #["-c", cmd], setsid := true }
  let reader ← IO.asTask child.stdout.readToEnd
  let deadline := (← IO.monoMsNow) + seconds * 1000
  match ← waitProvider child deadline with
  | none =>
    stopProvider child
    pure (.timedOut seconds)
  | some c =>
    match ← IO.wait reader with
    | .ok out => pure (.exited c.toNat out)
    | .error e => throw (IO.userError s!"provider output unreadable: {e}")

def readings (p : Parsed) : M (List Reading) := do
  let cmd ← need p "provider"
  let seconds ← natOr p "timeout" defaultTimeout
  let outcome ← match ← (runProvider cmd seconds).toBaseIO with
    | .ok o => pure o
    | .error e => fail 3 s!"provider could not be run: {e}"
  match readProvider outcome with
  | .ok rs => pure rs
  | .error r => fail 3 (providerText r)

def baselineOf (path text : String) : M Baseline :=
  match decodeBaseline text with
  | .ok b => pure b
  | .error r => fail 4 s!"{path}: {refusalText r}"

def historyOf (path text : String) : M History :=
  match decodeHistory text with
  | .ok h => pure h
  | .error r => fail 4 s!"{path}: {refusalText r}"

/-- Both files, as text and as values. -/
def loadBoth (p : Parsed) : M (String × String × String × Baseline × History) := do
  let bp ← need p "baseline"
  let hp ← need p "history"
  let bt ← readText bp
  let ht ← readText hp
  pure (bp, hp, bt, ← baselineOf bp bt, ← historyOf hp ht)

def say (s : String) : M Unit := IO.println s

/-! ## The subcommands -/

def runCheck (p : Parsed) : M UInt32 := do
  let bp ← need p "baseline"
  let b ← baselineOf bp (← readText bp)
  let rs ← readings p
  let vs := check b rs
  if passes vs then
    say s!"scoreboard: ok: {b.length} floors held"
    pure 0
  else
    for l in verdictLines b vs do IO.eprintln l
    pure 1

def runShow (p : Parsed) : M UInt32 := do
  let bp ← need p "baseline"
  let b ← baselineOf bp (← readText bp)
  let rs ← readings p
  for l in showLines b rs do say l
  pure 0

def runBank (p : Parsed) : M UInt32 := do
  let (bp, hp, bt, b, h) ← loadBoth p
  let rs ← readings p
  let now ← timeOf p
  match bankIfPassing [] b rs with
  | .error vs =>
    for l in verdictLines b vs do IO.eprintln l
    IO.eprintln "scoreboard: nothing banked"
    pure 1
  | .ok b' =>
    let es := bankEntries now b b'
    if es.isEmpty then
      say "scoreboard: nothing to bank: no floor moved"
      pure 0
    else
      replaceBoth bp (encodeBaseline b') hp (encodeHistory (es.foldl record h)) bt
      for e in es do say s!"scoreboard: banked: {entryLine e}"
      pure 0

def runReset (p : Parsed) : M UInt32 := do
  let some metric := p.positional.head? | fail 2 s!"reset needs a METRIC\n{usage}"
  let to ← needNat p "to"
  let reason ← need p "reason"
  let author ← need p "author"
  let (bp, hp, bt, b, h) ← loadBoth p
  let now ← timeOf p
  match reset b metric to reason author now with
  | .error r =>
    IO.eprintln s!"scoreboard: reset refused: {metric}: {resetText r}"
    pure 1
  | .ok (b', e) =>
    replaceBoth bp (encodeBaseline b') hp (encodeHistory (record h e)) bt
    say s!"scoreboard: {entryLine e}"
    pure 0

def runAdd (p : Parsed) : M UInt32 := do
  let some metric := p.positional.head? | fail 2 s!"add needs a METRIC\n{usage}"
  let dw ← need p "direction"
  let some d := directionOf dw | fail 2 s!"--direction must be higher or lower, not {dw}"
  let v ← needNat p "floor"
  let (bp, hp, bt, b, h) ← loadBoth p
  let now ← timeOf p
  match addMetric b metric d v now with
  | .error r =>
    IO.eprintln s!"scoreboard: add refused: {metric}: {addText r}"
    pure 1
  | .ok (b', e) =>
    replaceBoth bp (encodeBaseline b') hp (encodeHistory (record h e)) bt
    say s!"scoreboard: {entryLine e}"
    pure 0

/-- `--target METRIC=N`: the one thing the tool parses by hand; it names a `Target`. -/
def targetOf (s : String) : M Target :=
  match s.splitOn "=" with
  | [m, n] =>
    match n.toNat? with
    | some v => if m = "" then fail 2 s!"--target {s}: no metric" else pure ⟨m, v⟩
    | none => fail 2 s!"--target {s}: not METRIC=N"
  | _ => fail 2 s!"--target {s}: not METRIC=N"

def runProgress (p : Parsed) : M UInt32 := do
  let (_, _, _, b, h) ← loadBoth p
  let mut ts : List Target := []
  for (k, v) in p.flags do
    if k = "target" then ts := ts ++ [← targetOf v]
  for l in progressLines h ts b do say l
  pure 0

def dispatch (args : List String) : M UInt32 := do
  match parseArgs args with
  | .error e => fail 2 s!"{e}\n{usage}"
  | .ok p =>
    match p.command with
    | "check" => runCheck p
    | "show" => runShow p
    | "bank" => runBank p
    | "reset" => runReset p
    | "progress" => runProgress p
    | _ => runAdd p

end VbmScoreboardTool

def main (args : List String) : IO UInt32 := do
  match ← (VbmScoreboardTool.dispatch args).run with
  | .ok c => pure c
  | .error f =>
    IO.eprintln s!"scoreboard: {f.message}"
    pure f.code
