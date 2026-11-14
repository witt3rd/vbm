import Lean.Data.Json
import VbmDispatcher
/-! # The wire: JSON for the machines' data, both ways

A BINDING, not the specification: it only moves the machines' data to and from JSON (the conformance vectors, and an interpreter's own records), and it decides nothing. A word that names nothing is an error, never a default. The conformance vectors are
its test: every event and action of every vector decodes and encodes back to exactly the line it came from (`vbm-dispatcher-vectors --roundtrip`). -/
namespace VbmDispatcher.Wire
open Lean VbmWork Pool

def arr (xs : List Json) : Json := Json.arr xs.toArray

/-! ## Decoding helpers: nothing is repaired, defaulted or guessed -/

def getStr (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def getNat (j : Json) (k : String) : Except String Nat := do (← j.getObjVal? k).getNat?
def getBool (j : Json) (k : String) : Except String Bool := do (← j.getObjVal? k).getBool?
def getList (j : Json) (k : String) : Except String (List Json) := do pure (← (← j.getObjVal? k).getArr?).toList
def getOptStr (j : Json) (k : String) : Except String (Option String) := do
  match ← j.getObjVal? k with
  | .null => pure none
  | .str s => pure (some s)
  | _ => throw s!"{k} must be a string or null"
def optS : Option String → Json | some s => Json.str s | none => Json.null
def strs (xs : List Json) : Except String (List String) := xs.mapM fun x => x.getStr?

/-! ## The pool's data -/

def gateName : Gate → String
  | .feasible => "feasible" | .verifier => "verifier" | .classCheck => "classCheck" | .validator => "validator" | .approval => "approval" | .lander => "lander"
def gateOf : String → Except String Gate
  | "feasible" => pure .feasible | "verifier" => pure .verifier | "classCheck" => pure .classCheck | "validator" => pure .validator | "approval" => pure .approval | "lander" => pure .lander
  | w => throw s!"{w} names no gate"

def blockKindJ : BlockKind → Json
  | .readOnlyPath => Json.mkObj [("kind", "readOnlyPath")] | .protectedPath => Json.mkObj [("kind", "protectedPath")] | .redBase => Json.mkObj [("kind", "redBase")]
  | .classExceeded => Json.mkObj [("kind", "classExceeded")] | .conflict => Json.mkObj [("kind", "conflict")] | .budget => Json.mkObj [("kind", "budget")]
  | .lost => Json.mkObj [("kind", "lost")] | .depFailed => Json.mkObj [("kind", "depFailed")] | .unplaceable => Json.mkObj [("kind", "unplaceable")]
  | .gateFailed g => Json.mkObj [("kind", "gateFailed"), ("gate", gateName g)]
def blockKindOf (j : Json) : Except String BlockKind := do
  match ← getStr j "kind" with
  | "readOnlyPath" => pure .readOnlyPath | "protectedPath" => pure .protectedPath | "redBase" => pure .redBase | "classExceeded" => pure .classExceeded
  | "conflict" => pure .conflict | "budget" => pure .budget | "lost" => pure .lost | "depFailed" => pure .depFailed | "unplaceable" => pure .unplaceable
  | "gateFailed" => pure (.gateFailed (← gateOf (← getStr j "gate")))
  | w => throw s!"{w} names no block kind"

def evidenceJ (e : Evidence) : Json := arr (e.passed.map fun g => Json.str (gateName g))
def evidenceOf (j : Json) : Except String Evidence := do pure ⟨← (← strs (← j.getArr?).toList).mapM gateOf⟩

def stateJ : State → Json
  | .pending => Json.mkObj [("state", "pending")]
  | .claimed w => Json.mkObj [("state", "claimed"), ("host", toJson w.host)]
  | .running w => Json.mkObj [("state", "running"), ("host", toJson w.host)]
  | .gated w ev => Json.mkObj [("state", "gated"), ("host", toJson w.host), ("passed", evidenceJ ev)]
  | .landed ev => Json.mkObj [("state", "landed"), ("passed", evidenceJ ev)]
  | .blocked k => Json.mkObj [("state", "blocked"), ("why", blockKindJ k)]
  | .needsClarification => Json.mkObj [("state", "needsClarification")]
  | .cancelled => Json.mkObj [("state", "cancelled")]
def stateOf (j : Json) : Except String State := do
  match ← getStr j "state" with
  | "pending" => pure .pending
  | "claimed" => pure (.claimed ⟨← getNat j "host"⟩)
  | "running" => pure (.running ⟨← getNat j "host"⟩)
  | "gated" => pure (.gated ⟨← getNat j "host"⟩ (← evidenceOf (← j.getObjVal? "passed")))
  | "landed" => pure (.landed (← evidenceOf (← j.getObjVal? "passed")))
  | "blocked" => pure (.blocked (← blockKindOf (← j.getObjVal? "why")))
  | "needsClarification" => pure .needsClarification
  | "cancelled" => pure .cancelled
  | w => throw s!"{w} names no state"

def itemJ (i : Item) : Json :=
  Json.mkObj [("id", toJson i.id), ("project", toJson i.project), ("class", i.cls.name), ("priority", toJson i.priority), ("enqueuedAt", toJson i.enqueuedAt),
    ("keys", arr (i.keys.map Json.str)), ("deps", arr (i.deps.map toJson)), ("needs", arr (i.needs.map Json.str)), ("retries", toJson i.retries)]
def itemOf (j : Json) : Except String Item := do
  let cn ← getStr j "class"
  let some cls := ChangeClass.ofName cn | throw s!"{cn} names no class"
  pure { id := ← getNat j "id", project := ← getNat j "project", cls, priority := ← getNat j "priority", enqueuedAt := ← getNat j "enqueuedAt",
         keys := ← strs (← getList j "keys"), deps := ← (← getList j "deps").mapM fun x => x.getNat?, needs := ← strs (← getList j "needs"), retries := ← getNat j "retries" }

def entryJ (e : Entry) : Json :=
  Json.mkObj [("item", itemJ e.item), ("state", stateJ e.state), ("left", toJson e.left), ("lostOn", arr (e.lostOn.map toJson)), ("lostAt", toJson e.lostAt)]
def entryOf (j : Json) : Except String Entry := do
  pure { item := ← itemOf (← j.getObjVal? "item"), state := ← stateOf (← j.getObjVal? "state"), left := ← getNat j "left", lostOn := ← (← getList j "lostOn").mapM fun x => x.getNat?, lostAt := ← getNat j "lostAt" }

def queueJ (q : Queue) : Json := arr (q.entries.map entryJ)
def queueOf (j : Json) : Except String Queue := do pure ⟨← (← j.getArr?).toList.mapM entryOf⟩

def localJ (l : Local) : Json :=
  Json.mkObj [("now", toJson l.now), ("off", l.off), ("cpuPressure", toJson l.cpuPressure), ("memUsedPermille", toJson l.memUsedPermille), ("diskFreeGb", toJson l.diskFreeGb), ("memFreeGb", toJson l.memFreeGb)]
def localOf (j : Json) : Except String Local := do
  pure { now := ← getNat j "now", off := ← getBool j "off", cpuPressure := ← getNat j "cpuPressure", memUsedPermille := ← getNat j "memUsedPermille", diskFreeGb := ← getNat j "diskFreeGb", memFreeGb := ← getNat j "memFreeGb" }

def paramsJ (p : Params) : Json :=
  Json.mkObj [("quantum", toJson p.quantum), ("patience", toJson p.patience), ("pressureCeil", toJson p.pressureCeil), ("memCeil", toJson p.memCeil), ("diskFloor", toJson p.diskFloor), ("memFloor", toJson p.memFloor)]
def paramsOf (j : Json) : Except String Params := do
  pure ⟨← getNat j "quantum", ← getNat j "patience", ← getNat j "pressureCeil", ← getNat j "memCeil", ← getNat j "diskFloor", ← getNat j "memFloor"⟩

def qualsJ (q : Quals) : Json := Json.mkObj [("id", toJson q.id), ("labels", arr (q.labels.map Json.str)), ("draining", q.draining)]
def qualsOf (j : Json) : Except String Quals := do pure ⟨← getNat j "id", ← strs (← getList j "labels"), ← getBool j "draining"⟩

/-! ## The tick -/

def tickConfigJ (c : TickConfig) : Json := Json.mkObj [("params", paramsJ c.params), ("me", qualsJ c.me)]
def tickConfigOf (j : Json) : Except String TickConfig := do pure ⟨← paramsOf (← j.getObjVal? "params"), ← qualsOf (← j.getObjVal? "me")⟩

def tickResultJ : TickResult → Json
  | .skipped => Json.mkObj [("result", "skipped")] | .idle => Json.mkObj [("result", "idle")] | .storeUnreachable => Json.mkObj [("result", "storeUnreachable")]
  | .started id msg gen => Json.mkObj [("result", "started"), ("item", toJson id), ("msg", toJson msg), ("gen", toJson gen)]
def tickResultOf (j : Json) : Except String TickResult := do
  match ← getStr j "result" with
  | "skipped" => pure .skipped | "idle" => pure .idle | "storeUnreachable" => pure .storeUnreachable
  | "started" => pure (.started (← getNat j "item") (← getNat j "msg") (← getNat j "gen"))
  | w => throw s!"{w} names no tick result"

def tickEventJ : TickEvent → Json
  | .readings lc => Json.mkObj [("event", "readings"), ("readings", localJ lc)]
  | .queue q => Json.mkObj [("event", "queue"), ("queue", queueJ q)]
  | .storeDown => Json.mkObj [("event", "storeDown")]
  | .claimWon msg gen => Json.mkObj [("event", "claimWon"), ("msg", toJson msg), ("gen", toJson gen)]
  | .claimLost => Json.mkObj [("event", "claimLost")]
def tickEventOf (j : Json) : Except String TickEvent := do
  match ← getStr j "event" with
  | "readings" => pure (.readings (← localOf (← j.getObjVal? "readings")))
  | "queue" => pure (.queue (← queueOf (← j.getObjVal? "queue")))
  | "storeDown" => pure .storeDown
  | "claimWon" => pure (.claimWon (← getNat j "msg") (← getNat j "gen"))
  | "claimLost" => pure .claimLost
  | w => throw s!"{w} names no tick event"

def tickActionJ : TickAction → Json
  | .readHost => Json.mkObj [("action", "readHost")] | .readQueue => Json.mkObj [("action", "readQueue")]
  | .claim id => Json.mkObj [("action", "claim"), ("item", toJson id)]
  | .endTick r => Json.mkObj [("action", "endTick"), ("result", tickResultJ r)]
def tickActionOf (j : Json) : Except String TickAction := do
  match ← getStr j "action" with
  | "readHost" => pure .readHost | "readQueue" => pure .readQueue
  | "claim" => pure (.claim (← getNat j "item"))
  | "endTick" => pure (.endTick (← tickResultOf (← j.getObjVal? "result")))
  | w => throw s!"{w} names no tick action"

def tickPhaseJ : TickPhase → Json
  | .reading => Json.mkObj [("phase", "reading")]
  | .listing lc => Json.mkObj [("phase", "listing"), ("readings", localJ lc)]
  | .claiming id lc => Json.mkObj [("phase", "claiming"), ("item", toJson id), ("readings", localJ lc)]
  | .ended r => Json.mkObj [("phase", "ended"), ("result", tickResultJ r)]

/-! ## The run -/

def citationJ (c : Citation) : Json := Json.mkObj [("call", c.call), ("span", c.span)]
def outcomeJ : VbmWork.Outcome → Json
  | .done cs => Json.mkObj [("outcome", "done"), ("citations", arr (cs.map citationJ))]
  | .doneWithAssumptions as cs => Json.mkObj [("outcome", "done_with_assumptions"), ("assumptions", arr (as.map Json.str)), ("citations", arr (cs.map citationJ))]
  | .blocked k r cs => Json.mkObj [("outcome", "blocked"), ("kind", k.name), ("reason", r), ("citations", arr (cs.map citationJ))]
  | .needsClarification q d cs => Json.mkObj [("outcome", "needs_clarification"), ("question", q), ("default", d), ("citations", arr (cs.map citationJ))]
def citationOf (j : Json) : Except String Citation := do pure ⟨← getStr j "call", ← getStr j "span"⟩
def outcomeOf (j : Json) : Except String VbmWork.Outcome := do
  let cs ← (← getList j "citations").mapM citationOf
  match ← getStr j "outcome" with
  | "done" => pure (.done cs)
  | "done_with_assumptions" => pure (.doneWithAssumptions (← strs (← getList j "assumptions")) cs)
  | "blocked" =>
    let kn ← getStr j "kind"
    match Kind.ofName kn with
    | some k => pure (.blocked k (← getStr j "reason") cs)
    | none => throw s!"{kn} names no kind"
  | "needs_clarification" => pure (.needsClarification (← getStr j "question") (← getStr j "default") cs)
  | w => throw s!"{w} names no outcome"

def reportJ (r : Report) : Json := Json.mkObj [("outcome", outcomeJ r.outcome), ("landed", optS r.landed)]
def reportOf (j : Json) : Except String Report := do pure ⟨← outcomeOf (← j.getObjVal? "outcome"), ← getOptStr j "landed"⟩

def runEventJ : RunEvent → Json
  | .beat => Json.mkObj [("event", "beat")] | .renewed => Json.mkObj [("event", "renewed")] | .renewRefused => Json.mkObj [("event", "renewRefused")]
  | .renewUnreachable => Json.mkObj [("event", "renewUnreachable")] | .workerGone => Json.mkObj [("event", "workerGone")] | .workerStopped => Json.mkObj [("event", "workerStopped")]
  | .finished => Json.mkObj [("event", "finished")] | .finishRefused => Json.mkObj [("event", "finishRefused")] | .finishUnreachable => Json.mkObj [("event", "finishUnreachable")]
  | .cleaned => Json.mkObj [("event", "cleaned")] | .deadline => Json.mkObj [("event", "deadline")]
  | .workerReported r => Json.mkObj [("event", "workerReported"), ("report", reportJ r)]
def runEventOf (j : Json) : Except String RunEvent := do
  match ← getStr j "event" with
  | "beat" => pure .beat | "renewed" => pure .renewed | "renewRefused" => pure .renewRefused | "renewUnreachable" => pure .renewUnreachable
  | "workerGone" => pure .workerGone | "workerStopped" => pure .workerStopped | "finished" => pure .finished | "finishRefused" => pure .finishRefused
  | "finishUnreachable" => pure .finishUnreachable | "cleaned" => pure .cleaned | "deadline" => pure .deadline
  | "workerReported" => pure (.workerReported (← reportOf (← j.getObjVal? "report")))
  | w => throw s!"{w} names no run event"

def runActionJ : RunAction → Json
  | .renew => Json.mkObj [("action", "renew")] | .stopWorker => Json.mkObj [("action", "stopWorker")] | .cleanup => Json.mkObj [("action", "cleanup")]
  | .finish r => Json.mkObj [("action", "finish"), ("report", reportJ r)]
def runActionOf (j : Json) : Except String RunAction := do
  match ← getStr j "action" with
  | "renew" => pure .renew | "stopWorker" => pure .stopWorker | "cleanup" => pure .cleanup
  | "finish" => pure (.finish (← reportOf (← j.getObjVal? "report")))
  | w => throw s!"{w} names no run action"

def runPhaseJ : RunPhase → Json
  | .running => Json.mkObj [("phase", "running")] | .stopping => Json.mkObj [("phase", "stopping")] | .cleaning => Json.mkObj [("phase", "cleaning")] | .closed => Json.mkObj [("phase", "closed")]
  | .finishing r => Json.mkObj [("phase", "finishing"), ("report", reportJ r)]

/-! ## A scenario of the vectors, decoded -/

inductive Vector where
  | tick (name : String) (cfg : TickConfig) (start : List TickAction) (steps : List (TickEvent × List TickAction)) (final : Json)
  | run (name : String) (start : List RunAction) (steps : List (RunEvent × List RunAction)) (final : Json)

def vectorOf (j : Json) : Except String Vector := do
  match ← getStr j "machine" with
  | "tick" =>
    let steps ← (← getList j "steps").mapM fun s => do
      pure (← tickEventOf (← s.getObjVal? "event"), ← (← getList s "asks").mapM tickActionOf)
    pure (.tick (← getStr j "name") (← tickConfigOf (← j.getObjVal? "config")) (← (← getList j "start").mapM tickActionOf) steps (← j.getObjVal? "final"))
  | "run" =>
    let steps ← (← getList j "steps").mapM fun s => do
      pure (← runEventOf (← s.getObjVal? "event"), ← (← getList s "asks").mapM runActionOf)
    pure (.run (← getStr j "name") (← (← getList j "start").mapM runActionOf) steps (← j.getObjVal? "final"))
  | w => throw s!"{w} names no machine"

/-- The scenario as the line it came from: the decoded data encoded again. -/
def Vector.toJson : Vector → Json
  | .tick name cfg start steps final =>
    Json.mkObj [("name", name), ("machine", "tick"), ("config", tickConfigJ cfg), ("start", arr (start.map tickActionJ)),
      ("steps", arr (steps.map fun (e, as) => Json.mkObj [("event", tickEventJ e), ("asks", arr (as.map tickActionJ))])), ("final", final)]
  | .run name start steps final =>
    Json.mkObj [("name", name), ("machine", "run"), ("start", arr (start.map runActionJ)),
      ("steps", arr (steps.map fun (e, as) => Json.mkObj [("event", runEventJ e), ("asks", arr (as.map runActionJ))])), ("final", final)]

end VbmDispatcher.Wire
