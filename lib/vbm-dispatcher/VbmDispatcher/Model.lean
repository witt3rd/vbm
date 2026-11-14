import VbmDispatcher.Tick
import VbmDispatcher.Run
/-! # The reference models

Each machine driven under the PORT DISCIPLINE, which is what an interpreter must keep: every action asks one port and the event that follows answers it; only the world's own events (a beat, the worker's report or exit, the run's deadline) arrive unasked.
`driveTick` and `driveRun` refuse a sequence that breaks the discipline (an event that answers nothing pending) or a world event the machine would silently ignore: a scenario that passes is one a correct interpreter can meet. -/
namespace VbmDispatcher

/-- One step of a run of a machine: the event, and what the machine asked for in answer. -/
structure Step (E A : Type) where
  event : E
  actions : List A
  deriving Repr

/-- Does this event answer that action? Every tick event answers a question the tick asked. -/
def TickEvent.answers : TickEvent → TickAction → Bool
  | .readings _, .readHost => true
  | .queue _, .readQueue => true
  | .storeDown, .readQueue => true
  | .storeDown, .claim _ => true
  | .claimWon _ _, .claim _ => true
  | .claimLost, .claim _ => true
  | _, _ => false

def driveTick (cfg : TickConfig) : TickPhase → List TickAction → List TickEvent → Except String (List (Step TickEvent TickAction) × TickPhase)
  | s, _, [] => .ok ([], s)
  | s, pending, e :: es =>
    if !(pending.any e.answers) then .error "an event that answers no pending action"
    else
      let r := Tick.step cfg s e
      match driveTick cfg r.1 r.2 es with
      | .ok (steps, s') => .ok (⟨e, r.2⟩ :: steps, s')
      | .error m => .error m

def runTick (cfg : TickConfig) (events : List TickEvent) : Except String (List (Step TickEvent TickAction) × TickPhase) :=
  driveTick cfg Tick.start.1 Tick.start.2 events

/-- An event the world raises on its own, not in answer to an action. -/
def RunEvent.external : RunEvent → Bool
  | .beat | .workerReported _ | .workerGone | .deadline => true
  | _ => false

def RunEvent.answers : RunEvent → RunAction → Bool
  | .renewed, .renew | .renewRefused, .renew | .renewUnreachable, .renew => true
  | .finished, .finish _ | .finishRefused, .finish _ | .finishUnreachable, .finish _ => true
  | .workerStopped, .stopWorker => true
  | .cleaned, .cleanup => true
  | _, _ => false

def driveRun : RunPhase → List RunAction → List RunEvent → Except String (List (Step RunEvent RunAction) × RunPhase)
  | s, _, [] => .ok ([], s)
  | s, pending, e :: es =>
    if !(e.external || pending.any e.answers) then .error "an event that answers no pending action, and is not the world's own"
    else
      let r := Run.step s e
      if e.external && decide (r.1 = s) && r.2.isEmpty then .error "a world event the machine ignores (it changed nothing and asked for nothing)"
      else match driveRun r.1 r.2 es with
        | .ok (steps, s') => .ok (⟨e, r.2⟩ :: steps, s')
        | .error m => .error m

def runRun (events : List RunEvent) : Except String (List (Step RunEvent RunAction) × RunPhase) :=
  driveRun Run.start.1 Run.start.2 events

end VbmDispatcher
