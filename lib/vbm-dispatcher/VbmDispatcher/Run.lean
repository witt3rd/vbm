import VbmWork
/-! # VbmDispatcher.Run: one claimed item, supervised, as a pure machine

After a host wins a claim, a worker runs the item while this machine supervises it: the lease is renewed at every beat, the worker's typed report becomes the item's one finish, and the run is cleaned up exactly once whatever ended it.
`step : RunPhase -> RunEvent -> RunPhase x List RunAction`: no clock (the beat is an event), no input or output, no text.

**A refused renewal means another host owns the item**: the worker is stopped, nothing is finished, nothing is reported. The same holds for the run's own deadline (a worker that never reports). **A worker that exits with no report** is not
finished either: the item's lease lapses and the queue offers it again. **A finish whose reply is lost, refused or unreachable** ends the run all the same; the store's finish is idempotent, and the work stays on its branch. -/
namespace VbmDispatcher

/-- What the worker reports once: its typed outcome and the commit the lander pushed, when it did. -/
structure Report where
  outcome : VbmWork.Outcome
  landed : Option String
  deriving DecidableEq, Repr

inductive RunPhase where
  | running
  /-- The worker is being stopped; nothing will be finished. -/
  | stopping
  | finishing (r : Report)
  | cleaning
  | closed
  deriving DecidableEq, Repr

inductive RunEvent where
  | beat
  | renewed
  | renewRefused
  | renewUnreachable
  | workerReported (r : Report)
  | workerGone
  | workerStopped
  | finished
  | finishRefused
  | finishUnreachable
  | cleaned
  | deadline
  deriving DecidableEq, Repr

inductive RunAction where
  | renew
  | stopWorker
  | finish (r : Report)
  | cleanup
  deriving DecidableEq, Repr

/-- A run starts with its worker running and nothing asked. -/
def Run.start : RunPhase × List RunAction := (.running, [])

/-- The machine. A pair no rule names is IGNORED: a late report after the run was abandoned finishes nothing, and a beat after the run ended renews nothing. -/
def Run.step : RunPhase → RunEvent → RunPhase × List RunAction
  | .running, .beat => (.running, [.renew])
  | .running, .renewed => (.running, [])
  | .running, .renewUnreachable => (.running, [])
  | .running, .renewRefused => (.stopping, [.stopWorker])
  | .running, .deadline => (.stopping, [.stopWorker])
  | .running, .workerReported r => (.finishing r, [.finish r])
  | .running, .workerGone => (.cleaning, [.cleanup])
  | .stopping, .workerStopped => (.cleaning, [.cleanup])
  | .stopping, .workerGone => (.cleaning, [.cleanup])
  | .finishing _, .finished => (.cleaning, [.cleanup])
  | .finishing _, .finishRefused => (.cleaning, [.cleanup])
  | .finishing _, .finishUnreachable => (.cleaning, [.cleanup])
  | .cleaning, .cleaned => (.closed, [])
  | s, _ => (s, [])

/-- Feed events in order from a phase; the actions in the order they were asked. -/
def Run.run : RunPhase → List RunEvent → RunPhase × List RunAction
  | s, [] => (s, [])
  | s, e :: es =>
    let r := Run.step s e
    let t := Run.run r.1 es
    (t.1, r.2 ++ t.2)

end VbmDispatcher
