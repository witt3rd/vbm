import VbmDispatcher.Pool
/-! # VbmDispatcher.Tick: one host's tick, as a pure machine

A host's dispatcher wakes every period and does one thing: read itself, and if it has headroom read the queue, choose the next item (`Pool.choose`), claim exactly that item, and hand the claimed item to a run. This machine is that sequence and nothing else:
`step : TickConfig -> TickPhase -> TickEvent -> TickPhase x List TickAction`, typed events in and typed actions out. It has no clock (the tick's `now` arrives inside the host's readings), no input or output, and it reads no text.

A tick ends in exactly one of four ways: `skipped` (the guard `Pool.ready` said the host has no headroom, is off or is draining: nothing was read from the queue and nothing was written), `idle` (nothing to choose),
`storeUnreachable` (the queue could not be reached: fail-stop, nothing started, never a local spool), or `started` (this host won the claim of the item `choose` returned: the message and the delivery number come from the store, and the run starts).
A claim lost to another host is not an end: the tick reads the queue again and chooses again from the fresh snapshot (no cap: it ends when nothing is chosen or a claim is won). -/
namespace VbmDispatcher
open Pool

/-- The host's own facts that do not change between ticks: the pool's parameters (the host's DATA: no default here) and who this host is. -/
structure TickConfig where
  params : Params
  me : Quals
  deriving DecidableEq, Repr

/-- How a tick ended. `started` carries what a run needs: the item, the store's message id and the delivery number (the fencing token every later renewal and the finish are made under). -/
inductive TickResult where
  | skipped
  | idle
  | storeUnreachable
  | started (id : ItemId) (msg gen : Nat)
  deriving DecidableEq, Repr

inductive TickPhase where
  | reading
  | listing (lc : Local)
  | claiming (id : ItemId) (lc : Local)
  | ended (r : TickResult)
  deriving DecidableEq, Repr

/-- What the world answers: the host's readings, the queue's snapshot, the claim's result, or that the store cannot be reached. -/
inductive TickEvent where
  | readings (lc : Local)
  | queue (q : Queue)
  | storeDown
  | claimWon (msg gen : Nat)
  | claimLost
  deriving DecidableEq, Repr

/-- What the machine asks an interpreter to do. `endTick` is the end: the interpreter starts a run when its result is `started`. -/
inductive TickAction where
  | readHost
  | readQueue
  | claim (id : ItemId)
  | endTick (r : TickResult)
  deriving DecidableEq, Repr

/-- The tick begins by reading the host. -/
def Tick.start : TickPhase × List TickAction := (.reading, [.readHost])

/-- The machine. Every pair of phase and event that no rule names is IGNORED (the state is kept and nothing is asked): an answer that does not belong to the question asked cannot start anything, and a finished tick is absorbing. -/
def Tick.step (cfg : TickConfig) : TickPhase → TickEvent → TickPhase × List TickAction
  | .reading, .readings lc =>
      if ready cfg.params cfg.me lc then (.listing lc, [.readQueue]) else (.ended .skipped, [.endTick .skipped])
  | .listing lc, .queue q =>
      match choose cfg.params q cfg.me lc with
      | none => (.ended .idle, [.endTick .idle])
      | some id => (.claiming id lc, [.claim id])
  | .claiming id _, .claimWon msg gen => (.ended (.started id msg gen), [.endTick (.started id msg gen)])
  | .claiming _ lc, .claimLost => (.listing lc, [.readQueue])
  | .listing _, .storeDown => (.ended .storeUnreachable, [.endTick .storeUnreachable])
  | .claiming _ _, .storeDown => (.ended .storeUnreachable, [.endTick .storeUnreachable])
  | s, _ => (s, [])

/-- Feed events in order from a phase; the actions in the order they were asked. -/
def Tick.run (cfg : TickConfig) : TickPhase → List TickEvent → TickPhase × List TickAction
  | s, [] => (s, [])
  | s, e :: es =>
    let r := Tick.step cfg s e
    let t := Tick.run cfg r.1 es
    (t.1, r.2 ++ t.2)

end VbmDispatcher
