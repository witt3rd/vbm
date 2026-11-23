import VbmDispatcher
/-! # The run's claims

Every theorem says what it rules out. The witnesses at the end show each hypothesis can hold. -/
namespace VbmDispatcher

def finishes : List RunAction → Nat
  | [] => 0
  | .finish _ :: as => 1 + finishes as
  | _ :: as => finishes as

def cleanups : List RunAction → Nat
  | [] => 0
  | .cleanup :: as => 1 + cleanups as
  | _ :: as => cleanups as

theorem finishes_append (a b : List RunAction) : finishes (a ++ b) = finishes a + finishes b := by
  induction a with
  | nil => simp [finishes]
  | cons x xs ih => cases x <;> simp [finishes, ih] <;> omega

theorem cleanups_append (a b : List RunAction) : cleanups (a ++ b) = cleanups a + cleanups b := by
  induction a with
  | nil => simp [cleanups]
  | cons x xs ih => cases x <;> simp [cleanups, ih] <;> omega

/-- How many finishes a phase can still produce: one while the worker runs, none after. -/
def finishRoom : RunPhase → Nat
  | .running => 1
  | _ => 0

/-- **A closed run is absorbing**: nothing it is told changes it or asks for anything. -/
theorem run_closed_absorbing (e : RunEvent) : Run.step .closed e = (.closed, []) := by
  cases e <;> rfl

/-- **Renewal only while the worker runs, and only at a beat**: no other phase or event can ask for it (a beat after the run ended renews nothing). -/
theorem run_renews_only_at_beat (p : RunPhase) (e : RunEvent) (h : RunAction.renew ∈ (Run.step p e).2) : p = .running ∧ e = .beat := by
  cases p <;> cases e <;> simp [Run.step] at h ⊢

/-- **The finish is the worker's own report, unchanged**: a finish is asked only while the worker runs and only for the report it just made. -/
theorem run_finishes_only_the_report (p : RunPhase) (e : RunEvent) (r : Report) (h : RunAction.finish r ∈ (Run.step p e).2) :
    p = .running ∧ e = .workerReported r := by
  cases p <;> cases e <;> simp [Run.step] at h ⊢ <;> first | exact h | exact h.symm

/-- **A refused renewal reports nothing**: the worker is stopped and the machine waits for it to be gone. -/
theorem run_lost_lease_stops_worker : Run.step .running .renewRefused = (.stopping, [.stopWorker]) := rfl

/-- **The run's deadline reports nothing either.** -/
theorem run_deadline_stops_worker : Run.step .running .deadline = (.stopping, [.stopWorker]) := rfl

/-- **An abandoned run never finishes**: once the worker is being stopped, a late report is ignored. -/
theorem run_stopping_ignores_report (r : Report) : Run.step .stopping (.workerReported r) = (.stopping, []) := rfl

/-- One step: the finishes asked for plus the finish room after it fit in the room before. -/
theorem run_step_finish_room (p : RunPhase) (e : RunEvent) : finishes (Run.step p e).2 + finishRoom (Run.step p e).1 ≤ finishRoom p := by
  cases p <;> cases e <;> simp [Run.step, finishes, finishRoom]

/-- **An item is finished at most once**, whatever the run is told. -/
theorem run_finishes_at_most_once (p : RunPhase) (es : List RunEvent) : finishes (Run.run p es).2 ≤ finishRoom p := by
  induction es generalizing p with
  | nil => simp [Run.run, finishes]
  | cons e es ih =>
    have h1 := run_step_finish_room p e
    have h2 := ih (Run.step p e).1
    simp only [Run.run, finishes_append]
    omega

/-- The cleanups a phase still owes: one until the worker's end has been seen, none once the cleanup has been ASKED (`cleaning`) or the run is closed. -/
def owes : RunPhase → Nat
  | .running | .stopping | .finishing _ => 1
  | .cleaning | .closed => 0

/-- One step conserves the cleanups: what it asks for plus what is still owed after it equals what was owed before. The machine never loses a cleanup and never asks one twice. -/
theorem run_step_clean_conserved (p : RunPhase) (e : RunEvent) : cleanups (Run.step p e).2 + owes (Run.step p e).1 = owes p := by
  cases p <;> cases e <;> simp [Run.step, cleanups, owes]

/-- The same for any run of events: the cleanups asked plus the cleanups still owed at the end equal the cleanups owed at the start. -/
theorem run_clean_conserved (p : RunPhase) (es : List RunEvent) : cleanups (Run.run p es).2 + owes (Run.run p es).1 = owes p := by
  induction es generalizing p with
  | nil => simp [Run.run, cleanups]
  | cons e es ih =>
    have h1 := run_step_clean_conserved p e
    have h2 := ih (Run.step p e).1
    simp only [Run.run, cleanups_append]
    omega

/-- **A run is cleaned up at most once**, whatever it is told. -/
theorem run_cleans_at_most_once (p : RunPhase) (es : List RunEvent) : cleanups (Run.run p es).2 ≤ owes p := by
  have := run_clean_conserved p es
  omega

/-- **A run that closes was cleaned up exactly once**: from a phase that still owes its cleanup (the start is one), reaching `closed` asks for exactly one cleanup. -/
theorem run_closed_means_cleaned (p : RunPhase) (es : List RunEvent) (hp : owes p = 1) (h : (Run.run p es).1 = .closed) :
    cleanups (Run.run p es).2 = 1 := by
  have := run_clean_conserved p es
  rw [h] at this
  have h0 : owes RunPhase.closed = 0 := rfl
  omega

/-- The shape of an action and of a phase, without any report inside. -/
def RunAction.kind : RunAction → Nat
  | .renew => 0 | .stopWorker => 1 | .finish _ => 2 | .cleanup => 3

def RunPhase.kind : RunPhase → Nat
  | .running => 0 | .stopping => 1 | .finishing _ => 2 | .cleaning => 3 | .closed => 4

/-- **Control never depends on the report's content**: two different reports, whatever the outcome or text inside them, give the same phase shape and the same actions shape. The machine never reads prose. -/
theorem run_ignores_report_content (p : RunPhase) (r r' : Report) :
    (Run.step p (.workerReported r)).1.kind = (Run.step p (.workerReported r')).1.kind ∧
    (Run.step p (.workerReported r)).2.map RunAction.kind = (Run.step p (.workerReported r')).2.map RunAction.kind := by
  cases p <;> simp [Run.step, RunPhase.kind, RunAction.kind]

/-! ## Witnesses: each hypothesis above can hold -/

def rep₀ : Report := ⟨.done [], some "abc"⟩

/-- The whole happy run: a beat, a renewal, the worker's report, the finish, the cleanup: one finish, one cleanup, closed. -/
example : Run.run .running [.beat, .renewed, .workerReported rep₀, .finished, .cleaned] = (.closed, [.renew, .finish rep₀, .cleanup]) := by decide

/-- A lost lease: the worker is stopped, nothing is finished, the run is cleaned and closed. -/
example : Run.run .running [.beat, .renewRefused, .workerReported rep₀, .workerStopped, .cleaned] = (.closed, [.renew, .stopWorker, .cleanup]) := by decide

/-- A worker that exits without a report: no finish, one cleanup. -/
example : Run.run .running [.workerGone, .cleaned] = (.closed, [.cleanup]) := by decide

/-- A late beat after the run ended renews nothing. -/
example : Run.step .closed .beat = (.closed, []) := by decide

end VbmDispatcher
