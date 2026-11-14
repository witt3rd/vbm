import VbmDispatcher.Model
/-! # The conformance scenarios

Each is a configuration (the tick's) and the events a port-disciplined run raises. The machine's answers (the actions) are NOT written here: the machine computes them and the vector generator writes both. An interpreter conforms when, with its
ports answering the events in order, it makes exactly the calls the vector lists. -/
namespace VbmDispatcher
open Pool VbmWork

inductive Scenario where
  | tick (name : String) (cfg : TickConfig) (events : List TickEvent)
  | run (name : String) (events : List RunEvent)

def Scenario.name : Scenario → String
  | .tick n _ _ => n
  | .run n _ => n

private def cfg0 : TickConfig := ⟨pr₀, hq 1⟩
private def cfgLean : TickConfig := ⟨pr₀, hq 1 ["lean"]⟩
private def cfgDrain : TickConfig := ⟨pr₀, ⟨1, [], true⟩⟩
private def lcBusy : Local := { lc₀ 0 with cpuPressure := 900 }
private def lcFull : Local := { lc₀ 0 with diskFreeGb := 1 }
private def lcOff : Local := { lc₀ 0 with off := true }
private def qOne : Queue := ⟨[⟨item 7, .pending, 0, []⟩]⟩
private def qTwo : Queue := ⟨[⟨item 7 (prio := 1), .pending, 0, []⟩, ⟨item 9 (prio := 5), .pending, 0, []⟩]⟩
private def qDep : Queue := ⟨[⟨item 7 (deps := [3]), .pending, 0, []⟩]⟩
private def qKey : Queue := ⟨[⟨item 6 (keys := ["file:a"]), .running ⟨2⟩, 0, []⟩, ⟨item 7 (keys := ["file:a"]), .pending, 0, []⟩]⟩
private def qNeeds : Queue := ⟨[⟨item 7 (needs := ["lean"]), .pending, 0, []⟩]⟩
private def qDefer : Queue := ⟨[⟨item 7, .pending, 0, [1]⟩]⟩
private def rep1 : Report := ⟨.done [], some "abc1234"⟩
private def repBlocked : Report := ⟨.blocked .noFinish "no typed end" [], none⟩

def scenarios : List Scenario := [
  .tick "happy-claim" cfg0 [.readings (lc₀ 0), .queue qOne, .claimWon 41 1],
  .tick "skipped-no-headroom" cfg0 [.readings lcBusy],
  .tick "skipped-disk-floor" cfg0 [.readings lcFull],
  .tick "skipped-off-switch" cfg0 [.readings lcOff],
  .tick "skipped-draining" cfgDrain [.readings (lc₀ 0)],
  .tick "idle-empty-queue" cfg0 [.readings (lc₀ 0), .queue Queue.empty],
  .tick "highest-priority-first" cfg0 [.readings (lc₀ 0), .queue qTwo, .claimWon 52 1],
  .tick "idle-dependency-unmet" cfg0 [.readings (lc₀ 0), .queue qDep],
  .tick "idle-serialisation-key-held" cfg0 [.readings (lc₀ 0), .queue qKey],
  .tick "idle-label-not-held" cfg0 [.readings (lc₀ 0), .queue qNeeds],
  .tick "claims-when-label-held" cfgLean [.readings (lc₀ 0), .queue qNeeds, .claimWon 60 1],
  .tick "idle-deferred-to-others" cfg0 [.readings (lc₀ 0), .queue qDefer],
  .tick "lost-race-then-won" cfg0 [.readings (lc₀ 0), .queue qTwo, .claimLost, .queue qOne, .claimWon 52 2],
  .tick "lost-race-then-idle" cfg0 [.readings (lc₀ 0), .queue qOne, .claimLost, .queue Queue.empty],
  .tick "store-down-reading-the-queue" cfg0 [.readings (lc₀ 0), .storeDown],
  .tick "store-down-claiming" cfg0 [.readings (lc₀ 0), .queue qOne, .storeDown],
  .tick "store-down-after-a-lost-race" cfg0 [.readings (lc₀ 0), .queue qOne, .claimLost, .storeDown],
  .run "happy-run" [.beat, .renewed, .workerReported rep1, .finished, .cleaned],
  .run "several-beats" [.beat, .renewed, .beat, .renewed, .beat, .renewed, .workerReported rep1, .finished, .cleaned],
  .run "renewal-unreachable-then-renewed" [.beat, .renewUnreachable, .beat, .renewed, .workerReported rep1, .finished, .cleaned],
  .run "lost-lease" [.beat, .renewRefused, .workerStopped, .cleaned],
  .run "deadline" [.beat, .renewed, .deadline, .workerStopped, .cleaned],
  .run "worker-gone-without-a-report" [.beat, .renewed, .workerGone, .cleaned],
  .run "worker-exits-while-being-stopped" [.beat, .renewRefused, .workerGone, .cleaned],
  .run "finish-refused" [.workerReported rep1, .finishRefused, .cleaned],
  .run "finish-unreachable" [.workerReported rep1, .finishUnreachable, .cleaned],
  .run "blocked-report-is-finished-as-it-is" [.beat, .renewed, .workerReported repBlocked, .finished, .cleaned],
  .run "reported-at-once" [.workerReported rep1, .finished, .cleaned]]

end VbmDispatcher
