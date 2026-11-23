import VbmDispatcher
/-! # The scenarios obey the port discipline -/
namespace VbmDispatcher

def Scenario.obeys : Scenario → Bool
  | .tick _ cfg events => (runTick cfg events).toBool
  | .run _ events => (runRun events).toBool

/-- **Every conformance scenario is one a correct interpreter can meet**: each runs under the port discipline of its reference model (every event answers a pending action or is the world's own, and no world event is ignored), so the vectors never ask an interpreter for something no port could produce. -/
theorem scenarios_obey_the_discipline : scenarios.all Scenario.obeys = true := by decide

/-- Non-vacuity: the discipline CAN refuse: an answer to nothing, and a world event after the run closed. -/
example : (runTick ⟨Pool.pr₀, Pool.hq 1⟩ [.claimWon 1 1]).toBool = false := by decide
example : (runRun [.workerGone, .cleaned, .beat]).toBool = false := by decide

end VbmDispatcher
