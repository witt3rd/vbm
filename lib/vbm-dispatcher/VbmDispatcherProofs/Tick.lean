import VbmDispatcher
/-! # The tick's claims

Every theorem says what it rules out. The witnesses at the end show each hypothesis can hold. -/
namespace VbmDispatcher
open Pool

/-- How many `endTick` actions a list holds. -/
def ends : List TickAction → Nat
  | [] => 0
  | .endTick _ :: as => 1 + ends as
  | _ :: as => ends as

theorem ends_append (a b : List TickAction) : ends (a ++ b) = ends a + ends b := by
  induction a with
  | nil => simp [ends]
  | cons x xs ih => cases x <;> simp [ends, ih] <;> omega

/-- The most `endTick`s a phase can still produce: none once ended, else one. -/
def room : TickPhase → Nat
  | .ended _ => 0
  | _ => 1

/-- **A finished tick is absorbing**: nothing it is told changes it or asks for anything (a late answer cannot restart a tick). -/
theorem tick_ended_absorbing (cfg : TickConfig) (r : TickResult) (e : TickEvent) : Tick.step cfg (.ended r) e = (.ended r, []) := by
  cases e <;> rfl

/-- **The guard comes first, and a refusal writes nothing**: when the host has no headroom (off, draining, pressure, memory or disk) the tick ends `skipped` and asks for nothing else: the queue is not even read. -/
theorem tick_no_headroom_ends_skipped (cfg : TickConfig) (lc : Local) (h : ready cfg.params cfg.me lc = false) :
    Tick.step cfg .reading (.readings lc) = (.ended .skipped, [.endTick .skipped]) := by
  simp [Tick.step, h]

/-- With headroom the next thing asked is the queue. -/
theorem tick_headroom_reads_queue (cfg : TickConfig) (lc : Local) (h : ready cfg.params cfg.me lc = true) :
    Tick.step cfg .reading (.readings lc) = (.listing lc, [.readQueue]) := by
  simp [Tick.step, h]

/-- **A claim is only ever for the item `choose` returned**, read from the snapshot the machine was given and the readings the guard passed: there is no other way to ask for a claim. -/
theorem tick_claims_only_chosen (cfg : TickConfig) (s : TickPhase) (e : TickEvent) (s' : TickPhase) (acts : List TickAction) (id : ItemId)
    (h : Tick.step cfg s e = (s', acts)) (hm : TickAction.claim id ∈ acts) :
    ∃ lc q, s = .listing lc ∧ e = .queue q ∧ choose cfg.params q cfg.me lc = some id := by
  cases s <;> cases e <;> simp only [Tick.step] at h <;> try split at h
  all_goals
    have h2 := congrArg Prod.snd h
    simp only at h2
    subst h2
    first
      | (simp at hm; done)
      | (simp at hm; subst hm; exact ⟨_, _, rfl, rfl, ‹_›⟩)

/-- **Only a won claim starts a run**: the result `started` is produced only from a claim in flight for that item, answered `claimWon` with the store's message and delivery number. -/
theorem tick_started_only_on_win (cfg : TickConfig) (s : TickPhase) (e : TickEvent) (s' : TickPhase) (acts : List TickAction) (id : ItemId) (msg gen : Nat)
    (h : Tick.step cfg s e = (s', acts)) (hm : TickAction.endTick (.started id msg gen) ∈ acts) :
    ∃ lc, s = .claiming id lc ∧ e = .claimWon msg gen := by
  cases s <;> cases e <;> simp only [Tick.step] at h <;> try split at h
  all_goals
    have h2 := congrArg Prod.snd h
    simp only at h2
    subst h2
    first
      | (simp at hm; done)
      | (simp at hm; obtain ⟨rfl, rfl, rfl⟩ := hm; exact ⟨_, rfl, rfl⟩)

/-- **A lost race starts nothing**: another host won the claim, so this tick reads the queue again and chooses again. -/
theorem tick_lost_race_starts_nothing (cfg : TickConfig) (id : ItemId) (lc : Local) :
    Tick.step cfg (.claiming id lc) .claimLost = (.listing lc, [.readQueue]) := by
  simp [Tick.step]

/-- **An unreachable store starts nothing**: the tick ends `storeUnreachable` (fail-stop, no local spool). -/
theorem tick_store_down_ends (cfg : TickConfig) (lc : Local) (id : ItemId) :
    Tick.step cfg (.listing lc) .storeDown = (.ended .storeUnreachable, [.endTick .storeUnreachable]) ∧
    Tick.step cfg (.claiming id lc) .storeDown = (.ended .storeUnreachable, [.endTick .storeUnreachable]) := by
  simp [Tick.step]

/-- One step never ends a tick that has ended, and ends at most once: the ends it asks for plus the room left after it fit in the room before. -/
theorem tick_step_room (cfg : TickConfig) (s : TickPhase) (e : TickEvent) :
    ends (Tick.step cfg s e).2 + room (Tick.step cfg s e).1 ≤ room s := by
  cases s <;> cases e <;> simp only [Tick.step] <;> try split
  all_goals simp [ends, room]

/-- **A tick ends at most once**, whatever it is told. -/
theorem tick_ends_at_most_once (cfg : TickConfig) (s : TickPhase) (es : List TickEvent) : ends (Tick.run cfg s es).2 ≤ room s := by
  induction es generalizing s with
  | nil => simp [Tick.run, ends]
  | cons e es ih =>
    have h1 := tick_step_room cfg s e
    have h2 := ih (Tick.step cfg s e).1
    simp only [Tick.run, ends_append]
    omega

/-! ## Witnesses: each hypothesis above can hold -/

/-- A host with room, and a queue holding one pending item it is qualified for. -/
def cfg₀ : TickConfig := ⟨pr₀, hq 1⟩
def q₀ : Queue := ⟨[⟨item 7, .pending, 0, [], 0⟩]⟩

/-- The whole happy tick: readings with headroom, the queue, a won claim: the tick ends having started item 7. -/
example : (Tick.run cfg₀ .reading [.readings (lc₀ 0), .queue q₀, .claimWon 41 1]).1 = .ended (.started 7 41 1) := by decide

/-- A lost race reads the queue again; when the item is gone the tick ends idle. -/
example : (Tick.run cfg₀ .reading [.readings (lc₀ 0), .queue q₀, .claimLost, .queue Queue.empty]).1 = .ended .idle := by decide

/-- **A machine under pressure has no headroom, whatever the slice says.** The machine's CPU pressure at or above its ceiling makes the host claim nothing, though its own slice is idle (an idle slice feels no
pressure of its own: it cannot see a box that someone else is drowning). Rules out a host claiming onto a machine whose kernel says its tasks are waiting for a CPU. -/
theorem ready_machine_cpu_busy (pr : Params) (me : Quals) (lc : Local) (h : pr.sysCpuCeil ≤ lc.sysCpuPressure) : ready pr me lc = false := by
  have : ¬ lc.sysCpuPressure < pr.sysCpuCeil := Nat.not_lt.mpr h
  simp [ready, this]

/-- **The same for memory**: every task of the machine stalled on memory for at least the ceiling's share of the last 10 s means no headroom. -/
theorem ready_machine_memory_stalled (pr : Params) (me : Quals) (lc : Local) (h : pr.sysMemCeil ≤ lc.sysMemPressure) : ready pr me lc = false := by
  have : ¬ lc.sysMemPressure < pr.sysMemCeil := Nat.not_lt.mpr h
  simp [ready, this]

/-- Non-vacuity: the hypothesis of `ready_machine_cpu_busy` can hold with an idle slice, and the same host with a quiet machine IS ready (so the guard does not simply refuse everything). -/
example : ready cfg₀.params cfg₀.me { lc₀ 0 with sysCpuPressure := 900 } = false := by decide
example : ready cfg₀.params cfg₀.me { lc₀ 0 with sysMemPressure := 400 } = false := by decide
example : ready cfg₀.params cfg₀.me (lc₀ 0) = true := by decide

/-- A host with no headroom (a pressure above the ceiling) ends skipped, and asks for nothing but its own end. -/
example : (Tick.run cfg₀ .reading [.readings { lc₀ 0 with cpuPressure := 900 }]) = (.ended .skipped, [.endTick .skipped]) := by decide

/-- The claim is for the chosen item. -/
example : choose cfg₀.params q₀ cfg₀.me (lc₀ 0) = some 7 := by decide

end VbmDispatcher
