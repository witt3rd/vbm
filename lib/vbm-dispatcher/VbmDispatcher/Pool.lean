import VbmWork
/-! # VbmDispatcher.Pool: a leased work queue as ROWS and PORT LAWS, and the per-host claim step `choose`.
Specification: any leased queue that meets the port's laws implements the store, and the dispatcher's machines (`VbmDispatcher.Tick`, `VbmDispatcher.Run`) are handlers of `choose`. Total functions.

Two halves. (1) `choose`, UNCHANGED from the event-log shape (types, aging, determinism, the gates): a pure function of a SNAPSHOT of the queue, this host's qualifications and its own slice's headroom.
A host's SHARE of the machine is the kernel's (a cgroup CPU quota on the slice the pool runs in): the spec counts no items per host and weighs none, and no host levels against another; `ready` reads the
slice's own pressure and memory use, never the machine's load average.
(2) the STORE, as rows and not as a log: a leased queue with five operations (send, claim, renew, finish, and the snapshot that `choose` reads), whose laws are the conformance suite (pool/conformance.sh):
sent once, a live claim excludes every other host, a takeover after expiry raises the delivery number (the fencing token: the fencing law (`takeover_raises_gen`)), renew and finish are fenced by it, finish is
idempotent on retry, a finished id is never sendable again, delay hides, exhaustion is derived. A log with a version compare-and-swap is gone: leases do not fit a log (a renewal every 30 s is event noise).
Serialisation keys are SOFT: `choose` skips an item whose key is held in its snapshot; two hosts claiming in one instant may both run (a typed conflict at the lander), so no invariant here claims otherwise. -/
namespace VbmDispatcher.Pool
abbrev ItemId := Nat
abbrev HostId := Nat
abbrev Key    := String   -- a serialisation key: "file:spec/Wake.lean", "chain:approval-17", "lander:main"
abbrev Label  := String   -- a capability: "lean", "gpu", "docker": an item NEEDS labels, a host HAS them

/-- A change's class: the vocabulary of `vbm-work`, one list for the whole family. -/
abbrev Class := VbmWork.ChangeClass

structure Item where
  id         : ItemId
  project    : Nat
  cls        : Class         -- DECLARED class: an upper bound the diff must stay under
  priority   : Nat           -- bigger is more urgent
  enqueuedAt : Nat   -- the tick it was enqueued at
  keys       : List Key      -- serialisation keys (declared, plus the named files)
  deps       : List ItemId   -- every one must be `landed` before this runs
  needs      : List Label    -- capabilities the host must have; no credential is a qualification
  retries    : Nat           -- how many times a lost run is started again
  deriving DecidableEq, Repr

/-- What a host IS: stable, recorded in the queue. -/
structure Quals where
  id       : HostId
  labels   : List Label
  draining : Bool := false
  deriving DecidableEq, Repr

/-- What a host reads about itself NOW: its own pool slice (a cgroup: CPU pressure and memory use against that slice's limit) and the store's disk and free memory. Transient, never recorded, never makes an
item unplaceable (a full disk is a guard, not an exclusion); the number of items it runs is not read here, because the kernel's quota on the slice bounds it. -/
structure Local where
  now            : Nat             -- the tick, as this host reads it
  off            : Bool := false   -- the host's off switch
  cpuPressure    : Nat             -- permille of the last 10 s that the host's pool slice waited for a CPU (the slice's PSI `some avg10`)
  memUsedPermille : Nat            -- the slice's memory in use, permille of its limit; 0 when it has none
  diskFreeGb     : Nat
  memFreeGb      : Nat
  deriving DecidableEq, Repr

structure Params where
  quantum      : Nat   -- ticks of waiting worth one priority point (read as at least 1)
  patience     : Nat   -- ticks an item a host lost waits before that host stops deferring it to the others
  pressureCeil : Nat   -- permille of CPU pressure at or above which the slice has no headroom
  memCeil      : Nat   -- permille of the slice's memory limit at or above which it has no headroom
  diskFloor    : Nat
  memFloor     : Nat
  deriving DecidableEq, Repr

/-- The transient guard of one host: pure in the host's own facts. The slice's headroom, not a count of items. -/
def ready (pr : Params) (me : Quals) (lc : Local) : Bool :=
  !lc.off && !me.draining && lc.cpuPressure < pr.pressureCeil && lc.memUsedPermille < pr.memCeil &&
    pr.diskFloor ≤ lc.diskFreeGb && pr.memFloor ≤ lc.memFreeGb

/-- The stable qualification: every needed label. How much of the machine the host has is the kernel's quota, not a count here. -/
def qualified (h : Quals) (it : Item) : Bool := it.needs.all (· ∈ h.labels)

inductive Gate | feasible | verifier | classCheck | validator | approval | lander
  deriving DecidableEq, Repr

def required : Class → List Gate
  | .scout => [.feasible, .classCheck]
  | .docs  => [.feasible, .verifier, .classCheck, .lander]
  | .impl  => [.feasible, .verifier, .classCheck, .validator, .lander]
  | .spec | .tightening | .infra | .loosening | .trustedC => [.feasible, .verifier, .classCheck, .validator, .approval, .lander]

structure Evidence where passed : List Gate deriving DecidableEq, Repr

def nextGate (c : Class) (ev : Evidence) : Option Gate := (required c).find? (· ∉ ev.passed)

inductive BlockKind | readOnlyPath | protectedPath | redBase | classExceeded | conflict | budget
  | lost | depFailed | unplaceable | gateFailed (g : Gate)
  deriving DecidableEq, Repr

/-- The typed outcome. `lost` is what a lapsed lease shows (derived, never written by a worker). -/
inductive Outcome
  | done (diff : Nat) | doneWithAssumptions (diff : Nat) | blocked (k : BlockKind) | needsClarification | lost
  deriving DecidableEq, Repr

/-- The holder of a LEASED delivery (the lease itself, its end and its number, live in the store: section "The store"). -/
structure Held where host : HostId deriving DecidableEq, Repr

inductive State
  | pending
  | claimed (w : Held)
  | running (w : Held)
  | gated   (w : Held) (ev : Evidence)
  | landed  (ev : Evidence)
  | blocked (k : BlockKind)
  | needsClarification
  | cancelled
  deriving DecidableEq, Repr

def State.holder? : State → Option Held
  | .claimed w | .running w | .gated w _ => some w
  | _ => none

def State.terminal : State → Bool
  | .landed _ | .blocked _ | .needsClarification | .cancelled => true
  | _ => false

structure Entry where
  item   : Item
  state  : State
  left   : Nat                 -- retries left
  lostOn : List HostId := []   -- hosts that lost it: they defer it to others for a while
  lostAt : Nat := 0            -- when the loss showed: the end of the lease that lapsed (the instant the patience counts from)
  deriving DecidableEq, Repr

/-- The queue as `choose` reads it: a SNAPSHOT of the store's live rows (see `rowEntry`). No registry of hosts: a host judges no other host (`ready` is its own slice), and nothing here levels. -/
structure Queue where
  entries : List Entry
  deriving DecidableEq, Repr

def Queue.empty : Queue := ⟨[]⟩

def Queue.find? (q : Queue) (id : ItemId) : Option Entry := q.entries.find? (·.item.id == id)
def Queue.holder? (q : Queue) (id : ItemId) : Option HostId := (q.find? id).bind fun e => e.state.holder?.map (·.host)
def Queue.stateOf (q : Queue) (id : ItemId) : Option State := (q.find? id).map (·.state)
def Queue.landedIds (q : Queue) : List ItemId :=
  q.entries.filterMap fun e => match e.state with | .landed _ => some e.item.id | _ => none
def Queue.depsMet (q : Queue) (it : Item) : Bool := it.deps.all (· ∈ q.landedIds)
def Queue.heldKeys (q : Queue) : List Key := (q.entries.filter (·.state.holder?.isSome)).flatMap (·.item.keys)
def Queue.keysFree (q : Queue) (it : Item) : Bool := it.keys.all (· ∉ q.heldKeys)
/-- Does this snapshot show the entry as claimable by `h`? The store re-checks only what it owns (the lease); dependencies, keys and the labels are the claimant's `choose`. No count of items per host is
checked here (nor anywhere): the kernel's quota on the host's slice and the guard (`ready`) bound what it runs. -/
def Queue.canClaim (q : Queue) (e : Entry) (h : Quals) : Bool :=
  e.state == .pending && q.depsMet e.item && q.keysFree e.item && qualified h e.item

def Queue.set (q : Queue) (id : ItemId) (f : Entry → Entry) : Queue :=
  { q with entries := q.entries.map fun e => if e.item.id == id then f e else e }


/-! ## The claim: what one host's dispatcher does. A pure function of the queue, this host's qualifications and its own load. -/

def eff (pr : Params) (now : Nat) (it : Item) : Nat := it.priority + (now - it.enqueuedAt) / max 1 pr.quantum

/-- Total order on items: effective priority (high first), then the older, then the smaller id. -/
def prec (pr : Params) (now : Nat) (a b : Item) : Bool :=
  eff pr now b < eff pr now a ||
  (eff pr now a == eff pr now b && (a.enqueuedAt < b.enqueuedAt || (a.enqueuedAt == b.enqueuedAt && a.id < b.id)))

def best? {α : Type} (lt : α → α → Bool) : List α → Option α
  | []      => none
  | x :: xs => some (xs.foldl (fun m y => if lt y m then y else m) x)

/-- A host that LOST the item defers it to the others, but only for `patience` ticks AFTER THE LOSS (`lostAt`, the end of the lease that lapsed), not after the item was enqueued: then any qualified ready host claims it. That is the only deferral: there is no leveling between hosts. -/
def deferred (pr : Params) (now : Nat) (me : Quals) (e : Entry) : Bool :=
  me.id ∈ e.lostOn && now < e.lostAt + pr.patience

/-- THE STEP OF THE PER-HOST DISPATCHER: nothing while the host's transient guard says no, else the best claimable, not deferred item this host
is qualified for. No central dispatcher: every host calls this on its own copy of the queue, then `Port.claimOver`. -/
def choose (pr : Params) (q : Queue) (me : Quals) (lc : Local) : Option ItemId :=
  if !ready pr me lc then none
  else (best? (prec pr lc.now) ((q.entries.filter fun e => q.canClaim e me && !deferred pr lc.now me e).map (·.item))).map (·.id)

def pr₀ : Params := ⟨10, 5, 750, 900, 20, 8⟩
def lc₀ (now : Nat := 0) : Local := ⟨now, false, 0, 0, 100, 30⟩   -- an idle host's slice with headroom and room on disk

/-- What the store's claim gives the claimant's copy of the queue: the item is held by `h` (the snapshot the next reader sees). -/
def Queue.take (q : Queue) (id : ItemId) (h : HostId) : Queue := q.set id fun e => { e with state := .claimed ⟨h⟩ }

/-- One round: each of these hosts runs its own dispatcher, in the order given, and takes what it chose. (Sequential: the concurrent case is the store's claim, `claim_exclusive`.) -/
def round (pr : Params) (hosts : List Quals) (L : HostId → Local) (q : Queue) : Queue :=
  hosts.foldl (fun q H => match choose pr q H (L H.id) with | none => q | some id => q.take id H.id) q

/-! ## Scenarios as examples (the acceptance tests of the design, closed by evaluation) -/
def hq (i : Nat) (labels : List Label := []) : Quals := ⟨i, labels, false⟩
def item (i : Nat) (prio : Nat := 1) (keys : List Key := []) (deps : List ItemId := []) (needs : List Label := []) : Item :=
  ⟨i, 0, .impl, prio, 0, keys, deps, needs, 1⟩
def mk (items : List Item) : Queue := ⟨items.map fun i => ⟨i, .pending, i.retries, [], 0⟩⟩
def holders (q : Queue) (ids : List ItemId) : List (Option HostId) := ids.map q.holder?

/-- "spread": six items, three equal idle hosts, each running ITS OWN dispatcher: two each, in a fixed order. -/
example : holders (round pr₀ [hq 1, hq 2, hq 3] (fun _ => lc₀) (round pr₀ [hq 1, hq 2, hq 3] (fun _ => lc₀) (mk ((List.range 6).map (item ∘ (· + 1)))))) [1,2,3,4,5,6]
    = [some 1, some 2, some 3, some 1, some 2, some 3] := by decide
-- The number of items a host runs is NO LONGER A SPEC CONCEPT: a host takes one item per `choose` and then chooses again, and what bounds how many it runs is the kernel's CPU quota on the pool's slice
-- and the guard (`ready`, from the slice's pressure and memory use), not a count kept here. Nothing in this file restricts a second claim.
/-- "serialise": two items with one key are never chosen together from one snapshot, even by different hosts. -/
example : holders (round pr₀ [hq 1, hq 2] (fun _ => lc₀) (mk [item 1 1 ["file:scripts/land-direct"], item 2 1 ["file:scripts/land-direct"]])) [1, 2]
    = [some 1, none] := by decide
/-- "dependency": the second item waits for the first to land. -/
example : holders (round pr₀ [hq 1] (fun _ => lc₀) (mk [item 1, item 2 1 [] [1]])) [1, 2] = [some 1, none] := by decide
/-- "needs lean": a host without the label chooses nothing; the host with it takes the item. -/
example : (choose pr₀ (mk [item 1 1 [] [] ["lean"]]) (hq 1) lc₀,
           choose pr₀ (mk [item 1 1 [] [] ["lean"]]) (hq 2 ["lean"]) lc₀) = (none, some 1) := by decide
/-- "a full disk is not an exclusion": below the floor the host claims nothing now, and with room it claims it. -/
example : let q := mk [item 1]
          let full : Local := ⟨0, false, 0, 0, 5, 30⟩
          (choose pr₀ q (hq 1) full, choose pr₀ q (hq 1) lc₀) = (none, some 1) := by decide
/-- "the slice has no headroom": a slice that waited for a CPU (`cpuPressure` over `pressureCeil`), or whose memory is at its limit (`memUsedPermille` over `memCeil`), claims nothing now and does once it
has headroom again. The machine's load average is not read anywhere: another host's work is the kernel's business, not this host's. -/
example : let q := mk [item 1]
          let busy : Local := ⟨0, false, 800, 0, 100, 30⟩
          let tight : Local := ⟨0, false, 0, 950, 100, 30⟩
          (choose pr₀ q (hq 1) busy, choose pr₀ q (hq 1) tight, choose pr₀ q (hq 1) lc₀) = (none, none, some 1) := by decide
/-- "host dies for good": its lease lapses, the row is claimable again, the dead host defers it (it is in `lostOn`) and another host takes it. -/
example : let q : Queue := ⟨[⟨item 1, .pending, 0, [1], 0⟩]⟩
          (choose pr₀ q (hq 1) (lc₀ 1), choose pr₀ q (hq 2) (lc₀ 1)) = (none, some 1) := by decide

theorem quantum_pos (n : Nat) : 0 < max 1 n := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

/-- (g) NO STARVATION. Aging: waiting raises effective priority without bound. -/
theorem eff_unbounded (pr : Params) (it : Item) (B : Nat) : ∃ t, B ≤ eff pr t it := by
  refine ⟨it.enqueuedAt + B * max 1 pr.quantum, ?_⟩
  unfold eff
  rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (quantum_pos _)]
  omega

/-- A later arrival that comes after the aging bound (`maxPriority` quanta) never ranks ahead of an item already waiting: after that bound
only items that arrived before it can precede it, so none starves. -/
theorem no_overtake_after_aging (pr : Params) (maxPriority : Nat) (a b : Item) (t : Nat)
    (hp : b.priority ≤ maxPriority) (hlate : a.enqueuedAt < b.enqueuedAt) (hgap : a.enqueuedAt + maxPriority * max 1 pr.quantum ≤ b.enqueuedAt)
    (hb : b.enqueuedAt ≤ t) : prec pr t b a = false := by
  have hQ := quantum_pos pr.quantum
  have hef : eff pr t b ≤ eff pr t a := by
    unfold eff
    obtain ⟨Q, hQe⟩ : ∃ Q, Q = max 1 pr.quantum := ⟨_, rfl⟩
    rw [← hQe] at hQ hgap ⊢
    clear hQe
    have h3 : (t - b.enqueuedAt + maxPriority * Q) / Q ≤ (t - a.enqueuedAt) / Q := Nat.div_le_div_right (by omega)
    rw [Nat.add_mul_div_right _ _ hQ] at h3
    omega
  simp only [prec, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
  exact ⟨by omega, Or.inr ⟨by omega, Or.inl (by omega)⟩⟩


theorem guard_is_local (pr : Params) (q : Queue) (me : Quals) (lc : Local) (h : ready pr me lc = false) : choose pr q me lc = none := by
  simp [choose, h]


/-! ## What `choose` returns, and the queue's well-formedness -/
def WellFormed (q : Queue) : Prop := (q.entries.map (·.item.id)).Nodup

theorem inj_of_nodup_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hi : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd ⟨b, hb', hi.symm⟩ h.1
    · exact absurd ⟨a, ha', hi⟩ h.1
    · exact ih h.2 ha' hb'

theorem Queue.find?_some {q : Queue} {id : ItemId} {e : Entry} (h : q.find? id = some e) : e ∈ q.entries ∧ e.item.id = id :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩


theorem best?_mem {α : Type} (lt : α → α → Bool) (l : List α) (m : α) (h : best? lt l = some m) : m ∈ l := by
  have key : ∀ (xs : List α) (x : α), xs.foldl (fun m y => if lt y m then y else m) x ∈ x :: xs := by
    intro xs
    induction xs with
    | nil => intro x; simp
    | cons y ys ih =>
      intro x
      have := ih (if lt y x then y else x)
      simp only [List.foldl_cons]
      by_cases hl : lt y x = true
      · simp [hl] at this ⊢; exact Or.inr this
      · simp [hl] at this ⊢
        rcases this with h | h <;> simp [h]
  cases l with
  | nil => simp [best?] at h
  | cons x xs => simp only [best?, Option.some.injEq] at h; subst h; exact key xs x

theorem best?_isSome {α : Type} (lt : α → α → Bool) (l : List α) (x : α) (hx : x ∈ l) : (best? lt l).isSome = true := by
  cases l with
  | nil => simp at hx
  | cons y ys => simp [best?]

theorem find?_of_mem {q : Queue} (hw : WellFormed q) {e : Entry} (he : e ∈ q.entries) : q.find? e.item.id = some e := by
  cases hf : q.find? e.item.id with
  | none => exact absurd (List.find?_eq_none.1 hf e he) (by simp)
  | some x =>
    obtain ⟨hm, hi⟩ := Queue.find?_some hf
    have hw' : (q.entries.map (·.item.id)).Nodup := hw
    simp only [inj_of_nodup_map (·.item.id) hw' hm he hi]

/-- What `choose` returns, unpacked: a ready host, and an entry that is claimable by it and not deferred. -/
theorem choose_entry (pr : Params) (q : Queue) (me : Quals) (lc : Local) (id : ItemId) (hw : WellFormed q) (h : choose pr q me lc = some id) :
    ready pr me lc = true ∧ ∃ e, q.find? id = some e ∧ q.canClaim e me = true ∧ deferred pr lc.now me e = false := by
  unfold choose at h
  split at h
  · simp at h
  · rename_i hr
    refine ⟨by simpa using hr, ?_⟩
    obtain ⟨it, hit, rfl⟩ := Option.map_eq_some_iff.1 h
    have := best?_mem _ _ _ hit
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 this
    obtain ⟨he', hp⟩ := List.mem_filter.1 he
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact ⟨e, find?_of_mem hw he', hp.1, hp.2⟩

theorem choose_requires_qualified (pr : Params) (q : Queue) (me : Quals) (lc : Local) (id : ItemId) (hw : WellFormed q)
    (h : choose pr q me lc = some id) : ∃ e, q.find? id = some e ∧ qualified me e.item = true := by
  obtain ⟨-, e, hf, hc, -⟩ := choose_entry pr q me lc id hw h
  simp only [Queue.canClaim, Bool.and_eq_true] at hc
  exact ⟨e, hf, hc.2⟩

/-- A host that never lost an item is never deferred off it: nothing is levelled away from it. -/
theorem deferred_of_not_lost (pr : Params) (now : Nat) (me : Quals) (e : Entry) (hnl : me.id ∉ e.lostOn) :
    deferred pr now me e = false := by
  simp [deferred, hnl]

/-- A host that DID lose the item defers it to the others for `patience` ticks after it was enqueued. -/
theorem lost_item_deferred (pr : Params) (now : Nat) (me : Quals) (e : Entry) (hl : me.id ∈ e.lostOn)
    (hyoung : now < e.lostAt + pr.patience) : deferred pr now me e = true := by
  simp [deferred, hl, hyoung]

theorem patience_bounds_deferral (pr : Params) (q : Queue) (me : Quals) (lc : Local) (e : Entry) (he : e ∈ q.entries)
    (hr : ready pr me lc = true) (hc : q.canClaim e me = true) (old : e.lostAt + pr.patience ≤ lc.now) :
    (choose pr q me lc).isSome = true := by
  unfold choose
  simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false, Option.isSome_map]
  apply best?_isSome _ _ e.item
  refine List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, ?_⟩, rfl⟩
  have : ¬ lc.now < e.lostAt + pr.patience := Nat.not_lt.2 old
  simp [deferred, hc, this]


theorem required_pos (c : Class) : 0 < (required c).length := by cases c <;> decide
theorem required_lt (c : Class) : (required c).length < 7 := by cases c <;> decide
theorem nextGate_take (c : Class) : ∀ k, k < 7 → nextGate c ⟨(required c).take k⟩ = (required c)[k]? := by cases c <;> decide

theorem gate_progress (c : Class) (ev : Evidence) (g : Gate) (hok : ∃ k, k < (required c).length ∧ ev.passed = (required c).take k)
    (hn : nextGate c ev = some g) :
    ∃ k, k < (required c).length ∧ (⟨ev.passed ++ [g]⟩ : Evidence) = ⟨(required c).take (k + 1)⟩ ∧ nextGate c ⟨ev.passed ++ [g]⟩ = (required c)[k + 1]? := by
  obtain ⟨k, hk, hp⟩ := hok
  have hlt := required_lt c
  have h1 : ev = ⟨(required c).take k⟩ := by cases ev; simp_all
  rw [h1, nextGate_take c k (by omega)] at hn
  have h2 : (⟨ev.passed ++ [g]⟩ : Evidence) = ⟨(required c).take (k + 1)⟩ := by
    rw [hp, List.take_add_one, hn]; rfl
  exact ⟨k, hk, h2, by rw [h2]; exact nextGate_take c (k + 1) (by omega)⟩

/-! ## Determinism: `choose` reads the queue as a set (entries up to order), so every host computing it from one snapshot agrees. -/
theorem prec_trans (pr : Params) (now : Nat) (a b c : Item) (h₁ : prec pr now a b = true) (h₂ : prec pr now b c = true) : prec pr now a c = true := by
  simp only [prec, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  dsimp only [ItemId] at *
  omega

theorem prec_asym (pr : Params) (now : Nat) (a b : Item) (h₁ : prec pr now a b = true) (h₂ : prec pr now b a = true) : False := by
  simp only [prec, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  dsimp only [ItemId] at *
  omega

theorem prec_total (pr : Params) (now : Nat) (a b : Item) (h : a.id ≠ b.id) : prec pr now a b = true ∨ prec pr now b a = true := by
  simp only [prec, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  dsimp only [ItemId] at *
  omega

theorem foldl_min {α : Type} (lt : α → α → Bool) (S : List α) (htr : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, lt a b = true → lt b c = true → lt a c = true)
    (htot : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → lt a b = true ∨ lt b a = true) :
    ∀ (xs : List α) (m : α), m ∈ S → (∀ x ∈ xs, x ∈ S) →
      (xs.foldl (fun m y => if lt y m then y else m) m ∈ S) ∧
      ∀ z ∈ m :: xs, z = xs.foldl (fun m y => if lt y m then y else m) m ∨ lt (xs.foldl (fun m y => if lt y m then y else m) m) z = true := by
  intro xs
  induction xs with
  | nil => intro m hm _; simp [hm]
  | cons y ys ih =>
    intro m hm hys
    have hy : y ∈ S := hys y List.mem_cons_self
    have hys' : ∀ x ∈ ys, x ∈ S := fun x hx => hys x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons]
    by_cases hl : lt y m = true
    · simp only [hl, ite_true]
      obtain ⟨hr, hmin⟩ := ih y hy hys'
      refine ⟨hr, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · rcases hmin y List.mem_cons_self with h | h
        · exact Or.inr (h ▸ hl)
        · exact Or.inr (htr _ hr _ hy _ hm h hl)
      · exact hmin z hz
    · simp only [hl, Bool.false_eq_true, ite_false]
      obtain ⟨hr, hmin⟩ := ih m hm hys'
      refine ⟨hr, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hmin z List.mem_cons_self
      · rcases List.mem_cons.1 hz with rfl | hz
        · by_cases hym : z = m
          · exact hmin z (hym ▸ List.mem_cons_self)
          · have hmy : lt m z = true := by
              rcases htot z hy m hm hym with h | h
              · exact absurd h hl
              · exact h
            rcases hmin m List.mem_cons_self with h | h
            · exact Or.inr (h ▸ hmy)
            · exact Or.inr (htr _ hr _ hm _ hy h hmy)
        · exact hmin z (List.mem_cons_of_mem _ hz)

theorem best?_perm {α : Type} (lt : α → α → Bool) {l l' : List α} (hp : l.Perm l')
    (htr : ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, lt a b = true → lt b c = true → lt a c = true)
    (hasym : ∀ a ∈ l, ∀ b ∈ l, lt a b = true → lt b a = true → False)
    (htot : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → lt a b = true ∨ lt b a = true) : best? lt l = best? lt l' := by
  have htr' : ∀ a ∈ l', ∀ b ∈ l', ∀ c ∈ l', lt a b = true → lt b c = true → lt a c = true :=
    fun a ha b hb c hc => htr a (hp.mem_iff.2 ha) b (hp.mem_iff.2 hb) c (hp.mem_iff.2 hc)
  have htot' : ∀ a ∈ l', ∀ b ∈ l', a ≠ b → lt a b = true ∨ lt b a = true :=
    fun a ha b hb => htot a (hp.mem_iff.2 ha) b (hp.mem_iff.2 hb)
  cases hl : l with
  | nil => rw [hl] at hp; rw [hp.symm.eq_nil]
  | cons x xs =>
    cases hl' : l' with
    | nil => rw [hl, hl'] at hp; exact absurd hp.length_eq (by simp)
    | cons x' xs' =>
      subst hl; subst hl'
      obtain ⟨hr, hmin⟩ := foldl_min lt (x :: xs) htr htot xs x List.mem_cons_self (fun a ha => List.mem_cons_of_mem _ ha)
      obtain ⟨hr', hmin'⟩ := foldl_min lt (x' :: xs') htr' htot' xs' x' List.mem_cons_self (fun a ha => List.mem_cons_of_mem _ ha)
      simp only [best?, Option.some.injEq]
      generalize xs.foldl (fun m y => if lt y m then y else m) x = r at *
      generalize xs'.foldl (fun m y => if lt y m then y else m) x' = r' at *
      by_cases h : r = r'
      · exact h
      · exfalso
        have h1 := hmin r' (hp.mem_iff.2 hr')
        have h2 := hmin' r (hp.mem_iff.1 hr)
        rcases h1 with h1 | h1
        · exact h h1.symm
        · rcases h2 with h2 | h2
          · exact h h2
          · exact hasym r hr r' (hp.mem_iff.2 hr') h1 h2

theorem canClaim_perm (q r : Queue) (he : q.entries.Perm r.entries) (e : Entry) (h : Quals) : q.canClaim e h = r.canClaim e h := by
  have hl : ∀ x, x ∈ q.landedIds ↔ x ∈ r.landedIds := fun x => (List.Perm.filterMap _ he).mem_iff
  have hk : ∀ k, k ∈ q.heldKeys ↔ k ∈ r.heldKeys := fun k => by simp [Queue.heldKeys, List.mem_flatMap, List.mem_filter, he.mem_iff]
  simp only [Queue.canClaim, Queue.depsMet, Queue.keysFree]
  have h1 : (e.item.deps.all (· ∈ q.landedIds)) = (e.item.deps.all (· ∈ r.landedIds)) := by simp [hl]
  have h2 : (e.item.keys.all (· ∉ q.heldKeys)) = (e.item.keys.all (· ∉ r.heldKeys)) := by simp [hk]
  rw [h1, h2]

/-- DETERMINISM: the choice depends on what is in the queue, never on the order the entries are listed in. -/
theorem choose_deterministic (pr : Params) (q r : Queue) (me : Quals) (lc : Local) (he : q.entries.Perm r.entries)
    (hq : (q.entries.map (·.item.id)).Nodup) : choose pr q me lc = choose pr r me lc := by
  unfold choose
  by_cases hr : (!ready pr me lc) = true
  · simp [hr]
  · simp only [hr, Bool.false_eq_true, ite_false]
    have hP : (fun e : Entry => q.canClaim e me && !deferred pr lc.now me e) = (fun e : Entry => r.canClaim e me && !deferred pr lc.now me e) := by
      funext e; rw [canClaim_perm q r he]
    have hperm : ((q.entries.filter fun e => q.canClaim e me && !deferred pr lc.now me e).map (·.item)).Perm
        ((r.entries.filter fun e => r.canClaim e me && !deferred pr lc.now me e).map (·.item)) := by
      rw [← hP]; exact (he.filter _).map _
    have hd : ∀ a ∈ ((q.entries.filter fun e => q.canClaim e me && !deferred pr lc.now me e).map (·.item)),
        ∀ b ∈ ((q.entries.filter fun e => q.canClaim e me && !deferred pr lc.now me e).map (·.item)), a ≠ b → a.id ≠ b.id := by
      intro a ha b hb hne hid
      obtain ⟨e₁, h₁, rfl⟩ := List.mem_map.1 ha
      obtain ⟨e₂, h₂, rfl⟩ := List.mem_map.1 hb
      exact hne (by rw [inj_of_nodup_map (·.item.id) hq (List.mem_filter.1 h₁).1 (List.mem_filter.1 h₂).1 hid])
    rw [best?_perm (prec pr lc.now) hperm (fun a _ b _ c _ => prec_trans pr lc.now a b c) (fun a _ b _ => prec_asym pr lc.now a b)
      (fun a ha b hb hne => prec_total pr lc.now a b (hd a ha b hb hne))]



/-! ## The store: rows, five operations, and their laws (the port's conformance suite: pool/conformance.sh)
A message is a ROW: its delivery number `gen` (the queue's read count: the FENCING TOKEN), the time it is visible from (`vt`: the end of the lease, on the DATABASE's clock, which every operation takes as `now`),
who took that delivery, and the item's retries. A lease is the comparison `vt ≤ now` made by the next reader: nothing runs when it ends, nothing is deleted. `Store.sent` is the key table (an id outlives
its message); `Store.done` is how a finished message ended. The operations are total; a refusal is `none`. The laws mirror `Lease.lean` (one owner at a time, a takeover raises the generation,
a stale owner is refused) and add what a queue needs (idempotent send, finish once). -/

structure Row where
  gen     : Nat               -- delivery number; 0 = never delivered
  vt      : Nat               -- visible from this time (end of the lease; for a delayed send, the due time)
  holder  : Option HostId     -- who took delivery `gen`
  retries : Option Nat        -- the item's declared retries; an inbox message has none
  deriving DecidableEq, Repr

/-- How a finished message ended (the first outcome of that delivery stands). -/
structure Done where
  gen  : Nat
  host : HostId
  out  : Outcome
  deriving DecidableEq, Repr

structure Store where
  sent : ItemId → Bool
  live : ItemId → Option Row
  done : ItemId → Option Done

def Store.empty : Store := ⟨fun _ => false, fun _ => none, fun _ => none⟩

def upd {β : Type} (f : ItemId → β) (id : ItemId) (v : β) : ItemId → β := fun i => if i = id then v else f i

theorem upd_same {β : Type} (f : ItemId → β) (id : ItemId) (v : β) : upd f id v id = v := by simp [upd]
theorem upd_other {β : Type} (f : ItemId → β) (id : ItemId) (v : β) (j : ItemId) (h : j ≠ id) : upd f id v j = f j := by simp [upd, h]

def Row.visible (r : Row) (now : Nat) : Bool := decide (r.vt ≤ now)
/-- Delivered more than its retries allow: nobody claims it, a steward decides. Derived from the row; nothing is written. -/
def Row.spent (r : Row) : Bool := match r.retries with | some k => decide (k < r.gen) | none => false
def Row.claimable (r : Row) (now : Nat) : Bool := r.visible now && !r.spent
/-- The snapshot's `exhausted` column: claimable by the clock, but spent. -/
def Row.exhausted (r : Row) (now : Nat) : Bool := r.visible now && r.spent

/-- 1. send: once per id, ever (pending, leased or finished); `delay` is the not-before. -/
def Store.send (s : Store) (now : Nat) (id : ItemId) (delay : Nat) (retries : Option Nat) : Option Store :=
  if s.sent id = true then none
  else some { s with sent := upd s.sent id true, live := upd s.live id (some ⟨0, now + delay, none, retries⟩) }

/-- 2. claim by id: lease it for `lease ≥ 1` ticks. Only a visible row that is not spent; the delivery number rises by one and is returned. -/
def Store.claim (s : Store) (now : Nat) (id : ItemId) (h : HostId) (lease : Nat) : Option (Store × Nat) :=
  match s.live id with
  | none => none
  | some r =>
    if r.claimable now = true ∧ 1 ≤ lease then
      some ({ s with live := upd s.live id (some { r with gen := r.gen + 1, vt := now + lease, holder := some h }) }, r.gen + 1)
    else none

/-- 3. renew: only the holder of THIS delivery; allowed after expiry while nobody has taken the row (the number is unchanged). -/
def Store.renew (s : Store) (now : Nat) (id : ItemId) (h : HostId) (gen lease : Nat) : Option Store :=
  match s.live id with
  | none => none
  | some r =>
    if r.holder = some h ∧ r.gen = gen ∧ 1 ≤ lease then some { s with live := upd s.live id (some { r with vt := now + lease }) }
    else none

/-- 4. finish: only the holder of this delivery; the row leaves the queue and the outcome is recorded. A retry of the same finish is accepted again. -/
def Store.finish (s : Store) (id : ItemId) (h : HostId) (gen : Nat) (o : Outcome) : Option Store :=
  match s.done id with
  | some d => if d.host = h ∧ d.gen = gen then some s else none
  | none =>
    match s.live id with
    | none => none
    | some r =>
      if r.holder = some h ∧ r.gen = gen then some { s with live := upd s.live id none, done := upd s.done id (some ⟨gen, h, o⟩) }
      else none

/-- Well-formed: a live or finished id was sent, and nothing is both live and finished. -/
def Store.Wf (s : Store) : Prop :=
  ∀ id, ((s.live id).isSome → s.sent id = true) ∧ ((s.done id).isSome → s.sent id = true) ∧ ¬((s.live id).isSome ∧ (s.done id).isSome)

theorem wf_empty : Store.empty.Wf := by intro id; simp [Store.empty]

theorem wf_send (s s' : Store) (now id d r) (hw : s.Wf) (h : s.send now id d r = some s') : s'.Wf := by
  unfold Store.send at h
  split at h
  · cases h
  · rename_i hs
    cases h
    intro j
    by_cases hj : j = id
    · subst hj
      have h1 := hw j
      have hd : s.done j = none := by cases hh : s.done j <;> simp_all
      simp [upd_same, hd]
    · have := hw j
      simp only [upd_other _ _ _ _ hj]
      exact this

theorem wf_claim (s s' : Store) (now id h lease g) (hw : s.Wf) (hc : s.claim now id h lease = some (s', g)) : s'.Wf := by
  unfold Store.claim at hc
  split at hc
  · cases hc
  · rename_i r hr
    split at hc
    · cases hc
      intro j
      have := hw j
      by_cases hj : j = id
      · subst hj; simp [upd_same, hr] at *; exact this
      · simp only [upd_other _ _ _ _ hj]; exact this
    · cases hc

theorem wf_renew (s s' : Store) (now id h gen lease) (hw : s.Wf) (hc : s.renew now id h gen lease = some s') : s'.Wf := by
  unfold Store.renew at hc
  split at hc
  · cases hc
  · rename_i r hr
    split at hc
    · cases hc
      intro j
      have := hw j
      by_cases hj : j = id
      · subst hj; simp [upd_same, hr] at *; exact this
      · simp only [upd_other _ _ _ _ hj]; exact this
    · cases hc

theorem wf_finish (s s' : Store) (id h gen o) (hw : s.Wf) (hc : s.finish id h gen o = some s') : s'.Wf := by
  unfold Store.finish at hc
  split at hc
  · split at hc
    · cases hc; exact hw
    · cases hc
  · rename_i hd
    split at hc
    · cases hc
    · rename_i r hr
      split at hc
      · cases hc
        intro j
        have := hw j
        by_cases hj : j = id
        · subst hj
          have hs : s.sent j = true := (this.1) (by simp [hr])
          simp [upd_same, hs]
        · simp only [upd_other _ _ _ _ hj]; exact this
      · cases hc


/-! ### The laws -/

/-- (L1) Sent once: an id that was ever sent is never sent again. -/
theorem send_once (s : Store) (now id d r) (h : s.sent id = true) : s.send now id d r = none := by simp [Store.send, h]

/-- A send makes the id sent, puts one undelivered row in the queue due at `now + delay`, and touches no other id. -/
theorem send_effect (s s' : Store) (now id d r) (h : s.send now id d r = some s') :
    s'.sent id = true ∧ s'.live id = some ⟨0, now + d, none, r⟩ ∧ (∀ j, j ≠ id → s'.live j = s.live j ∧ s'.done j = s.done j) := by
  unfold Store.send at h
  split at h
  · cases h
  · cases h
    refine ⟨by simp [upd_same], by simp [upd_same], fun j hj => ⟨by simp [upd_other _ _ _ _ hj], rfl⟩⟩

/-- (L1) The key outlives the message: sent only ever grows. -/
theorem sent_monotone_send (s s' : Store) (now id d r) (h : s.send now id d r = some s') (j : ItemId) (hj : s.sent j = true) : s'.sent j = true := by
  unfold Store.send at h
  split at h
  · cases h
  · cases h; by_cases e : j = id <;> simp [upd, e, hj]

/-- Claim, renew and finish never change the set of sent ids. -/
theorem sent_claim (s s' : Store) (now id h lease g) (hc : s.claim now id h lease = some (s', g)) : s'.sent = s.sent := by
  unfold Store.claim at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc; rfl
    · cases hc
theorem sent_renew (s s' : Store) (now id h gen lease) (hc : s.renew now id h gen lease = some s') : s'.sent = s.sent := by
  unfold Store.renew at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc; rfl
    · cases hc
theorem sent_finish (s s' : Store) (id h gen o) (hc : s.finish id h gen o = some s') : s'.sent = s.sent := by
  unfold Store.finish at hc
  split at hc
  · split at hc
    · cases hc; rfl
    · cases hc
  · split at hc
    · cases hc
    · split at hc
      · cases hc; rfl
      · cases hc

/-- (L8) A finished id can never be sent again, and nothing finished is claimable: its row is gone. -/
theorem finished_never_resent (s : Store) (hw : s.Wf) (id : ItemId) (hd : (s.done id).isSome = true) (now d r) : s.send now id d r = none :=
  send_once s now id d r ((hw id).2.1 hd)
theorem finished_not_claimable (s : Store) (hw : s.Wf) (id : ItemId) (hd : (s.done id).isSome = true) (now h lease) : s.claim now id h lease = none := by
  have : s.live id = none := by
    cases hl : s.live id with
    | none => rfl
    | some _ => exact absurd ⟨by simp [hl], hd⟩ (hw id).2.2
  simp [Store.claim, this]

/-- (L3) ONE OWNER AT A TIME: a row whose lease has not ended cannot be claimed by anyone. -/
theorem claim_exclusive (s : Store) (now id h lease) (r : Row) (hl : s.live id = some r) (hlive : now < r.vt) : s.claim now id h lease = none := by
  have : r.claimable now = false := by simp [Row.claimable, Row.visible, Nat.not_le.mpr hlive]
  simp [Store.claim, hl, this]

/-- (L3) Two hosts claiming one item at one instant: whoever the store serves second gets nothing (the lease is at least one tick, so the row is not visible at `now`). -/
theorem one_winner (s s₁ : Store) (now id h₁ h₂ lease₁ lease₂ g) (h : s.claim now id h₁ lease₁ = some (s₁, g)) : s₁.claim now id h₂ lease₂ = none := by
  unfold Store.claim at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · rename_i hc
      obtain ⟨_, hl1⟩ := hc
      cases h
      exact claim_exclusive _ now id h₂ lease₂ { r with gen := r.gen + 1, vt := now + lease₁, holder := some h₁ } (by simp [upd_same]) (by simp; omega)
    · cases h

/-- (L5) A TAKEOVER RAISES THE DELIVERY NUMBER (the fencing law (`takeover_raises_gen`)): the fencing token. -/
theorem claim_raises_gen (s s' : Store) (now id h lease g) (hc : s.claim now id h lease = some (s', g)) :
    ∃ r, s.live id = some r ∧ g = r.gen + 1 ∧ s'.live id = some { r with gen := g, vt := now + lease, holder := some h } := by
  unfold Store.claim at hc
  split at hc
  · cases hc
  · rename_i r hr
    split at hc
    · cases hc; exact ⟨r, hr, rfl, by simp [upd_same]⟩
    · cases hc

/-- (L5) After the lease ends, anyone may take a row that is not spent: no administrator, no reaper. -/
theorem takeover_after_expiry (s : Store) (now id h lease) (r : Row) (hl : s.live id = some r) (hv : r.vt ≤ now) (hs : r.spent = false) (hle : 1 ≤ lease) :
    (s.claim now id h lease).isSome = true := by
  have : r.claimable now = true := by simp [Row.claimable, Row.visible, hv, hs]
  simp [Store.claim, hl, this, hle]

/-- (L10) A spent (exhausted) row is claimable by nobody; it shows as `exhausted`, and a steward decides. -/
theorem claim_spent (s : Store) (now id h lease) (r : Row) (hl : s.live id = some r) (hs : r.spent = true) : s.claim now id h lease = none := by
  have : r.claimable now = false := by simp [Row.claimable, hs]
  simp [Store.claim, hl, this]

/-- (L9) DELAY: a row sent with a delay is not claimable before it is due. -/
theorem delay_hides (s s' : Store) (now id d r) (h : s.send now id d r = some s') (t : Nat) (ht : t < now + d) (host lease) : s'.claim t id host lease = none := by
  obtain ⟨-, hl, -⟩ := send_effect s s' now id d r h
  exact claim_exclusive s' t id host lease _ hl ht

/-- A claim changes no other id. -/
theorem claim_other (s s' : Store) (now id h lease g) (hc : s.claim now id h lease = some (s', g)) (j : ItemId) (hj : j ≠ id) :
    s'.live j = s.live j ∧ s'.done j = s.done j := by
  unfold Store.claim at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc; exact ⟨by simp [upd_other _ _ _ _ hj], rfl⟩
    · cases hc

/-- (L6) RENEW IS FENCED: a stale delivery number, or a host that does not hold this delivery, is refused. -/
theorem renew_fenced (s : Store) (now id h gen lease) (r : Row) (hl : s.live id = some r) (hbad : r.gen ≠ gen ∨ r.holder ≠ some h) : s.renew now id h gen lease = none := by
  have hn : ¬ (r.holder = some h ∧ r.gen = gen ∧ 1 ≤ lease) := by
    rintro ⟨h1, h2, -⟩; rcases hbad with hb | hb
    · exact hb h2
    · exact hb h1
  simp [Store.renew, hl, hn]
/-- (L6) the holder of the current delivery renews, also after expiry while nobody has taken the row; the delivery number does not change. -/
theorem renew_holder (s : Store) (now id h lease) (r : Row) (hl : s.live id = some r) (hh : r.holder = some h) (hle : 1 ≤ lease) :
    ∃ s', s.renew now id h r.gen lease = some s' ∧ s'.live id = some { r with vt := now + lease } := by
  exact ⟨{ s with live := upd s.live id (some { r with vt := now + lease }) }, by simp [Store.renew, hl, hh, hle], by simp [upd_same]⟩

/-- (L6, L7) FINISH IS FENCED: with no finished record, a stale number or a host that does not hold the delivery is refused. -/
theorem finish_fenced (s : Store) (id h gen o) (hd : s.done id = none) (r : Row) (hl : s.live id = some r) (hbad : r.gen ≠ gen ∨ r.holder ≠ some h) :
    s.finish id h gen o = none := by
  have hn : ¬ (r.holder = some h ∧ r.gen = gen) := by
    rintro ⟨h1, h2⟩; rcases hbad with hb | hb
    · exact hb h2
    · exact hb h1
  simp [Store.finish, hd, hl, hn]

/-- (L7) The holder finishes: the row leaves the queue and the outcome is recorded against the delivery. -/
theorem finish_records (s : Store) (id h o) (r : Row) (hd : s.done id = none) (hl : s.live id = some r) (hh : r.holder = some h) :
    ∃ s', s.finish id h r.gen o = some s' ∧ s'.live id = none ∧ s'.done id = some ⟨r.gen, h, o⟩ := by
  exact ⟨{ s with live := upd s.live id none, done := upd s.done id (some ⟨r.gen, h, o⟩) }, by simp [Store.finish, hd, hl, hh], by simp [upd_same], by simp [upd_same]⟩

/-- (L7) FINISH IS IDEMPOTENT: after it succeeds, the same finish (a retry after a lost reply) succeeds again and changes nothing. -/
theorem finish_idempotent (s s' : Store) (id h gen o o') (hf : s.finish id h gen o = some s') : s'.finish id h gen o' = some s' := by
  unfold Store.finish at hf
  split at hf
  · rename_i d hd
    split at hf
    · rename_i hdh
      cases hf
      simp [Store.finish, hd, hdh]
    · cases hf
  · split at hf
    · cases hf
    · rename_i r hr
      split at hf
      · cases hf
        simp [Store.finish, upd_same]
      · cases hf

/-- (L6) THE ZOMBIE CANNOT FINISH: once another claim has taken a later delivery, the old holder, whatever its number was, is refused. -/
theorem zombie_cannot_finish (s s' : Store) (hw : s.Wf) (now id h lease g) (hc : s.claim now id h lease = some (s', g)) (zh : HostId) (zg : Nat) (hzg : zg ≤ g - 1) (o) :
    s'.finish id zh zg o = none := by
  have hw' := wf_claim s s' now id h lease g hw hc
  obtain ⟨r, hr, hg, hl⟩ := claim_raises_gen s s' now id h lease g hc
  have hd : s'.done id = none := by
    cases hdd : s'.done id with
    | none => rfl
    | some _ => exact absurd ⟨by simp [hl], by simp [hdd]⟩ (hw' id).2.2
  exact finish_fenced s' id zh zg o hd _ hl (Or.inl (by simp; omega))

/-- A finish leaves every other id alone. -/
theorem finish_other (s s' : Store) (id h gen o) (hc : s.finish id h gen o = some s') (j : ItemId) (hj : j ≠ id) :
    s'.live j = s.live j ∧ s'.done j = s.done j := by
  unfold Store.finish at hc
  split at hc
  · split at hc
    · cases hc; exact ⟨rfl, rfl⟩
    · cases hc
  · split at hc
    · cases hc
    · split at hc
      · cases hc; exact ⟨by simp [upd_other _ _ _ _ hj], by simp [upd_other _ _ _ _ hj]⟩
      · cases hc

/-! ### From the snapshot to `choose` and back to the claim
`Row.entry?` is how a row looks in the snapshot `choose` reads: visible and not spent = pending (claimable); visible and spent = blocked (lost): derived, never written; a row whose lease is live = held by its
holder; a delayed row with no holder is not offered at all. A host that last held a visible row lost it: it defers the row to the others for a while (`lostOn`). -/
def Row.entry? (it : Item) (r : Row) (now : Nat) : Option Entry :=
  if r.visible now then
    some { item := it, state := if r.spent then .blocked .lost else .pending, left := it.retries - r.gen, lostOn := if r.gen > 0 then r.holder.toList else [], lostAt := if r.gen > 0 then r.vt else 0 }
  else match r.holder with
    | some h => some ⟨it, .claimed ⟨h⟩, it.retries - r.gen, [], 0⟩
    | none => none

/-- The queue a host reads: the items it knows (the backlog) that have a live row, as the snapshot shows them. -/
def Store.view (s : Store) (now : Nat) (items : List Item) : Queue :=
  ⟨items.filterMap fun it => (s.live it.id).bind fun r => r.entry? it now⟩

theorem entry_pending (it : Item) (r : Row) (now : Nat) (e : Entry) (he : r.entry? it now = some e) (hp : e.state = .pending) :
    r.claimable now = true ∧ e.item = it := by
  unfold Row.entry? at he
  split at he
  · rename_i hv
    cases he
    simp only [Row.claimable, hv, Bool.true_and]
    cases hs : r.spent <;> simp_all
  · split at he
    · cases he; simp at hp
    · cases he

/-- (f) WHAT `choose` RETURNS IS CLAIMABLE: the row of the chosen item is visible and not spent, so the store's claim of it succeeds unless another host (or the lease clock) changed the row since the snapshot:
there is one winner, and the loser simply chooses again. -/
theorem choose_then_claim (pr : Params) (s : Store) (now : Nat) (items : List Item) (me : Quals) (lc : Local) (id : ItemId) (lease : Nat)
    (hw : WellFormed (s.view now items)) (hle : 1 ≤ lease) (h : choose pr (s.view now items) me lc = some id) :
    ∃ r, s.live id = some r ∧ r.claimable now = true ∧ (s.claim now id me.id lease).isSome = true := by
  obtain ⟨-, e, hf, hc, -⟩ := choose_entry pr _ me lc id hw h
  have hmem := (Queue.find?_some hf)
  simp only [Store.view, List.mem_filterMap] at hmem
  obtain ⟨⟨it, hit, hent⟩, hid⟩ := hmem
  cases hl : s.live it.id with
  | none => simp [hl] at hent
  | some r =>
    simp only [hl, Option.bind_some] at hent
    have hpend : e.state = .pending := by simp only [Queue.canClaim, Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1.1.1
    obtain ⟨hcl, hei⟩ := entry_pending it r now e hent hpend
    have hidd : it.id = id := by rw [← hid, ← hei]
    subst hidd
    exact ⟨r, hl, hcl, by simp [Store.claim, hl, hcl, hle]⟩


/-! ### Scenarios (the acceptance scenarios of the design, closed by evaluation)
Host 10 claims item 1 at t = 0 with a 120-tick lease and dies. Host 20 is refused at t = 60 and takes it at t = 120 with delivery number 2; the dead host's finish is refused; host 20 finishes,
retries the finish, and the id can never be sent again. -/
example :
    ((Store.empty.send 0 1 0 (some 1)).bind fun s =>
     (s.claim 0 1 10 120).bind fun (s, g1) =>
     (match s.claim 60 1 20 120 with | none => some s | some _ => none).bind fun s =>
     (s.claim 120 1 20 120).bind fun (s, g2) =>
     (match s.finish 1 10 g1 .needsClarification with | none => some s | some _ => none).bind fun s =>
     (s.finish 1 20 g2 .needsClarification).bind fun s =>
     (s.finish 1 20 g2 .needsClarification).bind fun s =>
     (match s.send 200 1 0 none with | none => some (g1, g2, (s.done 1).map (fun (d : Done) => d.gen)) | some _ => none))
    = some (1, 2, some 2) := by decide
/-- Delivered `retries + 1` times with the last lease over: spent, claimable by nobody, and the snapshot calls it exhausted. -/
example :
    ((Store.empty.send 0 1 0 (some 1)).bind fun s =>
     (s.claim 0 1 10 5).bind fun (s, _) =>
     (s.claim 5 1 20 5).bind fun (s, _) =>
     (match s.claim 10 1 30 5 with | none => some ((s.live 1).map (fun (r : Row) => r.exhausted 10)) | some _ => none))
    = some (some true) := by decide

end VbmDispatcher.Pool
