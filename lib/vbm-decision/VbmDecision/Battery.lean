import VbmDecision.Truth
/-! # The battery (S10)

A decision that no single question settles is made from a battery of items: each item is read as a probability (from code or from a typed `noul` answer), the score is the exact weighted mean (`Rat`), a veto may decide before the score, and a band table turns the score into one of the user's outcomes. A missing, refused or mistyped answer is a fault that abstains, never a guess; a bad battery or table is a typed `BatteryRefusal` of the author. Spec section 14. -/
namespace VbmDecision

/-- An item's weight: exact and non-negative. -/
abbrev Weight := Nat

/-- Items in a battery: unbounded work. -/
def maxItems : Nat := 64

/-- A weight: a hostile numeral in a weight (time and memory). -/
def maxWeight : Nat := 1000000

/-- Bands in a table: unbounded work. -/
def maxBands : Nat := 16

/-- A decidable item is answered by code (0 or 1); a judgmental item by a typed probability. -/
inductive ItemKind where
  | decidable | judgmental
  deriving DecidableEq, Repr

/-- A veto: it fires when the item's probability is at least the threshold (never 0). -/
structure Veto (α : Type) where
  threshold : Prob
  outcome : α
  deriving DecidableEq, Repr

/-- One item of a battery. -/
structure Item (α : Type) where
  id : String
  weight : Weight
  kind : ItemKind
  veto : Option (Veto α)
  deriving DecidableEq, Repr

/-- A battery: its items in order. -/
structure Battery (α : Type) where
  items : List (Item α)
  deriving DecidableEq, Repr

/-- The reply to one item. -/
inductive Reply where
  | code (b : Bool)
  | answer (a : Answer)
  | refused (r : Refusal)
  deriving DecidableEq, Repr

/-- The replies, keyed by item id; the order is not meaningful. -/
abbrev Answers := List (String × Reply)

/-- A verdict is one of the user's outcomes or an abstention. -/
inductive Verdict (α : Type) where
  | decided (o : α)
  | abstain
  deriving DecidableEq, Repr

/-- What is wrong with one item's reply, or with the answer set. -/
inductive Fault where
  | missing | refused (r : Refusal) | wrongKind | duplicateAnswer | unexpectedAnswer
  deriving DecidableEq, Repr

/-- What the verdict rests on. -/
inductive Basis where
  | veto | vetoConflict | score | gap | fault
  deriving DecidableEq, Repr

/-- The refusals of an author's battery or table. -/
inductive BatteryCode where
  | noItems | tooManyItems | badItemId | duplicateId | weightTooLarge | allWeightsZero | badVetoThreshold | vetoOutcomeUnknown
  | noBands | tooManyBands | bandRange | bandOrder
  deriving DecidableEq, Repr

/-- A code and the field path it concerns. -/
structure BatteryRefusal where
  code : BatteryCode
  field : String
  deriving DecidableEq, Repr

/-- A band: the interval `[lo, hi)`, closed at 1 when `hi = 1`. -/
structure Band (α : Type) where
  outcome : α
  lo : Rat
  hi : Rat
  deriving DecidableEq, Repr

/-- The table over the score, bands in ascending order. -/
structure Table (α : Type) where
  bands : List (Band α)
  deriving DecidableEq, Repr

/-- One guard of a battery check: the continuation if it holds, else the typed refusal. -/
def bguard (c : Prop) [Decidable c] (code : BatteryCode) (field : String) (k : Except BatteryRefusal Unit) : Except BatteryRefusal Unit :=
  if c then k else .error ⟨code, field⟩

/-! ## Validity -/

/-- A veto threshold is never 0. -/
def Item.VetoOk {α : Type} (it : Item α) : Prop := ∀ v ∈ it.veto, v.threshold.val ≠ 0

instance Item.decVetoOk {α : Type} (it : Item α) : Decidable it.VetoOk := by unfold Item.VetoOk; infer_instance

/-- The item rules in order, with the index for the path and the ids seen so far. -/
def checkItems {α : Type} : Nat → List String → List (Item α) → Except BatteryRefusal Unit
  | _, _, [] => .ok ()
  | i, seen, it :: rest =>
    bguard (it.id ≠ "") .badItemId s!"items[{i}].id" <|
    bguard (it.id ∉ seen) .duplicateId s!"items[{i}].id" <|
    bguard (it.weight ≤ maxWeight) .weightTooLarge s!"items[{i}].weight" <|
    bguard it.VetoOk .badVetoThreshold s!"items[{i}].veto.threshold" <|
    checkItems (i + 1) (it.id :: seen) rest

/-- A valid battery: 1 to `maxItems` items, ids non-empty and distinct, weights within `maxWeight`, veto thresholds nonzero, some weight positive. -/
def Battery.Valid {α : Type} (b : Battery α) : Prop :=
  0 < b.items.length ∧ b.items.length ≤ maxItems ∧ (∀ it ∈ b.items, it.id ≠ "") ∧ (b.items.map (·.id)).Nodup ∧
  (∀ it ∈ b.items, it.weight ≤ maxWeight) ∧ (∀ it ∈ b.items, it.VetoOk) ∧ ∃ it ∈ b.items, 0 < it.weight

instance Battery.decValid {α : Type} (b : Battery α) : Decidable b.Valid := by unfold Battery.Valid; infer_instance

/-- Decide `Battery.Valid`, or refuse with the first rule that fails. -/
def Battery.check {α : Type} (b : Battery α) : Except BatteryRefusal Unit :=
  bguard (0 < b.items.length) .noItems "items" <|
  bguard (b.items.length ≤ maxItems) .tooManyItems "items" <|
  match checkItems 0 [] b.items with
  | .error e => .error e
  | .ok () => bguard (∃ it ∈ b.items, 0 < it.weight) .allWeightsZero "items" (.ok ())

/-- Every veto outcome is an outcome of some band. -/
def Battery.OutcomesKnown {α : Type} (b : Battery α) (t : Table α) : Prop :=
  ∀ it ∈ b.items, ∀ v ∈ it.veto, v.outcome ∈ t.bands.map (·.outcome)

instance Battery.decOutcomesKnown {α : Type} [DecidableEq α] (b : Battery α) (t : Table α) : Decidable (b.OutcomesKnown t) := by
  unfold Battery.OutcomesKnown; infer_instance

/-- The veto outcomes against the table, with the index for the path. -/
def checkOutcomes {α : Type} [DecidableEq α] (t : Table α) : Nat → List (Item α) → Except BatteryRefusal Unit
  | _, [] => .ok ()
  | i, it :: rest =>
    bguard (∀ v ∈ it.veto, v.outcome ∈ t.bands.map (·.outcome)) .vetoOutcomeUnknown s!"items[{i}].veto.outcome" <|
    checkOutcomes t (i + 1) rest

/-- One band: `0 ≤ lo < hi ≤ 1`. -/
def Band.Ok {α : Type} (b : Band α) : Prop := 0 ≤ b.lo ∧ b.lo < b.hi ∧ b.hi ≤ 1

instance Band.decOk {α : Type} (b : Band α) : Decidable b.Ok := by unfold Band.Ok; infer_instance

/-- Every band is in range and the `hi` of a band is at most the `lo` of the next. -/
def BandsOk {α : Type} : List (Band α) → Prop
  | [] => True
  | b :: rest => b.Ok ∧ (match rest with | [] => True | n :: _ => b.hi ≤ n.lo) ∧ BandsOk rest

instance bandsOkDec {α : Type} : (l : List (Band α)) → Decidable (BandsOk l)
  | [] => isTrue trivial
  | b :: rest =>
    have := bandsOkDec rest
    match rest with
    | [] => inferInstanceAs (Decidable (b.Ok ∧ True ∧ BandsOk []))
    | n :: r => inferInstanceAs (Decidable (b.Ok ∧ b.hi ≤ n.lo ∧ BandsOk (n :: r)))

/-- The band rules in order, with the index for the path. -/
def checkBands {α : Type} : Nat → List (Band α) → Except BatteryRefusal Unit
  | _, [] => .ok ()
  | i, b :: rest =>
    bguard b.Ok .bandRange s!"bands[{i}]" <|
    (match rest with
      | [] => checkBands (i + 1) rest
      | n :: _ => bguard (b.hi ≤ n.lo) .bandOrder s!"bands[{i + 1}]" (checkBands (i + 1) rest))

/-- A valid table: 1 to `maxBands` bands in range and in order. -/
def Table.Valid {α : Type} (t : Table α) : Prop := 0 < t.bands.length ∧ t.bands.length ≤ maxBands ∧ BandsOk t.bands

instance Table.decValid {α : Type} (t : Table α) : Decidable t.Valid := by unfold Table.Valid; infer_instance

/-- Decide `Table.Valid`, or refuse with the first rule that fails. -/
def Table.check {α : Type} (t : Table α) : Except BatteryRefusal Unit :=
  bguard (0 < t.bands.length) .noBands "bands" <|
  bguard (t.bands.length ≤ maxBands) .tooManyBands "bands" <|
  checkBands 0 t.bands

/-! ## The score -/

/-- The numerator of the mean: the sum of weight times millionths. -/
def scoreN (ps : List (Weight × Prob)) : Nat := (ps.map fun e => e.1 * e.2.val).sum

/-- The denominator: `scale` times the sum of the weights. -/
def scoreD (ps : List (Weight × Prob)) : Nat := scale * (ps.map (·.1)).sum

/-- The weighted mean of the probabilities, exact; `allWeightsZero` before any division when every weight is 0. -/
def Battery.score (ps : List (Weight × Prob)) : Except BatteryRefusal Rat :=
  if scoreD ps = 0 then .error ⟨.allWeightsZero, "items"⟩ else .ok ((scoreN ps : Nat) / (scoreD ps : Nat))

/-! ## Reading the items -/

/-- An item is read when its weight is positive or it has a veto. -/
def Item.required {α : Type} (i : Item α) : Bool := Decidable.decide (0 < i.weight) || i.veto.isSome

/-- Read one reply as a probability; `none` is missing. -/
def Item.read {α : Type} (i : Item α) : Option Reply → Except Fault Prob
  | none => .error .missing
  | some (.refused r) => .error (.refused r)
  | some (.code b) =>
    match i.kind with
    | .decidable => .ok (if b then ⟨scale, Nat.le_refl _⟩ else ⟨0, Nat.zero_le _⟩)
    | .judgmental => .error .wrongKind
  | some (.answer a) =>
    match i.kind, a with
    | .judgmental, .noul p => .ok p
    | _, _ => .error .wrongKind

/-- Read the item from the answer set: no entry is missing, two entries are `duplicateAnswer`. -/
def Item.readIn {α : Type} (as : Answers) (i : Item α) : Except Fault Prob :=
  match as.filter (fun e => Decidable.decide (e.1 = i.id)) with
  | [] => i.read none
  | [e] => i.read (some e.2)
  | _ => .error .duplicateAnswer

/-- The outcome of the veto if it fired: its item read `ok p` with `p ≥ threshold`. -/
def Item.fired {α : Type} (as : Answers) (i : Item α) : Option α :=
  match i.veto, i.readIn as with
  | some v, .ok p => if v.threshold.val ≤ p.val then some v.outcome else none
  | _, _ => none

/-- The required item with its probability, when it reads `ok`. -/
def Item.readOpt {α : Type} (as : Answers) (i : Item α) : Option (Item α × Prob) :=
  if i.required then (match i.readIn as with | .ok p => some (i, p) | .error _ => none) else none

/-- The required item's id with its fault, when it does not read `ok`. -/
def Item.faultOpt {α : Type} (as : Answers) (i : Item α) : Option (String × Fault) :=
  if i.required then (match i.readIn as with | .error f => some (i.id, f) | .ok _ => none) else none

/-- The required items that read `ok`, with their probabilities, in battery order. -/
def Battery.reads {α : Type} (b : Battery α) (as : Answers) : List (Item α × Prob) := b.items.filterMap (Item.readOpt as)

/-- Keep each element once (its last occurrence). -/
def dedup : List String → List String
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

/-- Each answer id that is no item of the battery, once, as an `unexpectedAnswer` fault. -/
def Battery.unexpected {α : Type} (b : Battery α) (as : Answers) : List (String × Fault) :=
  ((dedup (as.map (·.1))).filter fun k => Decidable.decide (k ∉ b.items.map (·.id))).map fun k => (k, Fault.unexpectedAnswer)

/-- The faults: each required item that does not read `ok`, in battery order, then the unexpected ids. -/
def Battery.faults {α : Type} (b : Battery α) (as : Answers) : List (String × Fault) :=
  b.items.filterMap (Item.faultOpt as) ++ b.unexpected as

/-! ## The table over the score -/

/-- The score is in the band: `lo ≤ s < hi`, or `s = hi = 1`. -/
def Band.has {α : Type} (b : Band α) (s : Rat) : Bool := Decidable.decide (b.lo ≤ s ∧ (s < b.hi ∨ (s = b.hi ∧ b.hi = 1)))

/-- The first band that contains the score, with its index (counted from `k`). -/
def bandAt {α : Type} (s : Rat) : Nat → List (Band α) → Option (Nat × Band α)
  | _, [] => none
  | k, b :: rest => if b.has s then some (k, b) else bandAt s (k + 1) rest

/-- The index of the band that contains the score. -/
def Table.index {α : Type} (t : Table α) (s : Rat) : Option Nat := (bandAt s 0 t.bands).map (·.1)

/-- The outcome of the band that contains the score, else an abstention. -/
def Table.lookup {α : Type} (t : Table α) (s : Rat) : Verdict α :=
  match bandAt s 0 t.bands with
  | some (_, b) => .decided b.outcome
  | none => .abstain

/-- A table without a gap: it starts at `lo`, each band starts where the last ended, the last ends at 1. -/
def GaplessFrom {α : Type} : Rat → List (Band α) → Prop
  | lo, [] => lo = 1
  | lo, b :: rest => b.lo = lo ∧ GaplessFrom b.hi rest

instance gaplessDec {α : Type} : (lo : Rat) → (l : List (Band α)) → Decidable (GaplessFrom lo l)
  | lo, [] => inferInstanceAs (Decidable (lo = 1))
  | lo, b :: rest =>
    have := gaplessDec b.hi rest
    inferInstanceAs (Decidable (b.lo = lo ∧ GaplessFrom b.hi rest))

/-! ## The record and `evaluate` -/

/-- The audit record: the inputs, the verdict, what it rests on and every probability used. -/
structure Record (α : Type) where
  specVersion : Nat
  battery : Battery α
  table : Table α
  replies : Answers
  verdict : Verdict α
  basis : Basis
  score : Option Rat
  used : List (String × Prob)
  vetoed : List String
  faults : List (String × Fault)
  deriving DecidableEq, Repr

/-- The verdict and its basis, from the fired veto outcomes, else the score. -/
def verdictOf {α : Type} [DecidableEq α] (t : Table α) (os : List α) (sc : Option Rat) : Verdict α × Basis :=
  match os with
  | o :: rest => if rest.all (fun x => Decidable.decide (x = o)) then (.decided o, .veto) else (.abstain, .vetoConflict)
  | [] =>
    match sc with
    | none => (.abstain, .fault)
    | some s => match bandAt s 0 t.bands with
      | some (_, b) => (.decided b.outcome, .score)
      | none => (.abstain, .gap)

/-- The weight and probability of every required item that read `ok`, in battery order. -/
def Battery.pairs {α : Type} (b : Battery α) (as : Answers) : List (Weight × Prob) := (b.reads as).map fun e => (e.1.weight, e.2)

/-- The outcomes of the vetoes that fired, in battery order. -/
def Battery.fires {α : Type} (b : Battery α) (as : Answers) : List α := b.items.filterMap (Item.fired as)

/-- The score, when every required item read `ok` and there is no set-level fault. -/
def Battery.scoreOf {α : Type} (b : Battery α) (as : Answers) : Option Rat :=
  if (b.faults as).isEmpty then (Battery.score (b.pairs as)).toOption else none

/-- The record of a valid battery and table: veto, then fault, then the score and the table. -/
def Battery.run {α : Type} [DecidableEq α] (b : Battery α) (t : Table α) (as : Answers) : Record α :=
  let vb := verdictOf t (b.fires as) (b.scoreOf as)
  { specVersion := 1, battery := b, table := t, replies := as, verdict := vb.1, basis := vb.2, score := b.scoreOf as,
    used := (b.reads as).map fun e => (e.1.id, e.2),
    vetoed := (b.items.filter fun i => (i.fired as).isSome).map (·.id),
    faults := b.faults as }

/-- The verdict of a battery over a table: the author's errors first, then veto, fault, score, table. Total. -/
def evaluate {α : Type} [DecidableEq α] (b : Battery α) (t : Table α) (as : Answers) : Except BatteryRefusal (Record α) :=
  match b.check with
  | .error e => .error e
  | .ok () =>
    match t.check with
    | .error e => .error e
    | .ok () =>
      match checkOutcomes t 0 b.items with
      | .error e => .error e
      | .ok () => .ok (b.run t as)

end VbmDecision
