import Lean.Data.Json
import VbmScoreboard.Core
/-! # The wire formats of the scoreboard

Three text formats, each one JSON object per line, each carrying `"v": 1` (the protocol version: a decoder refuses a version it does not know, typed, `Why.unknownVersion`). The types are the core's (`VbmScoreboard.Reading`, `Floor`, `Entry`, `Baseline`, `Direction`, `Event`); this module only reads and writes them. No project, language or metric is named here: the formats are generic.

* the PROVIDER PROTOCOL `{"v":1,"metric":M,"value":N,"unit":U}` (`value` a natural number; `unit` optional text for people, read and checked but not kept, because the unit of a number is said in the metric's name): `decodeReadings`, `encodeReading`, `encodeReadings`;
* the BASELINE FILE `{"v":1,"metric":M,"direction":"higher"|"lower","floor":N}` (a floor's `value` is written under the key `floor`): `decodeBaseline`, `encodeBaseline` (in the order of the metric's name, `sortFloors`);
* the HISTORY FILE `{"v":1,"at":N,"metric":M,"event":"banked"|"added"|"reset","before":N|null,"after":N|null,"reason":S|null,"author":S|null}` (an entry's `time` is written under the key `at`; `reason` and `author` are the strings of a `reset` and `null` for the other events, and a `reset` without them is refused): `decodeHistory`, `encodeHistory`, in the order given (a series).

A blank line is skipped. A line that does not decode is a typed `Refusal`: the 1-based line number and WHAT is wrong (`Why`: not JSON, not an object, a missing key, a wrong type, an unknown version, an unknown word, a duplicate metric). The text is cut into lines by a structural function (`splitLines`), and a line is read by `Lean.Json.parse`, reached through the decoders' parameter `p` (the `...With` functions) so that the theorems of `VbmScoreboardProofs.Wire` are over any parser and renderer.

This `Refusal` is the wire's own (`VbmScoreboardWire.Refusal`), not the core's `VbmScoreboard.Refusal` of a refused reset.

The theorems and their non-vacuity witnesses are in `VbmScoreboardProofs.Wire`. -/
namespace VbmScoreboardWire

open Lean
open VbmScoreboard (Reading Floor Entry Baseline Direction Event)

/-! ## Types -/

/-- WHAT is wrong with a line. -/
inductive Why where
  | notJson (message : String)
  | notObject
  | missingKey (key : String)
  | wrongType (key : String)
  | unknownVersion (v : Nat)
  | unknownWord (key : String) (word : String)
  | duplicate (metric : String)
  deriving DecidableEq, Repr

/-- A refusal: the 1-based number of the line and what is wrong with it. -/
structure Refusal where
  line : Nat
  why : Why
  deriving DecidableEq, Repr

/-- The protocol version this module reads and writes. -/
def version : Nat := 1

/-! ## Lines -/

def splitAux : List Char → List Char → List String
  | [], cur => [String.ofList cur.reverse]
  | c :: cs, cur =>
    if c = '\n' then String.ofList cur.reverse :: splitAux cs [] else splitAux cs (c :: cur)

/-- The lines of a text, cut at each newline; a text ending in a newline ends in an empty line. -/
def splitLines (s : String) : List String := splitAux s.toList []

/-- Each line followed by a newline. -/
def joinLines : List String → String
  | [] => ""
  | l :: ls => l ++ "\n" ++ joinLines ls

/-- A line of nothing but whitespace is blank. -/
def isBlank (l : String) : Bool := l.toList.all Char.isWhitespace

/-! ## Decoding lines -/

/-- Read one line: blank is `none`; not JSON, or JSON that `f` refuses, is a refusal at line `n`. -/
def decodeLine {α : Type} (p : String → Except String Json) (f : Json → Except Why α)
    (n : Nat) (l : String) : Except Refusal (Option α) :=
  if isBlank l then .ok none
  else
    match p l with
    | .error m => .error ⟨n, .notJson m⟩
    | .ok j =>
      match f j with
      | .error w => .error ⟨n, w⟩
      | .ok a => .ok (some a)

/-- Read lines numbered from `n`; the first bad line is the refusal; each item keeps its line number. -/
def decodeLines {α : Type} (p : String → Except String Json) (f : Json → Except Why α) :
    Nat → List String → Except Refusal (List (Nat × α))
  | _, [] => .ok []
  | n, l :: ls =>
    match decodeLine p f n l with
    | .error e => .error e
    | .ok none => decodeLines p f (n + 1) ls
    | .ok (some a) =>
      match decodeLines p f (n + 1) ls with
      | .error e => .error e
      | .ok r => .ok ((n, a) :: r)

/-- Refuse a repeated key (the second occurrence, at its own line). -/
def dupCheck {α : Type} (key : α → String) :
    List String → List (Nat × α) → Except Refusal (List α)
  | _, [] => .ok []
  | seen, (n, a) :: rest =>
    if key a ∈ seen then .error ⟨n, .duplicate (key a)⟩
    else
      match dupCheck key (key a :: seen) rest with
      | .error e => .error e
      | .ok r => .ok (a :: r)

/-- The items with the line numbers `n`, `n+1`, ... . -/
def indexed {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | n, a :: as => (n, a) :: indexed (n + 1) as

/-- Read a text whose lines are objects: every item, no key check. -/
def decodeText {α : Type} (p : String → Except String Json) (f : Json → Except Why α)
    (text : String) : Except Refusal (List (Nat × α)) :=
  decodeLines p f 1 (splitLines text)

/-! ## Fields of an object -/

def natJ (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

def optNatJ : Option Nat → Json
  | none => Json.null
  | some n => natJ n

def optStrJ : Option String → Json
  | none => Json.null
  | some s => Json.str s

/-- A required key of an object. -/
def field (j : Json) (k : String) : Except Why Json :=
  match j with
  | .obj _ => match j.getObjVal? k with
    | .ok v => .ok v
    | .error _ => .error (.missingKey k)
  | _ => .error .notObject

/-- An optional key: absent or null is `none`. -/
def optField (j : Json) (k : String) : Except Why (Option Json) :=
  match j with
  | .obj _ => match j.getObjVal? k with
    | .error _ => .ok none
    | .ok Json.null => .ok none
    | .ok v => .ok (some v)
  | _ => .error .notObject

def natField (j : Json) (k : String) : Except Why Nat :=
  match field j k with
  | .error e => .error e
  | .ok v => match v.getNat? with
    | .ok n => .ok n
    | .error _ => .error (.wrongType k)

def strField (j : Json) (k : String) : Except Why String :=
  match field j k with
  | .error e => .error e
  | .ok v => match v.getStr? with
    | .ok s => .ok s
    | .error _ => .error (.wrongType k)

def optNatField (j : Json) (k : String) : Except Why (Option Nat) :=
  match optField j k with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some v) => match v.getNat? with
    | .ok n => .ok (some n)
    | .error _ => .error (.wrongType k)

def optStrField (j : Json) (k : String) : Except Why (Option String) :=
  match optField j k with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some v) => match v.getStr? with
    | .ok s => .ok (some s)
    | .error _ => .error (.wrongType k)

/-- The protocol version of an object: absent, mistyped or not 1 is a typed refusal. -/
def checkVersion (j : Json) : Except Why Unit :=
  match natField j "v" with
  | .error e => .error e
  | .ok n => if n = version then .ok () else .error (.unknownVersion n)

def directionWord : Direction → String
  | .higher => "higher"
  | .lower => "lower"

def eventWord : Event → String
  | .banked => "banked"
  | .added => "added"
  | .reset _ _ => "reset"

/-- The reason an event carries (only a reset has one). -/
def reasonOf : Event → Option String
  | .reset r _ => some r
  | _ => none

/-- The author an event carries (only a reset has one). -/
def authorOf : Event → Option String
  | .reset _ a => some a
  | _ => none

def directionOf (w : String) : Option Direction :=
  if w = "higher" then some .higher
  else if w = "lower" then some .lower
  else none

/-- The event of a word and the reason and author read beside it: a reset needs both. -/
def eventOf (w : String) (reason author : Option String) : Except Why Event :=
  if w = "banked" then .ok .banked
  else if w = "added" then .ok .added
  else if w = "reset" then
    match reason, author with
    | some r, some a => .ok (.reset r a)
    | none, _ => .error (.missingKey "reason")
    | some _, none => .error (.missingKey "author")
  else .error (.unknownWord "event" w)

/-! ## Objects of the three formats -/

/-- A reading as an object (the `unit` is not written). -/
def readingJson (r : Reading) : Json :=
  Json.mkObj [("v", natJ version), ("metric", Json.str r.metric), ("value", natJ r.value)]

/-- A reading from an object; an optional `unit` must be text and is not kept. -/
def readingOfJson (j : Json) : Except Why Reading :=
  match checkVersion j with
  | .error e => .error e
  | .ok _ =>
    match strField j "metric" with
    | .error e => .error e
    | .ok m =>
      match natField j "value" with
      | .error e => .error e
      | .ok v =>
        match optStrField j "unit" with
        | .error e => .error e
        | .ok _ => .ok { metric := m, value := v }

def floorJson (f : Floor) : Json :=
  Json.mkObj [("v", natJ version), ("metric", Json.str f.metric),
    ("direction", Json.str (directionWord f.direction)), ("floor", natJ f.value)]

def floorOfJson (j : Json) : Except Why Floor :=
  match checkVersion j with
  | .error e => .error e
  | .ok _ =>
    match strField j "metric" with
    | .error e => .error e
    | .ok m =>
      match strField j "direction" with
      | .error e => .error e
      | .ok w =>
        match directionOf w with
        | none => .error (.unknownWord "direction" w)
        | some d =>
          match natField j "floor" with
          | .error e => .error e
          | .ok n => .ok { metric := m, direction := d, value := n }

def entryJson (e : Entry) : Json :=
  Json.mkObj [("v", natJ version), ("at", natJ e.time), ("metric", Json.str e.metric),
    ("event", Json.str (eventWord e.event)), ("before", optNatJ e.before),
    ("after", optNatJ e.after), ("reason", optStrJ (reasonOf e.event)),
    ("author", optStrJ (authorOf e.event))]

def entryOfJson (j : Json) : Except Why Entry :=
  match checkVersion j with
  | .error e => .error e
  | .ok _ =>
    match natField j "at" with
    | .error e => .error e
    | .ok t =>
      match strField j "metric" with
      | .error e => .error e
      | .ok m =>
        match strField j "event" with
        | .error e => .error e
        | .ok w =>
          match optNatField j "before" with
          | .error e => .error e
          | .ok b =>
            match optNatField j "after" with
            | .error e => .error e
            | .ok a =>
              match optStrField j "reason" with
              | .error e => .error e
              | .ok rs =>
                match optStrField j "author" with
                | .error e => .error e
                | .ok au =>
                  match eventOf w rs au with
                  | .error e => .error e
                  | .ok ev => .ok { time := t, metric := m, before := b, after := a, event := ev }

/-! ## The order of a baseline -/

def insertFloor (f : Floor) : List Floor → List Floor
  | [] => [f]
  | g :: gs => if f.metric ≤ g.metric then f :: g :: gs else g :: insertFloor f gs

/-- A baseline in the order of its metrics' names (insertion sort, structural). -/
def sortFloors : List Floor → List Floor
  | [] => []
  | f :: fs => insertFloor f (sortFloors fs)

/-! ## The three formats, over any parser and renderer -/

/-- The written line reads back to its object, holds no newline and is not blank. -/
def LineOK (p : String → Except String Json) (render : Json → String) (j : Json) : Prop :=
  p (render j) = .ok j ∧ '\n' ∉ (render j).toList ∧ isBlank (render j) = false

def encodeWith {α : Type} (render : Json → String) (toJ : α → Json) (as : List α) : String :=
  joinLines (as.map (fun a => render (toJ a)))

/-! ### The provider protocol -/

def decodeReadingsWith (p : String → Except String Json) (text : String) :
    Except Refusal (List Reading) :=
  match decodeText p readingOfJson text with
  | .error e => .error e
  | .ok xs => dupCheck Reading.metric [] xs

def encodeReadingsWith (render : Json → String) (rs : List Reading) : String :=
  encodeWith render readingJson rs

/-- The provider protocol: a text of readings, one object per line. -/
def decodeReadings (text : String) : Except Refusal (List Reading) :=
  decodeReadingsWith Json.parse text

/-- One reading as its line (no newline). -/
def encodeReading (r : Reading) : String := (readingJson r).compress

/-- Readings as a text, each line ended by a newline. -/
def encodeReadings (rs : List Reading) : String := encodeReadingsWith Json.compress rs

/-! ### The baseline file -/

def decodeBaselineWith (p : String → Except String Json) (text : String) :
    Except Refusal Baseline :=
  match decodeText p floorOfJson text with
  | .error e => .error e
  | .ok xs => dupCheck Floor.metric [] xs

def encodeBaselineWith (render : Json → String) (b : Baseline) : String :=
  encodeWith render floorJson (sortFloors b)

/-- The baseline file: a text of floors, one object per line; a repeated metric is refused. -/
def decodeBaseline (text : String) : Except Refusal Baseline :=
  decodeBaselineWith Json.parse text

/-- A baseline as a text, in the order of the metrics' names. -/
def encodeBaseline (b : Baseline) : String := encodeBaselineWith Json.compress b

/-! ### The history file -/

def decodeHistoryWith (p : String → Except String Json) (text : String) :
    Except Refusal (List Entry) :=
  match decodeText p entryOfJson text with
  | .error e => .error e
  | .ok xs => .ok (xs.map (·.2))

def encodeHistoryWith (render : Json → String) (h : List Entry) : String :=
  encodeWith render entryJson h

/-- The history file: a text of entries, one object per line, in order. -/
def decodeHistory (text : String) : Except Refusal (List Entry) :=
  decodeHistoryWith Json.parse text

/-- A history as a text, in the order given (a series: append-only). -/
def encodeHistory (h : List Entry) : String := encodeHistoryWith Json.compress h

end VbmScoreboardWire
