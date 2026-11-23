import VbmDecision.Check
/-! # Decoding and encoding questions and answers over `J` (S7a)

A decoded wire value `J` is read into a typed `Question` or `Answer`, refusing with the field path. Every object goes through `objOf`: a duplicate key is refused, then (when the object has a closed field list) a key outside it. The structure and the numbers are read first; then `Question.check` or `checkAnswer` decides, so a decoded value is always valid or well formed. Nothing is guessed: no field is defaulted, no number clamped, no key case-folded. `encode` writes the wire form of a valid value. The decoders recurse on no `J`: only `J.depth`, the nesting guard of the root decoders, does. -/
namespace VbmDecision

mutual
/-- Nesting depth: a scalar is 0, an array or object is one more than its deepest member. -/
def J.depth : J → Nat
  | .arr xs => J.depthList xs + 1
  | .obj kvs => J.depthKvs kvs + 1
  | _ => 0
/-- Deepest member of a list of values. -/
def J.depthList : List J → Nat
  | [] => 0
  | x :: xs => max (J.depth x) (J.depthList xs)
/-- Deepest value of a list of members. -/
def J.depthKvs : List (String × J) → Nat
  | [] => 0
  | kv :: kvs => max (J.depthPair kv) (J.depthKvs kvs)
/-- The depth of a member's value. -/
def J.depthPair : String × J → Nat
  | (_, j) => J.depth j
end

/-- The field path of member `k` under `p` (`""` is the root). -/
def pathKey (p k : String) : String := if p = "" then k else p ++ "." ++ k

/-- The refusal of a check, moved under the path `p` (a check's own field `""` is `p` itself). -/
def Refusal.at (p : String) (r : Refusal) : Refusal := ⟨r.code, if r.field = "" then p else pathKey p r.field⟩

/-- A refusal at a path. -/
def refuse {α : Type} (c : RefusalCode) (path : String) : Except Refusal α := .error ⟨c, path⟩

/-! ## Objects, fields and values -/

/-- The first key that occurs again later in the list. -/
def firstDup : List String → Option String
  | [] => none
  | k :: ks => if k ∈ ks then some k else firstDup ks

/-- Refuse a repeated key (`duplicateKey`, naming it). -/
def dupCheck (path : String) (kvs : List (String × J)) : Except Refusal Unit :=
  match firstDup (kvs.map (·.1)) with
  | some k => refuse .duplicateKey (pathKey path k)
  | none => .ok ()

/-- Refuse the first key outside the allowed list (`unknownField`, naming it). -/
def unknownCheck (path : String) (allowed : List String) (kvs : List (String × J)) : Except Refusal Unit :=
  match (kvs.map (·.1)).find? (fun k => !allowed.contains k) with
  | some k => refuse .unknownField (pathKey path k)
  | none => .ok ()

/-- An object: of another kind `wrongKind`, then a repeated key, then (with a closed list) a key outside it. -/
def objOf (path : String) (allowed : Option (List String)) : J → Except Refusal (List (String × J))
  | .obj kvs => do
    dupCheck path kvs
    match allowed with
    | some al => unknownCheck path al kvs
    | none => pure ()
    pure kvs
  | _ => refuse .wrongKind path

/-- A required field: absent is `missingField`. -/
def field (path : String) (kvs : List (String × J)) (k : String) : Except Refusal J :=
  match kvs.lookup k with
  | some v => .ok v
  | none => refuse .missingField (pathKey path k)

/-- A string: a value of another kind is `wrongKind`. -/
def strOf (path : String) : J → Except Refusal String
  | .str s => .ok s
  | _ => refuse .wrongKind path

/-- A probability: through `Prob.ofDecimal`; a string is never read as a number. -/
def probOf (path : String) : J → Except Refusal Prob
  | .num d => match Prob.ofDecimal d with
    | .ok p => .ok p
    | .error e => refuse e.toCode path
  | _ => refuse .wrongKind path

/-- A position in millionths of an index: exact, not bounded here (the answer check bounds it). -/
def posOf (path : String) : J → Except Refusal Pos
  | .num d => match d.toScaled with
    | .ok v => .ok v
    | .error e => refuse e.toCode path
  | _ => refuse .wrongKind path

/-- A required string field. -/
def strField (path : String) (kvs : List (String × J)) (k : String) : Except Refusal String := do
  strOf (pathKey path k) (← field path kvs k)

/-- A required probability field. -/
def probField (path : String) (kvs : List (String × J)) (k : String) : Except Refusal Prob := do
  probOf (pathKey path k) (← field path kvs k)

/-- A key in canonical decimal form: digits only, no leading zero. -/
def canonIdx (k : String) : Bool := !k.isEmpty && k.toList.all Char.isDigit && (k = "0" || k.toList.head? != some '0')

/-- An object keyed `"0"`, `"1"`, … covering exactly `0..n-1`: a key not canonical is `badIndexKey`, a canonical one out of range `unknownOption`, an absent index `missingOption`. -/
def indexed {α : Type} (path : String) (n : Nat) (f : String → J → Except Refusal α) (j : J) : Except Refusal (List α) := do
  let kvs ← objOf path none j
  let _ ← kvs.mapM fun (k, _) =>
    if k ∈ (List.range n).map Nat.repr then pure ()
    else refuse (if canonIdx k then .unknownOption else .badIndexKey) (pathKey path k)
  (List.range n).mapM fun i => match kvs.lookup (Nat.repr i) with
    | some v => f (pathKey path (Nat.repr i)) v
    | none => refuse .missingOption (pathKey path (Nat.repr i))

/-! ## The type tag -/

/-- The wire tag of a kind. -/
def Kind.tag : Kind → String
  | .noul => "noul" | .choice => "choice" | .score => "score" | .box => "box"

/-- The `type` field: absent `missingField`, not a string `wrongKind`, a string outside the four `unknownType`. -/
def tagOf (path : String) (kvs : List (String × J)) : Except Refusal Kind :=
  match kvs.lookup "type" with
  | some (.str "noul") => .ok .noul
  | some (.str "choice") => .ok .choice
  | some (.str "score") => .ok .score
  | some (.str "box") => .ok .box
  | some (.str _) => refuse .unknownType (pathKey path "type")
  | some _ => refuse .wrongKind (pathKey path "type")
  | none => refuse .missingField (pathKey path "type")

/-- The fields of a question object of a kind, and no others. -/
def qKeys : Kind → List String
  | .box => ["type", "instructions"]
  | _ => ["type", "instructions", "criteria"]

/-- The fields of an answer object of a kind, and no others. -/
def aKeys : Kind → List String
  | .noul => ["type", "noul"]
  | .choice => ["type", "choice", "probabilities", "confidence"]
  | .score => ["type", "score", "confidence", "probabilities", "legend"]
  | .box => ["type", "box", "confidence"]

/-! ## Questions -/

/-- The criteria of a `choice` option: a string or `null`. -/
def optStr (path : String) : J → Except Refusal (Option String)
  | .null => .ok none
  | .str s => .ok (some s)
  | _ => refuse .wrongKind path

/-- A question's fields past the tag, by kind (not yet checked). -/
def rawQuestion (path : String) (kd : Kind) (kvs : List (String × J)) : Except Refusal Question := do
  let i ← strField path kvs "instructions"
  let cp := pathKey path "criteria"
  match kd with
  | .noul => match kvs.lookup "criteria" with
    | none => pure (.noul i none)
    | some c => do
      let cs ← objOf cp (some ["true", "false"]) c
      pure (.noul i (some (← strField cp cs "true", ← strField cp cs "false")))
  | .choice => do
    let cs ← objOf cp none (← field path kvs "criteria")
    pure (.choice i (← cs.mapM fun (k, v) => do pure (k, ← optStr (pathKey cp k) v)))
  | .score => match ← field path kvs "criteria" with
    | .arr xs => pure (.score i (← (List.range xs.length).zip xs |>.mapM fun (n, x) => strOf (pathKey cp (Nat.repr n)) x))
    | _ => refuse .wrongKind cp
  | .box => pure (.box i)

/-- Read a question at a path: object, tag, field list, fields, then `Question.check`. -/
def Question.decodeAt (path : String) (j : J) : Except Refusal Question := do
  let kvs ← objOf path none j
  let kd ← tagOf path kvs
  unknownCheck path (qKeys kd) kvs
  let q ← rawQuestion path kd kvs
  match q.check with
  | .ok () => pure q
  | .error r => .error (r.at path)

/-- Read a question at the root: a value nested deeper than `maxNestingDepth` is `nestingTooDeep`. -/
def Question.decode (j : J) : Except Refusal Question :=
  if J.depth j ≤ maxNestingDepth then Question.decodeAt "" j else refuse .nestingTooDeep ""

/-! ## Answers -/

/-- An answer's fields past the tag, by kind, for the question `q` (not yet checked). -/
def rawAnswer (path : String) (q : Question) (kd : Kind) (kvs : List (String × J)) : Except Refusal Answer := do
  let pp := pathKey path "probabilities"
  match kd with
  | .noul => pure (.noul (← probField path kvs "noul"))
  | .choice => do
    let s ← strField path kvs "choice"
    let ps ← objOf pp none (← field path kvs "probabilities")
    pure (.choice s (← ps.mapM fun (k, v) => do pure (k, ← probOf (pathKey pp k) v)) (← probField path kvs "confidence"))
  | .score => do
    let n := match q with | .score _ ls => ls.length | _ => 0
    let x ← posOf (pathKey path "score") (← field path kvs "score")
    let c ← probField path kvs "confidence"
    let ps ← indexed pp n probOf (← field path kvs "probabilities")
    pure (.score x c ps (← indexed (pathKey path "legend") n strOf (← field path kvs "legend")))
  | .box => do
    let bp := pathKey path "box"
    let bs ← objOf bp (some ["top", "bottom", "left", "right"]) (← field path kvs "box")
    let b : Box := ⟨← probField bp bs "top", ← probField bp bs "bottom", ← probField bp bs "left", ← probField bp bs "right"⟩
    pure (.box b (← probField path kvs "confidence"))

/-- The answer if `checkAnswer` accepts it, else its refusal under the path. -/
def checkedAt (path : String) (q : Question) (a : Answer) : Except Refusal Answer :=
  match checkAnswer q a with
  | .ok () => .ok a
  | .error r => .error (r.at path)

/-- Read an answer to `q` at a path: object, tag (another kind than `q`'s is `typeMismatch`), field list, fields, then `checkAnswer`. -/
def Answer.decodeAt (path : String) (q : Question) (j : J) : Except Refusal Answer := do
  let kvs ← objOf path none j
  let kd ← tagOf path kvs
  if kd = q.kindOf then pure () else refuse .typeMismatch (pathKey path "type")
  unknownCheck path (aKeys kd) kvs
  checkedAt path q (← rawAnswer path q kd kvs)

/-- Read an answer at the root: a value nested deeper than `maxNestingDepth` is `nestingTooDeep`. -/
def Answer.decode (q : Question) (j : J) : Except Refusal Answer :=
  if J.depth j ≤ maxNestingDepth then Answer.decodeAt "" q j else refuse .nestingTooDeep ""

/-! ## Encoding -/

/-- A probability as its exact decimal. -/
def Prob.toJ (p : Prob) : J := .num p.toDecimal

/-- A list as an object keyed `"0"`, `"1"`, …. -/
def indexedJ (xs : List J) : J := .obj ((List.range xs.length).zip xs |>.map fun (i, x) => (Nat.repr i, x))

/-- The wire form of a question. -/
def Question.encode : Question → J
  | .noul i c => .obj ([("type", .str "noul"), ("instructions", .str i)] ++
      match c with
      | none => []
      | some (t, f) => [("criteria", .obj [("true", .str t), ("false", .str f)])])
  | .choice i os => .obj [("type", .str "choice"), ("instructions", .str i),
      ("criteria", .obj (os.map fun (k, d) => (k, match d with | none => .null | some s => .str s)))]
  | .score i ls => .obj [("type", .str "score"), ("instructions", .str i), ("criteria", .arr (ls.map .str))]
  | .box i => .obj [("type", .str "box"), ("instructions", .str i)]

/-- The wire form of an answer. -/
def Answer.encode : Answer → J
  | .noul p => .obj [("type", .str "noul"), ("noul", p.toJ)]
  | .choice s ps c => .obj [("type", .str "choice"), ("choice", .str s),
      ("probabilities", .obj (ps.map fun (k, p) => (k, p.toJ))), ("confidence", c.toJ)]
  | .score x c ps lg => .obj [("type", .str "score"), ("score", .num ⟨false, x, -6⟩), ("confidence", c.toJ),
      ("probabilities", indexedJ (ps.map Prob.toJ)), ("legend", indexedJ (lg.map .str))]
  | .box b c => .obj [("type", .str "box"), ("box", .obj [("top", b.top.toJ), ("bottom", b.bottom.toJ),
      ("left", b.left.toJ), ("right", b.right.toJ)]), ("confidence", c.toJ)]

end VbmDecision
