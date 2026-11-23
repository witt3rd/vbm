import VbmDecision.Decode
/-! # Decoding and encoding the request and the response (S7b)

`Request.encode` validates a request and writes its wire object (fields `model`, `state`, `questions`); `Request.decode` reads one back, fields in any order, exactly those three. `Response.encode` writes a response; `Response.decode` takes the question set of the request and reads it back, refusing an answer that is no question's (`unexpectedAnswer`) and a question without an answer (`missingAnswer`). The questions and answers go through the S7a readers, so every decoded question is valid and every decoded answer well formed; a decoded request passes `Request.check`. A `state` is opaque: only its outer shape is read, never a media part. The cost is an exact decimal, never converted. The root decoders refuse a value nested deeper than `maxNestingDepth`. -/
namespace VbmDecision

/-- Run a check on every element, stopping at the first refusal. -/
def allOk {α : Type} (f : α → Except Refusal Unit) : List α → Except Refusal Unit
  | [] => .ok ()
  | x :: xs => match f x with
    | .ok () => allOk f xs
    | .error e => .error e

/-- A model string: a non-empty maker without `/`, then `/`, then a non-empty remainder. -/
def modelOk (s : String) : Bool :=
  match s.toList.span (· != '/') with
  | (mk, '/' :: rest) => !mk.isEmpty && !rest.isEmpty
  | _ => false

/-- A state part is a string or an object; the part itself is never read. -/
def partOk : J → Bool
  | .str _ => true
  | .obj _ => true
  | _ => false

/-- The outer shape of a state: a non-empty array of parts, or an object. -/
def stateShape : J → Bool
  | .arr xs => !xs.isEmpty && xs.all partOk
  | .obj _ => true
  | _ => false

/-- The number of parts of a state. -/
def stateLen : J → Nat
  | .arr xs => xs.length
  | _ => 0

/-- A valid request: a model string, a state of the right shape and size, 1 to `maxQuestions` named questions (non-empty distinct names), each valid. -/
def Request.Valid (r : Request) : Prop :=
  modelOk r.model = true ∧ stateShape r.state = true ∧ stateLen r.state ≤ maxStateParts ∧
  J.depth r.state < maxNestingDepth ∧ r.questions ≠ [] ∧ r.questions.length ≤ maxQuestions ∧
  (∀ nq ∈ r.questions, nq.1 ≠ "") ∧ (r.questions.map (·.1)).Nodup ∧ (∀ nq ∈ r.questions, nq.2.Valid)

instance (r : Request) : Decidable r.Valid := by unfold Request.Valid; infer_instance

/-- Decide `Request.Valid`, or refuse with the first rule that fails. -/
def Request.check (r : Request) : Except Refusal Unit :=
  guardWith (modelOk r.model = true) .badModelName "model" <|
  guardWith (stateShape r.state = true) .badState "state" <|
  guardWith (stateLen r.state ≤ maxStateParts) .tooManyStateParts "state" <|
  guardWith (J.depth r.state < maxNestingDepth) .nestingTooDeep "state" <|
  guardWith (r.questions ≠ []) .noQuestions "questions" <|
  guardWith (r.questions.length ≤ maxQuestions) .tooManyQuestions "questions" <|
  guardWith (∀ nq ∈ r.questions, nq.1 ≠ "") .badQuestionName "questions" <|
  guardWith (r.questions.map (·.1)).Nodup .duplicateKey "questions" <|
  allOk (fun nq => (nq.2.check).mapError (·.at (pathKey "questions" nq.1))) r.questions

/-- The wire form of a request, if it is valid. -/
def Request.encode (r : Request) : Except Refusal J :=
  match r.check with
  | .ok () => .ok (.obj [("model", .str r.model), ("state", r.state),
      ("questions", .obj (r.questions.map fun nq => (nq.1, nq.2.encode)))])
  | .error e => .error e

/-- One question of a request, read at its path. -/
def readQuestion (nq : String × J) : Except Refusal (String × Question) := do
  pure (nq.1, ← Question.decodeAt (pathKey "questions" nq.1) nq.2)

/-- Read a request at the root, without the nesting guard; the result passes `Request.check`. -/
def Request.decodeAt (j : J) : Except Refusal Request := do
  let kvs ← objOf "" (some ["model", "state", "questions"]) j
  let m ← strField "" kvs "model"
  let s ← field "" kvs "state"
  let qs ← objOf "questions" none (← field "" kvs "questions")
  let r : Request := ⟨m, s, ← qs.mapM readQuestion⟩
  match r.check with
  | .ok () => pure r
  | .error e => .error e

/-- Read a request: a value nested deeper than `maxNestingDepth` is `nestingTooDeep`. -/
def Request.decode (j : J) : Except Refusal Request :=
  if J.depth j ≤ maxNestingDepth then Request.decodeAt j else refuse .nestingTooDeep ""

/-! ## The response -/

/-- A token count as a wire number. -/
def natJ (n : Nat) : J := .num ⟨false, n, 0⟩

/-- A non-negative integer: a whole number of units, exactly (`3`, `3.0` and `0.3e1` are all 3; `0.5` is `notNatural`). -/
def natOf (path : String) : J → Except Refusal Nat
  | .num d => match d.toScaled with
    | .ok v => if v % scale = 0 then .ok (v / scale) else refuse .notNatural path
    | .error .exponentTooLarge => refuse .exponentTooLarge path
    | .error _ => refuse .notNatural path
  | _ => refuse .wrongKind path

/-- The cost: an exact decimal, kept as read; negative and hostile exponents are refused. -/
def costOf (path : String) : J → Except Refusal Decimal
  | .num d => if d.neg = true ∧ d.mantissa ≠ 0 then refuse .negative path
    else if Decimal.maxExponent < d.exp.natAbs then refuse .exponentTooLarge path else .ok d
  | _ => refuse .wrongKind path

/-- The wire form of a response. -/
def Response.encode (r : Response) : J :=
  .obj [("id", .str r.id), ("model", .str r.model), ("provider", .str r.provider),
    ("answers", .obj (r.answers.map fun na => (na.1, na.2.encode))),
    ("usage", .obj [("input_tokens", natJ r.usage.inputTokens), ("output_tokens", natJ r.usage.outputTokens),
      ("cost", .num r.usage.cost)])]

/-- One answer of a response: it must be the answer to a question of the request. -/
def readAnswer (qs : List (String × Question)) (nv : String × J) : Except Refusal (String × Answer) :=
  match qs.lookup nv.1 with
  | some q => do pure (nv.1, ← Answer.decodeAt (pathKey "answers" nv.1) q nv.2)
  | none => refuse .unexpectedAnswer (pathKey "answers" nv.1)

/-- Read a response against the questions of its request, without the nesting guard. -/
def Response.decodeAt (qs : List (String × Question)) (j : J) : Except Refusal Response := do
  let kvs ← objOf "" (some ["id", "model", "provider", "answers", "usage"]) j
  let i ← strField "" kvs "id"
  let m ← strField "" kvs "model"
  let pv ← strField "" kvs "provider"
  let ans ← objOf "answers" none (← field "" kvs "answers")
  let as ← ans.mapM (readAnswer qs)
  match qs.find? (fun nq => !(as.map (·.1)).contains nq.1) with
  | some nq => refuse .missingAnswer (pathKey "answers" nq.1)
  | none => pure ()
  let us ← objOf "usage" (some ["input_tokens", "output_tokens", "cost"]) (← field "" kvs "usage")
  let ti ← natOf "usage.input_tokens" (← field "usage" us "input_tokens")
  let to ← natOf "usage.output_tokens" (← field "usage" us "output_tokens")
  pure ⟨i, m, pv, as, ⟨ti, to, ← costOf "usage.cost" (← field "usage" us "cost")⟩⟩

/-- Read a response: a value nested deeper than `maxNestingDepth` is `nestingTooDeep`. -/
def Response.decode (qs : List (String × Question)) (j : J) : Except Refusal Response :=
  if J.depth j ≤ maxNestingDepth then Response.decodeAt qs j else refuse .nestingTooDeep ""

/-- The answer under a name is well formed for the question of that name, and there is one. -/
def AnswerFits (qs : List (String × Question)) (n : String) (a : Answer) : Prop :=
  match qs.lookup n with
  | some q => WellFormed q a
  | none => False

instance (qs : List (String × Question)) (n : String) (a : Answer) : Decidable (AnswerFits qs n a) := by
  unfold AnswerFits; split <;> infer_instance

/-- A response is valid for a question set: one answer per question and no other, each well formed, a cost that reads back. -/
def Response.Valid (qs : List (String × Question)) (r : Response) : Prop :=
  (r.answers.map (·.1)).Nodup ∧ (∀ na ∈ r.answers, AnswerFits qs na.1 na.2) ∧
  (∀ nq ∈ qs, nq.1 ∈ r.answers.map (·.1)) ∧
  ¬ (r.usage.cost.neg = true ∧ r.usage.cost.mantissa ≠ 0) ∧ r.usage.cost.exp.natAbs ≤ Decimal.maxExponent

instance (qs : List (String × Question)) (r : Response) : Decidable (Response.Valid qs r) := by
  unfold Response.Valid; infer_instance

end VbmDecision
