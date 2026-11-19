import VbmDecision.Truth
import VbmDecision.Message
/-! # The audit record (S6)

`audit` turns a request, a response, a name and a binding into the record of one use: the question and the answer under the name, the binding, and the outcome of `decide` on them. A refused decision still yields a record: the journal holds every use. `toJ` is canonical: a fixed field order, a `Prob` as the decimal of `Prob.toDecimal`, a refusal code by its name. `ofJ` reads a record back: an object with these fields and no others (`duplicateKey`, `unknownField`, `missingField` with the path), the question through `Question.decodeAt` (so it must be valid), the answer, binding and outcome in their canonical shapes (any other shape is `wrongKind`). The answer is read as written, never checked: a record of a malformed answer (its outcome refused) must read back. A record holds no secret, no request state and no cost. -/
namespace VbmDecision

/-- The record of one use of a decision model. -/
structure AuditRecord where
  specVersion : Nat
  «at» : Nat
  requested : String
  snapshot : String
  provider : String
  responseId : String
  questionName : String
  question : Question
  answer : Answer
  binding : Binding
  outcome : Outcome Refusal
  deriving DecidableEq, Repr

/-- A record that must read back: its question is valid, and its answer is well formed for it or its outcome is a refusal. -/
def AuditRecord.Valid (r : AuditRecord) : Prop :=
  r.question.Valid ∧ (WellFormed r.question r.answer ∨ ∃ x, r.outcome = .refused x)

/-- The record of the answer and the question under `name`, with `time` supplied by the caller. A name that is no question is `unexpectedAnswer`; a question without an answer is `missingAnswer`. -/
def audit (time : Nat) (req : Request) (resp : Response) (name : String) (b : Binding) : Except Refusal AuditRecord :=
  match req.questions.lookup name with
  | none => refuse .unexpectedAnswer (pathKey "questions" name)
  | some q => match resp.answers.lookup name with
    | none => refuse .missingAnswer (pathKey "answers" name)
    | some a => .ok ⟨1, time, req.model, resp.model, resp.provider, resp.id, name, q, a, b, decide b ⟨req.model, resp.model⟩ q a⟩

/-! ## Names of the codes and reasons -/

/-- The name of a refusal code, as written in a record. -/
def RefusalCode.name : RefusalCode → String
  | .wrongKind => "wrongKind" | .missingField => "missingField" | .unknownField => "unknownField"
  | .duplicateKey => "duplicateKey" | .unknownType => "unknownType" | .typeMismatch => "typeMismatch"
  | .badIndexKey => "badIndexKey" | .nestingTooDeep => "nestingTooDeep" | .negative => "negative"
  | .tooPrecise => "tooPrecise" | .outOfRange => "outOfRange" | .exponentTooLarge => "exponentTooLarge"
  | .notNatural => "notNatural" | .tooManyQuestions => "tooManyQuestions" | .noQuestions => "noQuestions"
  | .badQuestionName => "badQuestionName" | .tooFewOptions => "tooFewOptions" | .tooManyOptions => "tooManyOptions"
  | .tooFewLevels => "tooFewLevels" | .tooManyLevels => "tooManyLevels" | .badModelName => "badModelName"
  | .badState => "badState" | .tooManyStateParts => "tooManyStateParts" | .missingAnswer => "missingAnswer"
  | .unexpectedAnswer => "unexpectedAnswer" | .unknownOption => "unknownOption" | .missingOption => "missingOption"
  | .sumOffOne => "sumOffOne" | .selectedNotMaximal => "selectedNotMaximal" | .scoreOutOfScale => "scoreOutOfScale"
  | .scoreInconsistent => "scoreInconsistent" | .legendMismatch => "legendMismatch" | .boxInverted => "boxInverted"
  | .boxEmpty => "boxEmpty" | .thresholdKind => "thresholdKind" | .badThresholds => "badThresholds"
  | .modelMismatch => "modelMismatch" | .snapshotMismatch => "snapshotMismatch" | .badTarget => "badTarget"
  | .sampleTooSmall => "sampleTooSmall" | .sampleTooLarge => "sampleTooLarge" | .sampleOneSided => "sampleOneSided"
  | .noThresholdMeetsTarget => "noThresholdMeetsTarget" | .bandInverted => "bandInverted"

/-- The code of a name, if it is one. -/
def RefusalCode.ofName (s : String) : Option RefusalCode := RefusalCode.all.find? (·.name == s)

/-- The name of an abstention reason. -/
def AbstainReason.name : AbstainReason → String
  | .uncertainBand => "uncertainBand" | .lowProbability => "lowProbability" | .lowMargin => "lowMargin" | .lowConfidence => "lowConfidence"

/-- The reason of a name, if it is one. -/
def AbstainReason.ofName : String → Option AbstainReason
  | "uncertainBand" => some .uncertainBand | "lowProbability" => some .lowProbability
  | "lowMargin" => some .lowMargin | "lowConfidence" => some .lowConfidence | _ => none

/-! ## The `J` form of the parts -/

/-- A natural number (a time, a version) as a wire integer. -/
def Pos.toJ (x : Pos) : J := .num ⟨false, x, -6⟩

/-- A refusal. -/
def Refusal.toJ (r : Refusal) : J := .obj [("code", .str r.code.name), ("field", .str r.field)]

/-- Read a refusal. -/
def Refusal.ofJ (path : String) : J → Except Refusal Refusal
  | .obj [("code", .str c), ("field", .str f)] => match RefusalCode.ofName c with
    | some code => .ok ⟨code, f⟩
    | none => refuse .unknownType (pathKey path "code")
  | _ => refuse .wrongKind path

/-- A box. -/
def Box.toJ (b : Box) : J := .obj [("top", b.top.toJ), ("bottom", b.bottom.toJ), ("left", b.left.toJ), ("right", b.right.toJ)]

/-- Read a box. -/
def Box.ofJ (path : String) : J → Except Refusal Box
  | .obj [("top", t), ("bottom", b), ("left", l), ("right", r)] => do
    pure ⟨← probOf (pathKey path "top") t, ← probOf (pathKey path "bottom") b, ← probOf (pathKey path "left") l, ← probOf (pathKey path "right") r⟩
  | _ => refuse .wrongKind path

/-- An answer, as written (the lists are not keyed: a malformed answer must still be written). -/
def Answer.toAuditJ : Answer → J
  | .noul p => .obj [("type", .str "noul"), ("noul", p.toJ)]
  | .choice s ps c => .obj [("type", .str "choice"), ("choice", .str s), ("probabilities", .obj (ps.map fun (k, p) => (k, p.toJ))), ("confidence", c.toJ)]
  | .score x c ps lg => .obj [("type", .str "score"), ("score", Pos.toJ x), ("confidence", c.toJ), ("probabilities", .arr (ps.map Prob.toJ)), ("legend", .arr (lg.map .str))]
  | .box b c => .obj [("type", .str "box"), ("box", b.toJ), ("confidence", c.toJ)]

/-- Read an answer as written, without `checkAnswer`. -/
def Answer.ofAuditJ (path : String) : J → Except Refusal Answer
  | .obj [("type", .str "noul"), ("noul", p)] => do pure (.noul (← probOf (pathKey path "noul") p))
  | .obj [("type", .str "choice"), ("choice", .str s), ("probabilities", .obj kvs), ("confidence", c)] => do
    let pp := pathKey path "probabilities"
    pure (.choice s (← kvs.mapM fun (k, v) => do pure (k, ← probOf (pathKey pp k) v)) (← probOf (pathKey path "confidence") c))
  | .obj [("type", .str "score"), ("score", x), ("confidence", c), ("probabilities", .arr ps), ("legend", .arr lg)] => do
    pure (.score (← posOf (pathKey path "score") x) (← probOf (pathKey path "confidence") c)
      (← ps.mapM (probOf (pathKey path "probabilities"))) (← lg.mapM (strOf (pathKey path "legend"))))
  | .obj [("type", .str "box"), ("box", b), ("confidence", c)] => do
    pure (.box (← Box.ofJ (pathKey path "box") b) (← probOf (pathKey path "confidence") c))
  | _ => refuse .wrongKind path

/-- Thresholds. -/
def Thresholds.toJ : Thresholds → J
  | .noul no yes => .obj [("type", .str "noul"), ("no", no.toJ), ("yes", yes.toJ)]
  | .choice mp mm => .obj [("type", .str "choice"), ("min_prob", mp.toJ), ("min_margin", mm.toJ)]
  | .score lo hi mc => .obj [("type", .str "score"), ("lo", Pos.toJ lo), ("hi", Pos.toJ hi), ("min_confidence", mc.toJ)]
  | .box mc => .obj [("type", .str "box"), ("min_confidence", mc.toJ)]

/-- Read thresholds as written, without `checkThresholds`. -/
def Thresholds.ofJ (path : String) : J → Except Refusal Thresholds
  | .obj [("type", .str "noul"), ("no", n), ("yes", y)] => do
    pure (.noul (← probOf (pathKey path "no") n) (← probOf (pathKey path "yes") y))
  | .obj [("type", .str "choice"), ("min_prob", mp), ("min_margin", mm)] => do
    pure (.choice (← probOf (pathKey path "min_prob") mp) (← probOf (pathKey path "min_margin") mm))
  | .obj [("type", .str "score"), ("lo", lo), ("hi", hi), ("min_confidence", mc)] => do
    pure (.score (← posOf (pathKey path "lo") lo) (← posOf (pathKey path "hi") hi) (← probOf (pathKey path "min_confidence") mc))
  | .obj [("type", .str "box"), ("min_confidence", mc)] => do pure (.box (← probOf (pathKey path "min_confidence") mc))
  | _ => refuse .wrongKind path

/-- A binding: an absent snapshot is `null`. -/
def Binding.toJ (b : Binding) : J :=
  .obj [("model", .str b.model), ("snapshot", match b.snapshot with | none => .null | some s => .str s), ("thresholds", b.thresholds.toJ)]

/-- Read a binding. -/
def Binding.ofJ (path : String) : J → Except Refusal Binding
  | .obj [("model", .str m), ("snapshot", .null), ("thresholds", t)] => do pure ⟨m, none, ← Thresholds.ofJ (pathKey path "thresholds") t⟩
  | .obj [("model", .str m), ("snapshot", .str s), ("thresholds", t)] => do pure ⟨m, some s, ← Thresholds.ofJ (pathKey path "thresholds") t⟩
  | _ => refuse .wrongKind path

/-- A decision. -/
def Decision.toJ : Decision → J
  | .yes => .str "yes" | .no => .str "no" | .below => .str "below" | .within => .str "within" | .above => .str "above"
  | .option n => .obj [("option", .str n)]
  | .found b => .obj [("found", b.toJ)]

/-- Read a decision. -/
def Decision.ofJ (path : String) : J → Except Refusal Decision
  | .str "yes" => .ok .yes | .str "no" => .ok .no | .str "below" => .ok .below | .str "within" => .ok .within | .str "above" => .ok .above
  | .obj [("option", .str n)] => .ok (.option n)
  | .obj [("found", b)] => do pure (.found (← Box.ofJ (pathKey path "found") b))
  | _ => refuse .wrongKind path

/-- An outcome. -/
def Outcome.toJ : Outcome Refusal → J
  | .decided d => .obj [("decided", d.toJ)]
  | .abstain r => .obj [("abstain", .str r.name)]
  | .refused r => .obj [("refused", r.toJ)]

/-- Read an outcome. -/
def Outcome.ofJ (path : String) : J → Except Refusal (Outcome Refusal)
  | .obj [("decided", d)] => do pure (.decided (← Decision.ofJ (pathKey path "decided") d))
  | .obj [("abstain", .str r)] => match AbstainReason.ofName r with
    | some a => .ok (.abstain a)
    | none => refuse .unknownType (pathKey path "abstain")
  | .obj [("refused", r)] => do pure (.refused (← Refusal.ofJ (pathKey path "refused") r))
  | _ => refuse .wrongKind path

/-! ## The record -/

/-- The canonical form of a record: fixed field order. -/
def AuditRecord.toJ (r : AuditRecord) : J :=
  .obj [("spec_version", natJ r.specVersion), ("at", natJ r.«at»), ("requested", .str r.requested), ("snapshot", .str r.snapshot),
    ("provider", .str r.provider), ("response_id", .str r.responseId), ("question_name", .str r.questionName),
    ("question", r.question.encode), ("answer", r.answer.toAuditJ), ("binding", r.binding.toJ), ("outcome", r.outcome.toJ)]

/-- The fields of a record, and no others. -/
def auditKeys : List String := ["spec_version", "at", "requested", "snapshot", "provider", "response_id", "question_name", "question", "answer", "binding", "outcome"]

/-- Read a record: fields in any order, exactly those of `auditKeys`. -/
def AuditRecord.ofJ (j : J) : Except Refusal AuditRecord := do
  let kvs ← objOf "" (some auditKeys) j
  pure ⟨← natOf "spec_version" (← field "" kvs "spec_version"), ← natOf "at" (← field "" kvs "at"),
    ← strField "" kvs "requested", ← strField "" kvs "snapshot", ← strField "" kvs "provider", ← strField "" kvs "response_id",
    ← strField "" kvs "question_name", ← Question.decodeAt "question" (← field "" kvs "question"),
    ← Answer.ofAuditJ "answer" (← field "" kvs "answer"), ← Binding.ofJ "binding" (← field "" kvs "binding"),
    ← Outcome.ofJ "outcome" (← field "" kvs "outcome")⟩

end VbmDecision
