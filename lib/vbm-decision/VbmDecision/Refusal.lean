import VbmDecision.Prob
/-! # Typed refusals (S1b)

`RefusalCode` is the closed list of the ways the library refuses (spec section 9); `Refusal` is a code with the field path it concerns. A refusal is a value, never a default. -/
namespace VbmDecision

/-- Why a value, an answer, a threshold or a sample is refused, grouped as in the spec. -/
inductive RefusalCode where
  -- shape
  | wrongKind | missingField | unknownField | duplicateKey | unknownType | typeMismatch | badIndexKey | nestingTooDeep
  -- numbers
  | negative | tooPrecise | outOfRange | exponentTooLarge | notNatural
  -- request
  | tooManyQuestions | noQuestions | badQuestionName | tooFewOptions | tooManyOptions | tooFewLevels | tooManyLevels | badModelName | badState | tooManyStateParts
  -- answer set
  | missingAnswer | unexpectedAnswer
  -- answer
  | unknownOption | missingOption | sumOffOne | selectedNotMaximal | scoreOutOfScale | scoreInconsistent | legendMismatch | boxInverted | boxEmpty
  -- thresholds
  | thresholdKind | badThresholds | modelMismatch | snapshotMismatch
  -- calibration
  | badTarget | sampleTooSmall | sampleTooLarge | sampleOneSided | noThresholdMeetsTarget | bandInverted
  deriving DecidableEq, Repr

/-- A refusal: the code and the field path (`""` is the root; `thresholds` or `sample` for a threshold or a calibration). -/
structure Refusal where
  code : RefusalCode
  field : String
  deriving DecidableEq, Repr

/-- Every refusal code once, in the order of the spec. -/
def RefusalCode.all : List RefusalCode := [
  .wrongKind, .missingField, .unknownField, .duplicateKey, .unknownType, .typeMismatch, .badIndexKey, .nestingTooDeep,
  .negative, .tooPrecise, .outOfRange, .exponentTooLarge, .notNatural,
  .tooManyQuestions, .noQuestions, .badQuestionName, .tooFewOptions, .tooManyOptions, .tooFewLevels, .tooManyLevels, .badModelName, .badState, .tooManyStateParts,
  .missingAnswer, .unexpectedAnswer,
  .unknownOption, .missingOption, .sumOffOne, .selectedNotMaximal, .scoreOutOfScale, .scoreInconsistent, .legendMismatch, .boxInverted, .boxEmpty,
  .thresholdKind, .badThresholds, .modelMismatch, .snapshotMismatch,
  .badTarget, .sampleTooSmall, .sampleTooLarge, .sampleOneSided, .noThresholdMeetsTarget, .bandInverted
]

/-- The numeric refusal of a decimal conversion, as the spec's refusal code. -/
def ScaleRefusal.toCode : ScaleRefusal → RefusalCode
  | .negative => .negative
  | .tooPrecise => .tooPrecise
  | .outOfRange => .outOfRange
  | .exponentTooLarge => .exponentTooLarge

end VbmDecision
