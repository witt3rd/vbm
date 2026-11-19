import VbmDecisionProofs.Audit
import VbmDecisionProofs.Battery
import VbmDecisionProofs.Check
import VbmDecisionProofs.Core
import VbmDecisionProofs.Decode
import VbmDecisionProofs.Prob
import VbmDecisionProofs.Refusal
import VbmDecisionProofs.Limits
import VbmDecisionProofs.Message
import VbmDecisionProofs.Truth
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "the-library-has-a-name" (.proved [``VbmDecision.libraryName_nonempty]),
  O "prob-ofdecimal-exact" (.proved [``VbmDecision.ofDecimal_exact]),
  O "prob-toscaled-refuses-imprecise" (.proved [``VbmDecision.toScaled_tooPrecise]),
  O "prob-roundtrip" (.proved [``VbmDecision.ofDecimal_toDecimal]),
  O "prob-range" (.proved [``VbmDecision.ofDecimal_range, ``VbmDecision.ofDecimal_negative, ``VbmDecision.ofDecimal_outOfRange]),
  O "refusal-codes-complete" (.proved [``VbmDecision.refusalCode_all_complete, ``VbmDecision.refusalCode_all_nodup, ``VbmDecision.refusalCode_count, ``VbmDecision.refusal_ext_code, ``VbmDecision.scaleRefusal_toCode_injective]),
  O "named-limits-values" (.proved [``VbmDecision.limits_values, ``VbmDecision.maxSample_quadratic]),
  O "named-limits-consistent" (.proved [``VbmDecision.sumEpsilon_le, ``VbmDecision.sumEpsilon_lt_scale, ``VbmDecision.calibration_limits_consistent, ``VbmDecision.structural_limits_roomy]),
  O "check-sound-complete" (.proved [``VbmDecision.question_check_ok_iff, ``VbmDecision.checkAnswer_ok_iff, ``VbmDecision.checkThresholds_ok_iff, ``VbmDecision.checkAnswer_error_iff, ``VbmDecision.checkAnswer_typeMismatch]),
  O "decide-total" (.proved [``VbmDecision.decide_total, ``VbmDecision.outcome_exclusive]),
  O "fail-closed" (.proved [``VbmDecision.fail_closed_answer, ``VbmDecision.fail_closed_question, ``VbmDecision.fail_closed_thresholds, ``VbmDecision.fail_closed_binding, ``VbmDecision.decide_modelMismatch, ``VbmDecision.decide_snapshotMismatch, ``VbmDecision.gate_ok_iff]),
  O "noul-characterised" (.proved [``VbmDecision.noul_yes_iff, ``VbmDecision.noul_no_iff, ``VbmDecision.noul_band_iff]),
  O "one-decision" (.proved [``VbmDecision.noul_no_overlap, ``VbmDecision.noul_one_decision, ``VbmDecision.choice_decision_is_selected]),
  O "noul-monotone" (.proved [``VbmDecision.noul_monotone_yes, ``VbmDecision.noul_monotone_no]),
  O "score-monotone" (.proved [``VbmDecision.score_monotone_above, ``VbmDecision.score_monotone_below]),
  O "threshold-monotone" (.proved [``VbmDecision.threshold_monotone]),
  O "choice-characterised" (.proved [``VbmDecision.choice_decided_iff, ``VbmDecision.choice_lowProbability_iff, ``VbmDecision.choice_lowMargin_iff]),
  O "decode-refuses-unknown" (.partly [``VbmDecision.objOf_duplicate, ``VbmDecision.Question.decodeAt_duplicate, ``VbmDecision.Answer.decodeAt_duplicate, ``VbmDecision.Question.decodeAt_unknownField, ``VbmDecision.Answer.decodeAt_unknownField, ``VbmDecision.Question.decodeAt_extra, ``VbmDecision.Answer.decodeAt_extra, ``VbmDecision.Question.decodeAt_unknownType, ``VbmDecision.Answer.decodeAt_unknownType, ``VbmDecision.Request.decodeAt_duplicate, ``VbmDecision.Request.decodeAt_unknownField, ``VbmDecision.Response.decodeAt_duplicate, ``VbmDecision.Response.decodeAt_unknownField] "proved for the top-level object of a Question, an Answer, a Request and a Response, and a duplicate key in any object read by objOf; an extra key in a nested object (criteria, box, usage) is witnessed by examples only"),
  O "decode-wellformed" (.proved [``VbmDecision.Answer.decodeAt_wellFormed, ``VbmDecision.Answer.decode_wellFormed, ``VbmDecision.Question.decodeAt_valid, ``VbmDecision.Question.decode_valid]),
  O "message-roundtrip" (.proved [``VbmDecision.request_roundtrip, ``VbmDecision.request_encode_decode, ``VbmDecision.response_roundtrip, ``VbmDecision.response_encode_decode, ``VbmDecision.request_check_ok_iff, ``VbmDecision.request_encode_refuses, ``VbmDecision.Request.decode_valid]),
  O "decode-total" (.proved [``VbmDecision.decode_total, ``VbmDecision.Question.decode_nestingTooDeep, ``VbmDecision.Answer.decode_nestingTooDeep, ``VbmDecision.decode_within, ``VbmDecision.Request.decode_nestingTooDeep, ``VbmDecision.Response.decode_nestingTooDeep, ``VbmDecision.message_decode_total]),
  O "audit-roundtrip" (.proved [``VbmDecision.audit_roundtrip, ``VbmDecision.answer_audit_roundtrip, ``VbmDecision.outcome_roundtrip, ``VbmDecision.binding_roundtrip]),
  O "audit-faithful" (.proved [``VbmDecision.audit_faithful]),
  O "audit-total-on-refusal" (.proved [``VbmDecision.audit_total_on_refusal, ``VbmDecision.audit_ok_iff, ``VbmDecision.audit_error_iff]),
  O "battery-check-sound-complete" (.partly [``VbmDecision.Battery.check_ok_iff, ``VbmDecision.Table.check_ok_iff, ``VbmDecision.checkItems_ok_iff, ``VbmDecision.checkBands_ok_iff, ``VbmDecision.checkOutcomes_ok_iff] "check is ok iff Valid is proved; that each refusal code arises at its path is witnessed by one example per code, not proved"),
  O "battery-score-range" (.proved [``VbmDecision.battery_score_range, ``VbmDecision.score_ok_iff, ``VbmDecision.scoreN_le]),
  O "battery-score-monotone" (.proved [``VbmDecision.battery_score_monotone, ``VbmDecision.score_le_iff, ``VbmDecision.score_lt_iff]),
  O "battery-score-permutation" (.proved [``VbmDecision.battery_score_permutation]),
  O "battery-score-zero-weight" (.proved [``VbmDecision.battery_score_zero_weight]),
  O "battery-score-refuses" (.proved [``VbmDecision.battery_score_refuses, ``VbmDecision.scoreD_eq_zero_iff]),
  O "battery-fail-closed" (.proved [``VbmDecision.battery_fail_closed, ``VbmDecision.evaluate_ok_iff]),
  O "battery-faults-listed" (.proved [``VbmDecision.battery_faults_listed, ``VbmDecision.faults_mem, ``VbmDecision.faults_nodup]),
  O "veto-decides" (.proved [``VbmDecision.veto_decides]),
  O "veto-conflict" (.proved [``VbmDecision.veto_conflict, ``VbmDecision.verdictOf_conflict]),
  O "veto-absent-score-decides" (.proved [``VbmDecision.veto_absent_score_decides, ``VbmDecision.veto_absent_no_veto_items]),
  O "table-disjoint" (.proved [``VbmDecision.table_disjoint, ``VbmDecision.table_index_iff]),
  O "table-monotone" (.proved [``VbmDecision.table_monotone]),
  O "table-cut-side" (.proved [``VbmDecision.table_cut_lo, ``VbmDecision.table_cut_hi_next, ``VbmDecision.table_cut_hi_gap, ``VbmDecision.table_cut_one]),
  O "table-gapless-total" (.proved [``VbmDecision.table_gapless_total]),
  O "battery-verdict-in-table" (.proved [``VbmDecision.battery_verdict_in_table]),
  O "battery-monotone" (.proved [``VbmDecision.battery_monotone]),
  O "battery-permutation" (.proved [``VbmDecision.battery_permutation, ``VbmDecision.valid_perm]),
  O "battery-record-replay" (.proved [``VbmDecision.battery_record_replay]),
  O "battery-record-used" (.proved [``VbmDecision.battery_record_used])
]
