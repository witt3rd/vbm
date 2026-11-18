import VbmScoreboardProofs.Direction
import VbmScoreboardProofs.Core
import VbmScoreboardProofs.Wire
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration, so a renamed or deleted theorem breaks this file), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "a-value-is-at-least-as-good-as-itself" (.proved [``VbmScoreboard.Direction.better_refl]),
  O "any-two-values-are-comparable" (.proved [``VbmScoreboard.Direction.better_total, ``VbmScoreboard.Direction.better_trans]),
  O "the-two-directions-are-opposite" (.proved [``VbmScoreboard.Direction.better_opposite]),
  O "check-gives-one-verdict-per-floor" (.proved [``VbmScoreboard.check_complete]),
  O "a-floor-is-held-when-its-reading-is-at-least-as-good" (.proved [``VbmScoreboard.check_held_iff]),
  O "an-unmeasured-floor-fails-closed" (.proved [``VbmScoreboard.check_unmeasured_fails]),
  O "passes-means-no-floor-regressed-or-unmeasured" (.proved [``VbmScoreboard.passes_iff_no_regression]),
  O "banking-only-moves-a-floor-toward-better" (.proved [``VbmScoreboard.bank_monotone]),
  O "banking-twice-is-banking-once" (.proved [``VbmScoreboard.bank_idempotent]),
  O "banking-never-records-a-worse-number" (.proved [``VbmScoreboard.bank_never_worse]),
  O "what-passed-still-passes-after-banking" (.proved [``VbmScoreboard.bank_then_check_passes]),
  O "a-reset-needs-a-reason-and-an-author" (.proved [``VbmScoreboard.reset_requires_reason]),
  O "a-reset-only-loosens-a-floor" (.proved [``VbmScoreboard.reset_only_loosens]),
  O "a-reset-is-recorded-with-its-reason-and-author" (.proved [``VbmScoreboard.reset_recorded]),
  O "a-history-is-append-only" (.proved [``VbmScoreboard.history_append_only]),
  O "progress-is-between-0-and-1000-permille" (.proved [``VbmScoreboard.progress_bounds]),
  O "progress-is-1000-once-the-target-is-reached" (.proved [``VbmScoreboard.progress_target_reached]),
  O "progress-never-falls-as-the-reading-improves" (.proved [``VbmScoreboard.progress_monotone_in_now]),
  O "a-reading-a-floor-and-a-history-entry-read-back-from-their-objects" (.proved [``VbmScoreboardWire.readingOfJson_readingJson, ``VbmScoreboardWire.floorOfJson_floorJson, ``VbmScoreboardWire.entryOfJson_entryJson]),
  O "readings-written-and-read-back-are-the-same-readings" (.proved [``VbmScoreboardWire.decode_encode_readings]),
  O "a-baseline-written-and-read-back-is-the-same-baseline-in-order" (.proved [``VbmScoreboardWire.decode_encode_baseline]),
  O "a-history-written-and-read-back-is-the-same-history" (.proved [``VbmScoreboardWire.decode_encode_history]),
  O "a-refusal-names-the-line-it-is-about" (.proved [``VbmScoreboardWire.decodeReadings_names_line, ``VbmScoreboardWire.decodeReadings_names_line_general]),
  O "a-version-other-than-1-is-refused-with-that-version" (.proved [``VbmScoreboardWire.decodeReadings_refuses_unknown_version]),
  O "a-repeated-metric-is-refused-at-the-line-of-the-second" (.proved [``VbmScoreboardWire.decodeReadings_refuses_duplicate, ``VbmScoreboardWire.dupCheck_refuses_any]),
  O "a-baseline-is-written-in-the-order-of-its-metrics-names" (.proved [``VbmScoreboardWire.encodeBaseline_sorted, ``VbmScoreboardWire.sortFloors_perm])
]
