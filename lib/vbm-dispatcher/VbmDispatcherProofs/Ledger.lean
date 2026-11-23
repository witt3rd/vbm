import VbmDispatcherProofs.Tick
import VbmDispatcherProofs.Run
import VbmDispatcherProofs.Model
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger`: a claim is `proved` only by naming theorems (double-backtick names are checked at elaboration), `open_` while nothing is proved, or a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "a-finished-tick-is-absorbing" (.proved [``VbmDispatcher.tick_ended_absorbing]),
  O "the-guard-comes-first-and-a-refusal-writes-nothing" (.proved [``VbmDispatcher.tick_no_headroom_ends_skipped, ``VbmDispatcher.tick_headroom_reads_queue]),
  O "a-claim-is-only-ever-for-the-item-choose-returned" (.proved [``VbmDispatcher.tick_claims_only_chosen]),
  O "only-a-won-claim-starts-a-run-and-a-lost-race-starts-nothing" (.proved [``VbmDispatcher.tick_started_only_on_win, ``VbmDispatcher.tick_lost_race_starts_nothing]),
  O "an-unreachable-store-starts-nothing" (.proved [``VbmDispatcher.tick_store_down_ends]),
  O "a-tick-ends-at-most-once" (.proved [``VbmDispatcher.tick_step_room, ``VbmDispatcher.tick_ends_at_most_once]),
  O "a-closed-run-is-absorbing" (.proved [``VbmDispatcher.run_closed_absorbing]),
  O "the-lease-is-renewed-only-at-a-beat-while-the-worker-runs" (.proved [``VbmDispatcher.run_renews_only_at_beat]),
  O "the-finish-is-the-workers-own-report-unchanged" (.proved [``VbmDispatcher.run_finishes_only_the_report]),
  O "a-lost-lease-or-the-deadline-stops-the-worker-and-reports-nothing" (.proved [``VbmDispatcher.run_lost_lease_stops_worker, ``VbmDispatcher.run_deadline_stops_worker,
    ``VbmDispatcher.run_stopping_ignores_report]),
  O "an-item-is-finished-at-most-once" (.proved [``VbmDispatcher.run_step_finish_room, ``VbmDispatcher.run_finishes_at_most_once]),
  O "a-run-is-cleaned-up-exactly-once-on-every-path" (.proved [``VbmDispatcher.run_step_clean_conserved, ``VbmDispatcher.run_clean_conserved, ``VbmDispatcher.run_cleans_at_most_once,
    ``VbmDispatcher.run_closed_means_cleaned]),
  O "control-never-depends-on-the-contents-of-a-report" (.proved [``VbmDispatcher.run_ignores_report_content]),
  O "every-conformance-scenario-obeys-the-port-discipline" (.proved [``VbmDispatcher.scenarios_obey_the_discipline]),
  O "the-ports-meet-their-laws" (.limit "the host's readings, the queue, the claim, the lease renewal, the finish, the worker and its cleanup are bindings of the application; that they meet the laws the machines rely on (a claim has one winner, a renewal and a finish are fenced by the delivery number, a finish is idempotent on retry: the store's laws in `VbmDispatcher.Pool`) is the application's conformance suite, not a theorem here"),
  O "the-guard-is-local-and-a-host-without-headroom-chooses-nothing" (.proved [``VbmDispatcher.Pool.guard_is_local]),
  O "the-chooser-picks-only-a-claimable-qualified-item-and-is-deterministic" (.proved [``VbmDispatcher.Pool.choose_entry, ``VbmDispatcher.Pool.choose_requires_qualified,
    ``VbmDispatcher.Pool.choose_deterministic, ``VbmDispatcher.Pool.canClaim_perm]),
  O "aging-lets-no-priority-overtake-forever-and-deferral-ends" (.proved [``VbmDispatcher.Pool.no_overtake_after_aging, ``VbmDispatcher.Pool.patience_bounds_deferral,
    ``VbmDispatcher.Pool.lost_item_deferred]),
  O "a-claim-has-one-winner-and-raises-the-delivery-number" (.proved [``VbmDispatcher.Pool.claim_exclusive, ``VbmDispatcher.Pool.one_winner, ``VbmDispatcher.Pool.claim_raises_gen,
    ``VbmDispatcher.Pool.takeover_after_expiry]),
  O "renewal-and-finish-are-fenced-by-the-delivery-number" (.proved [``VbmDispatcher.Pool.renew_fenced, ``VbmDispatcher.Pool.renew_holder, ``VbmDispatcher.Pool.finish_fenced,
    ``VbmDispatcher.Pool.zombie_cannot_finish]),
  O "a-finish-is-idempotent-and-a-finished-id-is-never-sendable-again" (.proved [``VbmDispatcher.Pool.finish_idempotent, ``VbmDispatcher.Pool.finished_never_resent,
    ``VbmDispatcher.Pool.send_once]),
  O "the-chosen-item-can-be-claimed-through-the-store" (.proved [``VbmDispatcher.Pool.choose_then_claim])]
