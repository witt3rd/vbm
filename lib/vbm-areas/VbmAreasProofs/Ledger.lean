import VbmAreasProofs.Core
import VbmAreasProofs.Glob
import VbmAreasProofs.Area
import VbmAreasProofs.Decide
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "the-library-has-a-name" (.proved [``VbmAreas.libraryName_nonempty]),
  O "glob-matcher-total" (.proved [``VbmAreas.matches_total]),
  O "glob-star-matches-any-run" (.proved [``VbmAreas.star_iff, ``VbmAreas.star_matches_all, ``VbmAreas.double_star]),
  O "glob-query-matches-one-char" (.proved [``VbmAreas.query_cons, ``VbmAreas.query_nil]),
  O "glob-literal-matches-only-itself" (.proved [``VbmAreas.literal_iff]),
  O "glob-refusal-exact" (.proved [``VbmAreas.refusalChars_none_iff, ``VbmAreas.valid_iff, ``VbmAreas.validCwd_iff]),
  O "glob-every-reason-has-a-witness" (.proved [``VbmAreas.witness_refused]),
  O "glob-start-dir-is-a-valid-directory-prefix" (.proved [``VbmAreas.startDir_prefix]),
  O "glob-under-by-whole-segments" (.proved [``VbmAreas.under_root, ``VbmAreas.under_irrefl]),
  O "area-owns-is-the-rule" (.proved [``VbmAreas.owns_iff, ``VbmAreas.excluded_not_owned]),
  O "area-owners-in-file-order-no-duplicates" (.proved [``VbmAreas.mem_owners, ``VbmAreas.owners_sublist, ``VbmAreas.owners_nodup]),
  O "areas-validate-exact" (.proved [``VbmAreas.area_refusal_none_iff, ``VbmAreas.validate_none_iff, ``VbmAreas.check_ok]),
  O "areas-valid-names-unique-and-shaped" (.proved [``VbmAreas.valid_names_nodup, ``VbmAreas.valid_names_ok]),
  O "areas-every-glob-refusal-has-a-witness-file" (.proved [``VbmAreas.reason_witness_file]),
  O "area-encloses-by-whole-segments-and-not-excluded" (.proved [``VbmAreas.encloses_iff, ``VbmAreas.encloses_not_excluded, ``VbmAreas.encloses_of_under, ``VbmAreas.enclosureLength_isSome_iff]),
  O "decide-touched-in-run-and-run-is-touched-unless-full" (.proved [``VbmAreas.touched_sub_run, ``VbmAreas.run_eq_touched, ``VbmAreas.full_run_all, ``VbmAreas.partition]),
  O "decide-release-candidate-runs-every-area" (.proved [``VbmAreas.rc_runs_all]),
  O "decide-unmapped-and-gate-defining-imply-full" (.proved [``VbmAreas.unmapped_full, ``VbmAreas.gate_full, ``VbmAreas.unmappedAt_iff]),
  O "decide-owned-touches-and-renames-split" (.proved [``VbmAreas.owned_touched, ``VbmAreas.owned_touched_file, ``VbmAreas.rename_decide, ``VbmAreas.rename_touched, ``VbmAreas.touched_append, ``VbmAreas.split_rename, ``VbmAreas.split_length, ``VbmAreas.split_norename, ``VbmAreas.flatMap_split_len]),
  O "decide-monotone" (.proved [``VbmAreas.monotone]),
  O "decide-steps-are-the-steps-of-run-once-in-file-order" (.proved [``VbmAreas.mem_steps, ``VbmAreas.steps_sublist_nodup, ``VbmAreas.stepless, ``VbmAreas.inert_iff]),
  O "decide-closest-enclosing-all-ties-run" (.proved [``VbmAreas.mem_closest, ``VbmAreas.closest_eq_nil, ``VbmAreas.closest_touched]),
  O "decide-inert-never-owns-a-deleted-path" (.proved [``VbmAreas.inert_not_owner_deleted, ``VbmAreas.inert_owner_iff])
]
