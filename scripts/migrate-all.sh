#!/usr/bin/env bash
# migrate-all.sh NAME...: migrate libraries one after another (migrate-library.sh), with per-library choices from the environment:
#   SCRUB_LIBS="a b"          libraries whose text names the product (SCRUB=1 for them; also set SCRUB_PRODUCT and SCRUB_MACHINES)
#   ID_NAME="..."             the name the project commits under (required)
#   REVIEWED_BRANCHES="x y"   branches reviewed and left
# One library at a time (the trunk must be quiet), each archived in the background after its push. Stops at the first failure.
here=$(cd "$(dirname "$0")" && pwd); export PATH=$HOME/.local/share/mise/shims:$PATH
LOG=/var/tmp/migrate-all.log; exec >>"$LOG" 2>&1
for n in "$@"; do
  echo "=== $(date '+%F %T') migrating $n"
  s=0; case " ${SCRUB_LIBS:-} " in *" $n "*) s=1;; esac
  SCRUB=$s "$here/migrate-library.sh" "$n" --push || { echo "=== $n FAILED: stopping the batch (nothing was pushed for it)"; exit 1; }
  ( "$here/archive-old-repo.sh" "$n" > "/var/tmp/archive-$n.log" 2>&1; echo "archive $n exit $?" >> "$LOG" ) &
done
wait; echo "=== $(date '+%F %T') batch done: $*"
