#!/usr/bin/env bash
# The trust keys the tool derives from the tree that `land-lean trust` cannot (.land/lean.conf: LAND_LEAN_TRUST_KEYS_CMD): each kind of call the command-line tool makes outside Lean's proofs.
# A call in VbmScoreboardTool/ that is not in docs/trust-ledger.md fails the trust gate. Prints one key per line.
set -euo pipefail
cd "$(dirname "$0")/.."
has() { grep -rqE -- "$1" VbmScoreboardTool --include='*.lean'; }
if has 'IO\.FS\.(readFile|writeFile|rename|removeFile)|pathExists'; then echo io:files; fi
if has 'IO\.Process\.(spawn|output|getPID)|child\.(tryWait|kill)'; then echo io:process; fi
if has 'Timestamp\.now|monoMsNow'; then echo io:clock; fi
if has 'IO\.(println|eprintln)'; then echo io:streams; fi
