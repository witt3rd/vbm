#!/usr/bin/env bash
# RL1 (docs/spec.md, "Reflection of the family's rule"): no floating point and no second ratio in the production library.
#   1. the word `Float` does not occur in VbmProb/ or VbmProb.lean;
#   2. no `structure` in VbmProb/ has both a field `num` and a field `den` (a ratio is `Rat`, from `Init`).
# Usage: scripts/scan_rl1.sh [ROOT]   (default: the repository root). Prints each finding as FILE:LINE: WHY and exits 1 if there is any.
# scripts/rl1_selftest.sh is its negative self-test.
set -euo pipefail
root=${1:-$(dirname "$0")/..}
cd "$root"
files=$(find VbmProb -name '*.lean' 2>/dev/null | sort || true)
[ -f VbmProb.lean ] && files="$files
VbmProb.lean"
findings=""
for f in $files; do
  [ -n "$f" ] || continue
  hits=$(grep -nw 'Float' "$f" | sed -E "s|^([0-9]+):.*|$f:\\1: Float (no floating point in the library)|" || true)
  [ -z "$hits" ] || findings="$findings$hits
"
  # a structure block runs to the next line that starts at column 0; its fields are the indented `name :` lines
  ratio=$(awk -v F="$f" '
    function flush() { if (inS && hasNum && hasDen) printf "%s:%d: a structure with fields num and den (a second ratio; use Rat)\n", F, start; inS = 0; hasNum = 0; hasDen = 0 }
    /^[^ \t-]/ { flush(); if ($0 ~ /^(private |protected )?structure[ \t]/) { inS = 1; start = NR } }
    inS && /^[ \t]+(num|den)[ \t]*:/ { if ($1 == "num") hasNum = 1; if ($1 == "den") hasDen = 1 }
    inS && /^[ \t]+\(?(num|den)[ \t]*:/ { }
    END { flush() }' "$f")
  [ -z "$ratio" ] || findings="$findings$ratio
"
done
if [ -n "$findings" ]; then printf '%s' "$findings" >&2; exit 1; fi
echo "scan_rl1: ok"
