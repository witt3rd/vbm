#!/usr/bin/env bash
# Tier 1: the known-answer vectors of docs/spec.md section 10. vectors/Vectors.lean states each answer as an `example` over the real functions (checked when it compiles) and prints
# each as an `ID KEY VALUE` line; this script RE-DERIVES every line with a tiny reference of its own (shell integer arithmetic, no library code) and compares line by line.
# A disagreement is a bug in one of them. The comparison is shown able to fail (a mutated line is refused). Ends with `ran: vectors: N cases`.
set -euo pipefail
cd "$(dirname "$0")/.."
. ../../.land/tool/lib/ran.sh
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "vectors: $*" >&2; exit 1; }

# ---- the reference (integers only), s = 10 ----
s=10
sq() { echo $(( $1 * $1 )); }
brier_bin() { local p=$1 y=$2; sq $(( p - y * s )); }                       # (p - y s)^2
brier_cat() { local o=$1; shift; local j=0 t=0 p; for p in "$@"; do t=$(( t + $(sq $(( p - (j == o ? s : 0) ))) )); j=$((j+1)); done; echo $t; }
exp_bin() { local q=$1 p=$2; echo $(( q * $(brier_bin "$p" 1) + (s - q) * $(brier_bin "$p" 0) )); }
pin() { local lv=$1 q=$2 o=$3; if [ "$o" -ge "$q" ]; then echo $(( lv * (o - q) )); else echo $(( (s - lv) * (q - o) )); fi; }
interval() { local t=$1 lo=$2 hi=$3 o=$4 w=$(( 2 * $1 * ($3 - $2) )); if [ "$o" -lt "$lo" ]; then echo $(( w + 2 * s * (lo - o) )); elif [ "$o" -gt "$hi" ]; then echo $(( w + 2 * s * (o - hi) )); else echo $w; fi; }
# RPS: thresholds F_j = cumulative of ps, indicator [obs <= vals_j], for j < m-1
rps() { local obs=$1; shift; local m=$(( $# / 2 )) i F=0 t=0 v p; local -a vs=("${@:1:m}") ps=("${@:m+1}")
  for (( i = 0; i < m - 1; i++ )); do F=$(( F + ps[i] )); t=$(( t + $(sq $(( F - (obs <= vs[i] ? s : 0) ))) )); done; echo $t; }
prod() { local t=1 x; for x in "$@"; do t=$(( t * x )); done; echo $t; }
cmp3() { if [ "$1" -gt "$2" ]; then echo gt; elif [ "$1" -lt "$2" ]; then echo lt; else echo eq; fi; }

# V9: reliability over edges [0,5,10], the last bin takes s
ps9=(2 3 4 7 8 9 10); hs9=(0 1 0 1 1 0 1); N=7
n0=0 h0=0 p0=0 n1=0 h1=0 p1=0
for i in "${!ps9[@]}"; do p=${ps9[i]}
  if [ "$p" -lt 5 ]; then n0=$((n0+1)); h0=$((h0+hs9[i])); p0=$((p0+p)); else n1=$((n1+1)); h1=$((h1+hs9[i])); p1=$((p1+p)); fi; done
absv() { echo $(( $1 < 0 ? -$1 : $1 )); }
cal=$(( $(absv $(( h0 * s - p0 ))) + $(absv $(( h1 * s - p1 ))) ))
H=$(( h0 + h1 )); SP=$(( p0 + p1 ))

# V12: bootstrap of d = [2,-1,3], R = 4, draws as listed; the sums, the sorted sums, the interval at t = 2
d=(2 -1 3); draws=(0 0 0 1 1 1 2 2 2 0 1 2); n=3; R=4
sums=(); for (( r = 0; r < R; r++ )); do t=0; for (( i = 0; i < n; i++ )); do t=$(( t + d[draws[r*n+i]] )); done; sums+=("$t"); done
sorted=("${sums[@]}"); for (( i = 0; i < R; i++ )); do for (( j = 0; j + 1 < R - i; j++ )); do
  if [ "${sorted[j]}" -gt "${sorted[j+1]}" ]; then x=${sorted[j]}; sorted[j]=${sorted[j+1]}; sorted[j+1]=$x; fi; done; done
tt=2; k=$(( R * tt / s )); lo=${sorted[k]}; hi=${sorted[R-1-k]}
dsum=$(( d[0] + d[1] + d[2] ))
verdict() { local min=$1; if [ "$n" -lt "$min" ]; then echo "refused $n $min"; elif [ "$hi" -lt 0 ] && [ "$dsum" -lt 0 ]; then echo better; elif [ "$lo" -gt 0 ] && [ "$dsum" -gt 0 ]; then echo worse; else echo inconclusive; fi; }
lst() { local o="[" x; for x in "$@"; do [ "$o" = "[" ] || o+=", "; o+=$x; done; echo "$o]"; }   # [a, b, c]

cat > "$T/expected" <<EOF
V1 brier $(brier_bin 7 1)
V2 brier $(brier_bin 7 0)
V3 brier $(brier_cat 0 5 3 2)
V4 e57 $(exp_bin 7 5)
V4 e77 $(exp_bin 7 7)
V5 rps $(rps 2 1 2 3 5 3 2)
V6 pinball $(pin 9 5 8) $(pin 9 5 3)
V7 interval $(interval 1 2 6 9) $(( 2 * ( $(pin 1 2 9) + $(pin 9 6 9) ) ))
V8 products $(prod 5 8) $(prod 6 4) $(cmp3 "$(prod 5 8)" "$(prod 6 4)")
V8 enclosure $(( -(1 << 3) )) $(( -(1 << 3) ))
V9 rows 0,5,$n0,$h0,$p0 5,10,$n1,$h1,$p1 N=$N
V10 calib $cal/$(( N * s ))
V11 citl $SP/$(( N * s )) $H/$N $(( H * s - SP ))/$(( N * s ))
V12 sums $(lst "${sums[@]}")
V12 sorted $(lst "${sorted[@]}")
V12 ci $lo/$n $hi/$n
V12 mean $dsum/$n
V13 verdict $(verdict 30)
V13 compare $(verdict 30) $dsum/$n none
V14 verdict $(verdict 3)
V14 compare $(verdict 3) $dsum/$n $lo/$n $hi/$n
EOF

# ---- the library's answers ----
lake env lean -DwarningAsError=true --run vectors/Vectors.lean > "$T/actual" || fail "vectors/Vectors.lean did not compile or run"
[ -s "$T/actual" ] || fail "the library printed no vector"

# ---- compare, line by line (each line is one case) ----
lines=$(wc -l < "$T/expected" | tr -d ' ')
[ "$lines" = "$(wc -l < "$T/actual" | tr -d ' ')" ] || fail "the reference has $lines vectors, the library $(wc -l < "$T/actual" | tr -d ' ')"
while IFS= read -r e <&3 && IFS= read -r a <&4; do
  [ "$e" = "$a" ] || fail "disagreement: reference '$e' library '$a'"
  ran_case
done 3< "$T/expected" 4< "$T/actual"

# ---- the comparison can fail: a mutated library line must be refused ----
sed 's/^V1 brier 9$/V1 brier 10/' "$T/actual" > "$T/mutated"
must_fail "a mutated vector is flagged" bash -c 'diff "$1" "$2"' _ "$T/expected" "$T/mutated"
ran_done vectors
