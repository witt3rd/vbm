#!/usr/bin/env bash
# Tier 1: a card is ONE page (the house format). Every committed card PDF (docs/cards/*.pdf) has exactly one page, counted from the PDF itself (no publishing tool is needed, so CI can check it). Negative self-test: the counter
# is shown on a hand-built two-page PDF (it must say 2 and the check must fail) and on a one-page PDF (1).
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
fail() { echo "tier1: cards: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
pages() { python3 - "$1" <<'PY'
import re, sys
b = open(sys.argv[1], "rb").read()
print(len(re.findall(rb"/Type\s*/Page(?![s\w])", b)))
PY
}
mkpdf() {   # mkpdf FILE N: a minimal PDF with N empty pages
  python3 - "$1" "$2" <<'PY'
import sys
f, n = sys.argv[1], int(sys.argv[2])
kids = " ".join(f"{3 + i} 0 R" for i in range(n))
objs = ["<< /Type /Catalog /Pages 2 0 R >>", f"<< /Type /Pages /Kids [{kids}] /Count {n} >>"] + ["<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 100] >>"] * n
out, offs = b"%PDF-1.4\n", []
for i, o in enumerate(objs, 1): offs.append(len(out)); out += f"{i} 0 obj\n{o}\nendobj\n".encode()
x = len(out); out += f"xref\n0 {len(objs) + 1}\n0000000000 65535 f \n".encode() + b"".join(f"{o:010d} 00000 n \n".encode() for o in offs) + f"trailer\n<< /Size {len(objs) + 1} /Root 1 0 R >>\nstartxref\n{x}\n%%EOF\n".encode()
open(f, "wb").write(out)
PY
}
mkpdf "$T/one.pdf" 1; mkpdf "$T/two.pdf" 2
[ "$(pages "$T/one.pdf")" = 1 ] && [ "$(pages "$T/two.pdf")" = 2 ] && ran_case || fail "the page counter is wrong on hand-built PDFs: $(pages "$T/one.pdf") / $(pages "$T/two.pdf")"
check() { local bad=0 f; for f in "$@"; do [ "$(pages "$f")" = 1 ] || { echo "$f: $(pages "$f") pages, a card is exactly 1" >&2; bad=1; }; done; return $bad; }
check "$T/two.pdf" 2>/dev/null && fail "negative self-test: a two-page card passed the one-page check"
check "$T/one.pdf" && ran_case || fail "a one-page PDF failed the check"
n=0; for f in docs/cards/*.pdf; do [ -f "$f" ] || continue; n=$((n + 1)); done
[ "$n" -ge 1 ] && ran_case || fail "no committed card PDF to check"
check docs/cards/*.pdf && ran_case || fail "a committed card is not exactly one page"
ran_done test_cards_one_page
echo "tier1: cards: every committed card PDF ($n) is exactly one page; the check fails a two-page PDF: ok"
