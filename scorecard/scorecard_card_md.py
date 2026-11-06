"""A scorecard JSON card rendered as a human-first Markdown page (GitHub renders it, so it works while the repository is private and after it is public). One function: `render(card, repo, pdf, previous, raw)`.
The page is a pure function of the card (and of the entry's repo URL and the card PDFs that exist): same inputs, same bytes, no timestamp. It is a render, never a second source: registry-table writes it next to the JSON and its --check fails when
the page differs from the card (a JSON edit without regenerating the page). Everything taken from the card is escaped: the card holds text the subject controls (file names, reasons, symbols). The verdicts are derived from the dimensions."""
import html, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import scorecard_verdicts as V
from scorecard_plain import PLAIN as _P, RETIRED
PLAIN = {**_P, **RETIRED}

DIMS = {"verified": "Verified", "construction": "Correct by construction", "generation": "Trusted code generation", "honesty": "Process honesty", "velocity": "Velocity (landedness)", "bare_metal": "Bare metal", "efficiency": "Resource efficiency"}
MARK = {"pass": "✅ pass", "fail": "❌ FAIL", "not-measurable": "⚠️ not measurable"}
VMARK = {"pass": "✅ PASS", "fail": "❌ FAIL", "pending": "⏳ PENDING"}


def esc(x):
    return html.escape(str(x), quote=False).replace("|", "&#124;").replace("`", "&#96;").replace("\n", " ")


def num(v): return "-" if v is None else (f"{v:g}" if isinstance(v, float) else str(v))
def floor(m): return "tracked, not floored" if not m.get("floor") else f"{m['floor']['op']} {num(m['floor']['value'])}"
def meaning(m):
    if m.get("id") in PLAIN: return PLAIN[m["id"]]
    d = " ".join(str(m.get("definition", "")).split()); i = d.find(". ")
    d = d[:i] if i > 0 else d.rstrip(".")
    return d if len(d) <= 170 else d[:167].rsplit(" ", 1)[0] + "..."


def value(m):
    v = num(m.get("value")) if m.get("bytes") is None else f"{m['bytes']} B"
    if m["id"].endswith("_seconds_warm") or m["id"].endswith("_seconds_cold"): v += " s"
    if m["id"] == "velocity.tier1_seconds_warm" and "gates_shown" in m: v += f" (skipped {len(m['gates_skipped'])} of {len(m['gates_shown']) + len(m['gates_skipped'])} gates)"
    return v


def comparator(m):
    if m["id"] == "efficiency.throughput_vs_best" and m.get("best_scalar"): return f"best scalar: {m['best_scalar']} ({m['gap_to_best_scalar_x']:g}x faster)"
    return ""


def render(c, repo="", pdf="", previous=(), raw="card.json"):
    ms = c["metrics"]; sub, sc = c["subject"], c["scorecard"]
    bad = [m["id"] for m in ms if m["status"] == "not-measurable" and not m.get("reason")]
    if bad: raise SystemExit(f"card-md: not-measurable without a reason: {', '.join(bad)}")
    vd = V.verdicts(c)
    if "verdicts" in c and c["verdicts"] != vd: raise SystemExit("card-md: the card's verdicts disagree with its dimensions")
    name = sub["name"]; commit = sub["commit"]
    out = [f"# {esc(name)}: scorecard", ""]
    out += [f"**Correctness: {VMARK[vd['correctness']['status']]}**" + (f" ({vd['correctness']['measured']} of {vd['correctness']['of']} primary dimensions measured; " + ", ".join(V.NAMES.get(n, n) for n in vd["correctness"]["not_defined_yet"]) + " not yet defined)" if vd["correctness"]["not_defined_yet"] and vd["correctness"]["status"] != "pending" else ""), ""]
    out += [f"**Landedness: {VMARK[vd['landedness']['status']]}**" + (f" ({esc(vd['landedness']['why'])})" if vd["landedness"].get("why") else "") + (f" (below its floor: {', '.join(esc(i) for i in vd['landedness']['below_floor'])})" if vd["landedness"]["below_floor"] else ""), ""]
    if vd["correctness"]["below_floor"]: out += ["Correctness below its floor: " + ", ".join(f"`{esc(i)}`" for i in vd["correctness"]["below_floor"]), ""]
    out += ["Two verdicts, no blended score. The profile (bare metal, resource efficiency) is in neither: " + ", ".join(f"{DIMS.get(k, k)} {v}" for k, v in vd["profile"]["dimensions"].items()) + ".", ""]
    out += [f"Subject: [{esc(name)}]({repo}) at commit `{commit[:12]}`, committed {esc(sub.get('commit_date', 'unknown'))}. Scorecard `{sc['sha'][:12]}`, adapter `{c['adapter']['sha256'][:12]}`, schema `{esc(c['schema'])}`.", ""]
    why = {}
    for m in ms:
        if m["status"] == "not-measurable": why.setdefault(m["reason"], []).append(m["id"])
    notes = {r: str(i + 1) for i, r in enumerate(sorted(why, key=lambda r: why[r]))}
    dims = sorted({m["dimension"] for m in ms}, key=lambda d: (list(V.GROUPS).index(V.group_of(d)), list(DIMS).index(d) if d in DIMS else 99, d))
    for g, title in (("correctness", "Correctness"), ("landedness", "Landedness"), ("profile", "Profile (in neither verdict)")):
        gd = [d for d in dims if V.group_of(d) == g]
        if not gd: continue
        out += [f"## {title}", ""]
        for d in gd:
            out += [f"### {esc(DIMS.get(d, d))}: {vd[g].get('dimensions', {}).get(d, '')}".rstrip(": "), "", "| Metric | Status | Value | Floor | Comparator | Meaning |", "|---|---|---|---|---|---|"]
            for m in (x for x in ms if x["dimension"] == d):
                st = MARK[m["status"]] + (f" ({notes[m['reason']]})" if m["status"] == "not-measurable" else "")
                out.append(f"| {esc(m['id'].split('.', 1)[1].replace('_', ' '))} | {st} | {esc(value(m))} | {esc(floor(m))} | {esc(comparator(m))} | {esc(meaning(m))} |")
            out.append("")
    if why: out += ["**Not measurable.** " + " ".join(f"({notes[r]}) {esc(r)}." for r in sorted(notes, key=notes.get)), ""]
    for m in ms:
        if m["id"] == "efficiency.throughput_vs_best" and m.get("comparators_mb_s") and m.get("subject_mb_s") is not None:
            out += ["## Comparison", "", "Throughput in MB/s on the floored corpus (the floor: within 2x of the best scalar comparator; the gap to non-scalar parsers is stated, not floored).", "", "| Implementation | MB/s |", "|---|---|"]
            out += [f"| {esc(k)}{' (this subject)' if k == name else ''} | {v:g} |" for k, v in sorted({**m["comparators_mb_s"], name: m["subject_mb_s"]}.items(), key=lambda kv: -kv[1])]
            out += ["", "Gaps to non-scalar comparators: " + ", ".join(f"{esc(k)} {v:g}x" for k, v in sorted((m.get("gap_to_non_scalar_x") or {}).items())) + "." if m.get("gap_to_non_scalar_x") else "", ""]
            pins = m.get("comparator_provenance") or {}
            if pins: out += ["Pinned comparators: " + ", ".join(f"{esc(k)} {esc(v['version'])}" for k, v in sorted(pins.items())) + ".", ""]
            if m.get("corpora"):
                names = sorted({k for r in m["corpora"] for k in r["mb_s"] if k != "subject"})
                out += [f"{m['corpora_at_or_above_floor']} of {len(m['corpora'])} corpora at or above the {m['corpora_floor_percent']:g}% line (the first is floored, the rest are reported).", "", "| Corpus | KB | " + " | ".join(esc(x) for x in [name] + names) + " | % of best scalar |", "|---|---|" + "---|" * (len(names) + 2)]
                out += [f"| {esc(r['name'])} | {r['bytes'] // 1000} | {r['mb_s']['subject']:g} | " + " | ".join(f"{r['mb_s'].get(k, 0):g}" for k in names) + f" | {r['percent_of_best_scalar']:g}% |" for r in m["corpora"]]
                out.append("")
    led = {m["id"]: m for m in ms}
    if "verified.trusted_c_lines" in led or "verified.trust_ledger_entries" in led:
        out += ["## Trust ledger", "", f"Trusted native code: {num(led.get('verified.trusted_c_lines', {}).get('value'))} lines" + (" (" + ", ".join(f"`{esc(f)}` {n}" for f, n in sorted(led["verified.trusted_c_lines"].get("files", {}).items())) + ")" if led.get("verified.trusted_c_lines", {}).get("files") else "") + f"; ledger entries: {num(led.get('verified.trust_ledger_entries', {}).get('value'))}.", ""]
    w = led.get("velocity.tier1_seconds_warm")
    if w and "gates_shown" in w: out += ["## Fast gate", "", f"Warm run {num(w['value'])} s (skipped {len(w['gates_skipped'])} of {len(w['gates_shown']) + len(w['gates_skipped'])} gates by design: " + ", ".join(esc(g) for g in w["gates_skipped"]) + ").", ""]
    out += ["## Reproduce", "", "```", f"mise exec -- scorecard/scorecard run --repo {repo or '<repo>'} --commit {commit} --sandbox scorecard/sandbox-bwrap", "```", "", "Same pinned commit, same bytes out (the card carries no run timestamp).", ""]
    out += ["## Links", ""] + [f"- [One-page PDF]({pdf})" if pdf else "- One-page PDF: none for this card"]
    out += [f"- [Raw JSON (the source this page is generated from)]({raw})"]
    out += [f"- Previous cards: " + ", ".join(f"[{esc(t)}]({u})" for t, u in previous) if previous else "- Previous cards: none"]
    return "\n".join(out) + "\n"
