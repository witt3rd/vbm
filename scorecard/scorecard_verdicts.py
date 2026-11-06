"""The verdicts of a card (scorecard/SPEC.md, "The verdicts"; DECISIONS 18, the owner's ruling: correctness first, landedness second, then a profile; no blended score).
ONE function, used by the runner (to write the card's `verdicts`), by card-to-page and by registry-table (to read any card, including the scorecard-1 cards written before the verdicts existed): `verdicts(card)`.
  correctness  the primary ideals: verified, construction (correct by construction), generation (trusted code generation: no metric is defined yet), honesty. FAIL when a floored metric of one of them is below its floor (not-measurable included).
  landedness   velocity: how fast and cleanly changes land. PENDING for a card written before the warm/cold split of the tier-1 metric (it carries the retired velocity.tier1_seconds): its landedness is not judged by a definition that no longer exists.
  profile      bare_metal and efficiency: each dimension's own status, listed with its values and floors, in NEITHER verdict.
Nothing is averaged and nothing is blended: two verdict lines and a profile. The Correctness line states its coverage while a primary dimension is undefined (`label`; main's addition to DECISIONS 18). This file is gate-defining (scripts/protected-paths.txt)."""

CORRECTNESS = ("verified", "construction", "generation", "honesty")
LANDEDNESS = ("velocity",)
PROFILE = ("bare_metal", "efficiency")
GROUPS = {"correctness": CORRECTNESS, "landedness": LANDEDNESS, "profile": PROFILE}
LEGACY = "velocity.tier1_seconds"                                              # retired: split into the two below (DECISIONS 17)
SPLIT = ("velocity.tier1_seconds_warm", "velocity.tier1_seconds_cold")
NAMES = {"verified": "Verified", "construction": "By construction", "generation": "Trusted generation", "honesty": "Process honesty"}
NOT_DEFINED = ("generation",)                                                  # a correctness dimension with no metric defined yet: said on the card, never silently dropped


def group_of(dim):
    return next((g for g, ds in GROUPS.items() if dim in ds), "profile")       # an unknown dimension is a profile entry: it can never pass a verdict by being new


def verdicts(card):
    dims, ids = card["dimensions"], {m["id"] for m in card["metrics"]}
    def block(names):
        have = [n for n in names if n in dims]
        return {"dimensions": {n: dims[n]["status"] for n in have}, "below_floor": [i for n in have for i in dims[n]["below_floor"]]}
    c, l = block(CORRECTNESS), block(LANDEDNESS)
    c["status"] = "fail" if any(s == "fail" for s in c["dimensions"].values()) else "pass" if c["dimensions"] else "pending"
    c["not_defined_yet"] = [n for n in NOT_DEFINED if n not in dims]
    c["measured"], c["of"] = len(c["dimensions"]), len([n for n in CORRECTNESS if n != "honesty" or "honesty" in dims])   # Process honesty counts only on a card that has it (the attack suite and gate self-tests are deleted; recorded cards keep theirs)
    if LEGACY in ids and not any(i in ids for i in SPLIT): l["status"], l["why"] = "pending", "scored before the warm/cold split (DECISIONS 17): re-run"
    else: l["status"] = "fail" if any(s == "fail" for s in l["dimensions"].values()) else "pass" if l["dimensions"] else "pending"
    p = {n: dims[n]["status"] for n in PROFILE if n in dims}
    p.update({n: d["status"] for n, d in dims.items() if group_of(n) == "profile" and n not in p})
    return {"correctness": c, "landedness": l, "profile": {"dimensions": p, "below_floor": [i for n in p for i in dims[n]["below_floor"]]}}


def label(v, short=False):
    """The text of a verdict: PASS, FAIL or PENDING; the Correctness verdict ALWAYS states its coverage while a primary dimension is undefined (never a bare PASS): `PASS (3 of 4 primary dimensions measured; Trusted generation not yet defined)`. short: for the registry table."""
    t = v["status"].upper()
    nd = v.get("not_defined_yet")
    if not nd or v["status"] == "pending": return t
    names = ", ".join(NAMES.get(n, n) for n in nd)
    return f"{t} ({v['measured']} of {v['of']}{'' if short else ' primary dimensions measured'}; {names} not yet defined)"
