"""Plain one-line meanings, one per metric: data about the metrics for a reader who has never seen the scorecard (the technical definition stays in METRICS and in the card JSON).
Not a metric definition: adding or rewording a line here changes no measurement, floor or verdict. scripts/test_plain_meanings.sh holds every line to `problems`."""
import re

PLAIN = {
    "verified.unproved_escapes": "Counts places where a proof is skipped or faked; zero means every claim is actually proved.",
    "verified.specified_share": "How much of the code has a written, machine-checked specification.",
    "verified.nonstandard_axioms": "Counts proofs that quietly rely on assumptions beyond the usual logic; zero means none do.",
    "verified.trusted_c_lines": "Lines of hand-written C that must be trusted because no proof covers them; fewer is better.",
    "verified.trust_ledger_entries": "How many things the project openly lists as trusted without proof; fewer is better.",
    "verified.non_vacuity": "Whether the specification has teeth: deliberately broken specs should make the proofs fail.",
    "bare_metal.freestanding_build": "Whether the code builds with no operating system or standard library underneath it.",
    "bare_metal.wasm_freestanding_build": "Whether the code also builds as a standalone WebAssembly module with no outside help.",
    "bare_metal.libc_symbols": "Counts calls the built code makes into the C standard library; zero means fully self-contained.",
    "construction.hand_written_tests": "Counts test cases a person wrote by hand; zero means correctness comes from proofs and generated checks.",
    "construction.mutation_score": "Share of deliberately injected bugs that the checks catch; 100 means none slip through.",
    "efficiency.throughput_vs_best": "Speed on real data as a percent of the fastest comparable library; 50 means within twice as slow.",
    "velocity.tier1_seconds_warm": "Seconds the quick check takes for a typical change once caches are warm; this is what a landing costs.",
    "velocity.tier1_seconds_cold": "Seconds the quick check takes on a fresh copy with no caches; this is what a newcomer pays.",
    "velocity.open_prs": "How many proposed changes are waiting to be merged; zero means nothing is stuck in review.",
    "velocity.commits_per_hour": "How fast changes land on the main branch, in commits per hour.",
    "velocity.p90_commit_to_main_seconds": "How long, for 9 in 10 changes, from first authoring to landing on main.",
}


def problems(plain):
    """Every violation as a string: a missing, empty, long, non-ASCII or identifier-like line."""
    out = []
    for i, t in sorted(plain.items()):
        if not isinstance(t, str) or not t.strip(): out.append(f"{i}: empty"); continue
        if len(t) > 140: out.append(f"{i}: {len(t)} chars (max 140)")
        if not t.isascii(): out.append(f"{i}: not ASCII")
        if "`" in t: out.append(f"{i}: backtick")
        if re.search(r"[A-Za-z0-9]_[A-Za-z0-9]", t): out.append(f"{i}: snake_case identifier")
        if "\n" in t: out.append(f"{i}: more than one line")
    return out


# Metrics the runner no longer measures (the attack suite and the gate self-tests are deleted): kept so the pages of recorded cards still read plainly.
RETIRED = {
    "honesty.gate_selftests": "Share of the project's checks that have a test proving the check can fail.",
    "honesty.gates_self_tested": "Share of the project's checks whose can-it-fail test actually ran in this measurement.",
    "honesty.selftests_ran_cases": "Whether the project's checks reported how many cases they ran, and ran at least one, with none skipped.",
    "honesty.attack_suite": "Whether an attempt to cheat the checks is caught, and a sabotaged run is correctly reported as failing.",
}
