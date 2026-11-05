"""The Level 1 proof manifest (scorecard/SPEC.md, "Level 1: Certified"). A DATA file the candidate writes: no key holds a command. Every key is required, an unknown or mistyped key is rejected,
every path is relative without `..`. Executes nothing; `load(text)` returns the manifest or raises ManifestError.
  [export]   path, sha256 (the candidate's integrity check: the scorer computes its own hash and compares), lean_version (self-reported: shown, never judged)
  [claims]   theorems (the theorems that CARRY THE CLAIM), definitions (the definitions they are about); declaration names of the export
  [[artifact]] one table per shipped artifact: path, kind (wasm | object), allowed_symbols
  [binding]  generator, compiler: ids of entries of the trust ledger (the named trust of "the binding between the shipped artifact and the proved definitions")
  [source] globs  [proof] sorry_pattern, allow_marker  [trust] c_files, ledger, entry_regex  [tests] generated, extra, gate_selftests, entry_points, scenario_files  [velocity] window_hours
The sections source/proof/trust/tests/velocity are the same shapes as the adapter's, so the static metrics of the runner read them unchanged."""
import re, tomllib

NAME = re.compile(r"^[^\s\"'\\\x00-\x1f]{1,200}$")        # a declaration name of the export (Lean names are dotted; no whitespace, quote, backslash or control character)
ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,39}$")     # a trust-ledger entry id
KINDS = ("wasm", "object")
MAX_NAMES = 200
SCHEMA = {
    "export": {"path": str, "sha256": str, "lean_version": str},
    "claims": {"theorems": list, "definitions": list},
    "binding": {"generator": str, "compiler": str},
    "source": {"globs": list},
    "proof": {"sorry_pattern": str, "allow_marker": str},
    "trust": {"c_files": list, "ledger": str, "entry_regex": str},
    "tests": {"generated": list, "extra": list, "gate_selftests": list, "entry_points": list, "scenario_files": list},
    "velocity": {"window_hours": int},
}
ARTIFACT = {"path": str, "kind": str, "allowed_symbols": list}
PATH_KEYS = [("export", "path"), ("source", "globs"), ("trust", "c_files"), ("trust", "ledger"), ("tests", "generated"), ("tests", "extra"), ("tests", "gate_selftests"), ("tests", "scenario_files")]


class ManifestError(ValueError): pass


def _typed(v, t): return not isinstance(v, bool) and isinstance(v, t)


def _path(where, v):
    if v.startswith("/") or ".." in v.split("/") or "\0" in v or not v: raise ManifestError(f"manifest: {where}: an absolute, empty or '..' path is not allowed: {v!r}")


def load(text):
    try: d = tomllib.loads(text)
    except tomllib.TOMLDecodeError as e: raise ManifestError(f"manifest: not valid TOML: {e}")
    for sec, keys in SCHEMA.items():
        if not isinstance(d.get(sec), dict): raise ManifestError(f"manifest: missing section [{sec}]")
        for k, t in keys.items():
            if k not in d[sec]: raise ManifestError(f"manifest: missing key [{sec}] {k}")
            v = d[sec][k]
            if not _typed(v, t) or (t is list and not all(isinstance(x, str) for x in v)): raise ManifestError(f"manifest: [{sec}] {k} must be {'a list of strings' if t is list else t.__name__}")
        for k in d[sec]:
            if k not in keys: raise ManifestError(f"manifest: unknown key [{sec}] {k}")
    arts = d.get("artifact")
    if not isinstance(arts, list) or not arts or not all(isinstance(a, dict) for a in arts): raise ManifestError("manifest: at least one [[artifact]] table is required (Level 1 checks a SUBMITTED artifact)")
    for i, a in enumerate(arts):
        for k, t in ARTIFACT.items():
            if k not in a: raise ManifestError(f"manifest: missing key [[artifact]] #{i + 1} {k}")
            if not _typed(a[k], t) or (t is list and not all(isinstance(x, str) for x in a[k])): raise ManifestError(f"manifest: [[artifact]] #{i + 1} {k} must be {'a list of strings' if t is list else t.__name__}")
        for k in a:
            if k not in ARTIFACT: raise ManifestError(f"manifest: unknown key [[artifact]] #{i + 1} {k}")
        _path(f"[[artifact]] #{i + 1} path", a["path"])
        if a["kind"] not in KINDS: raise ManifestError(f"manifest: [[artifact]] #{i + 1} kind must be one of {KINDS}")
        if not all(re.fullmatch(r"[A-Za-z0-9_.$@]{1,200}", x) for x in a["allowed_symbols"]): raise ManifestError(f"manifest: [[artifact]] #{i + 1} allowed_symbols must be symbol names")
    for sec in d:
        if sec not in SCHEMA and sec != "artifact": raise ManifestError(f"manifest: unknown section [{sec}]")
    for sec, k in PATH_KEYS:
        for v in (d[sec][k] if isinstance(d[sec][k], list) else [d[sec][k]]): _path(f"[{sec}] {k}", v)
    if not re.fullmatch(r"[0-9a-f]{64}", d["export"]["sha256"]): raise ManifestError("manifest: [export] sha256 must be 64 lower-case hex digits")
    for k in ("theorems", "definitions"):
        names = d["claims"][k]
        if not 1 <= len(names) <= MAX_NAMES or len(set(names)) != len(names) or not all(NAME.match(n) for n in names): raise ManifestError(f"manifest: [claims] {k} must be 1..{MAX_NAMES} distinct declaration names")
    for k in ("generator", "compiler"):
        if not ID.match(d["binding"][k]): raise ManifestError(f"manifest: [binding] {k} must be a trust-ledger entry id (e.g. T3)")
    if d["binding"]["generator"] == d["binding"]["compiler"]: raise ManifestError("manifest: [binding] the generator and the compiler are two different ledger entries")
    for k in ("sorry_pattern", "entry_regex"):
        try: re.compile(d["proof"][k] if k == "sorry_pattern" else d["trust"][k])
        except re.error as e: raise ManifestError(f"manifest: {k} is not a valid regex: {e}")
    if not 1 <= d["velocity"]["window_hours"] <= 24 * 90: raise ManifestError("manifest: [velocity] window_hours must be 1..2160")
    if any(g.startswith(".git/") for g in d["source"]["globs"]): raise ManifestError("manifest: [source] globs may not name .git")
    return d
