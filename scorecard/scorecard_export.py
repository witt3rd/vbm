"""Level 1 export INTAKE (scorecard/SPEC.md, "Level 1", step 2): a Lean declaration export (the lean4export NDJSON format, 3.x) is read as DATA and validated; nothing in it is ever executed or interpreted beyond its JSON.
`intake(raw)` returns an Export or raises ExportError (a hostile or malformed export is the candidate's bytes: the metric FAILS with the reason). Strict by design: at most MAX_BYTES / MAX_LINES / MAX_LINE; strict UTF-8; one JSON object per line,
no duplicate keys, no NaN; the first line a `meta` object with format 3.1.x; then names, levels, expressions and declarations, each object holding exactly its id key and ONE known tag; ids are DENSE and in order (names and levels from 1,
expressions from 0), so every reference points at something defined EARLIER and the structure is a DAG with no cycle; every type, value, name and level reference in a declaration is checked. The reader is iterative (an attacker's depth
costs nothing: depth is computed per node as it is defined and capped); `bounded()` adds a wall-clock alarm and an address-space limit around it."""
import contextlib, json, re, resource, signal

MAX_BYTES, MAX_LINES, MAX_LINE, MAX_DEPTH, MAX_STR, MAX_NAT_DIGITS = 64 << 20, 1_000_000, 1 << 20, 100_000, 4096, 10_000
FORMAT = re.compile(r"^3\.1\.\d{1,4}$")   # what the independent kernel accepts (nanoda: 3.1.0 up to, excluding, 3.2.0)
BINDER = {"default", "implicit", "strictImplicit", "instImplicit"}


class ExportError(ValueError): pass
class TimedOut(BaseException): pass


class Export:
    """names: id -> (prefix id, str | int); levels: id -> tuple; exprs: id -> tuple(tag, ...); decls: name string -> dict(kind, name_id, params, type, value, unsafe, safety)."""
    def __init__(self): self.meta, self.names, self.levels, self.exprs, self.depth, self.decls, self._s = {}, {0: None}, {0: ("zero",)}, {}, {}, {}, {0: ""}
    def name(self, i):   # the dotted string of a name id (iterative: prefix chains can be deep)
        chain = []
        while i not in self._s: chain.append(i); i = self.names[i][0]
        s = self._s[i]
        for j in reversed(chain): s = f"{s}.{self.names[j][1]}" if s else str(self.names[j][1]); self._s[j] = s
        return s


def _obj(pairs):
    d = {}
    for k, v in pairs:
        if k in d: raise ExportError(f"duplicate key {k!r}")
        d[k] = v
    return d


def _nat(v, what, hi=None):
    if isinstance(v, bool) or not isinstance(v, int) or v < 0 or (hi is not None and v > hi): raise ExportError(f"{what} must be a natural number" + (f" below {hi}" if hi is not None else ""))
    return v


def _need(o, keys, what):
    if not isinstance(o, dict) or set(o) != set(keys): raise ExportError(f"{what} must be an object with exactly the keys {sorted(keys)}")
    return o


def intake(raw, max_bytes=MAX_BYTES, max_lines=MAX_LINES, max_line=MAX_LINE):
    if len(raw) > max_bytes: raise ExportError(f"the export is {len(raw)} bytes, over the {max_bytes}-byte cap")
    try: text = raw.decode("utf-8")
    except UnicodeDecodeError as e: raise ExportError(f"the export is not UTF-8: {e}")
    lines = text.split("\n")
    if lines and lines[-1] == "": lines.pop()
    if not lines: raise ExportError("the export is empty")
    if len(lines) > max_lines: raise ExportError(f"the export has {len(lines)} lines, over the {max_lines}-line cap")
    X = Export(); nn, nl, ne = 1, 1, 0
    ok_name = lambda i: isinstance(i, int) and not isinstance(i, bool) and 0 <= i < nn
    ok_level = lambda i: isinstance(i, int) and not isinstance(i, bool) and 0 <= i < nl
    for n, line in enumerate(lines, 1):
        if len(line) > max_line: raise ExportError(f"line {n}: over the {max_line}-character cap")
        try: o = json.loads(line, object_pairs_hook=_obj, parse_constant=lambda c: (_ for _ in ()).throw(ExportError(f"{c} is not JSON")))
        except ExportError as e: raise ExportError(f"line {n}: {e}")
        except (ValueError, RecursionError) as e: raise ExportError(f"line {n}: not a JSON object per line ({str(e)[:80]})")
        if not isinstance(o, dict) or not o: raise ExportError(f"line {n}: not a JSON object")
        try:
            if n == 1:
                m = _need(o, ["meta"], "the first line")["meta"]
                if not isinstance(m, dict) or not isinstance(m.get("format"), dict) or not isinstance(m["format"].get("version"), str) or not FORMAT.match(m["format"]["version"]): raise ExportError("the first line must be a meta object with format version 3.1.x")
                X.meta = m; continue
            if "in" in o:   # a name
                k = _need(o, ["in", "str" if "str" in o else "num"], "a name")
                if _nat(o["in"], "name id") != nn: raise ExportError(f"name ids are dense and in order: expected {nn}, got {o['in']}")
                if "str" in o:
                    b = _need(o["str"], ["pre", "str"], "Name.str"); s = b["str"]
                    if not isinstance(s, str) or len(s) > MAX_STR: raise ExportError("a name component must be a string of at most 4096 characters")
                    if not ok_name(b["pre"]): raise ExportError("a name prefix is not an earlier name")
                    X.names[nn] = (b["pre"], s)
                else:
                    b = _need(o["num"], ["pre", "i"], "Name.num")
                    if not ok_name(b["pre"]): raise ExportError("a name prefix is not an earlier name")
                    X.names[nn] = (b["pre"], _nat(b["i"], "a numeric name component", 1 << 62))
                nn += 1
            elif "il" in o:   # a level
                tags = [t for t in o if t != "il"]
                if len(tags) != 1 or tags[0] not in ("succ", "max", "imax", "param"): raise ExportError("a level has exactly one of succ, max, imax, param")
                if _nat(o["il"], "level id") != nl: raise ExportError(f"level ids are dense and in order: expected {nl}, got {o['il']}")
                t = tags[0]; v = o[t]
                if t in ("succ", "param"):
                    if not (ok_level(v) if t == "succ" else ok_name(v)): raise ExportError(f"a level {t} does not point at an earlier {'level' if t == 'succ' else 'name'}")
                    X.levels[nl] = (t, v)
                else:
                    if not isinstance(v, list) or len(v) != 2 or not all(ok_level(x) for x in v): raise ExportError(f"a level {t} needs two earlier levels")
                    X.levels[nl] = (t, v[0], v[1])
                nl += 1
            elif "ie" in o:   # an expression
                tags = [t for t in o if t != "ie"]
                if len(tags) != 1 or tags[0] not in ("bvar", "sort", "const", "app", "lam", "forallE", "letE", "proj", "natVal", "strVal", "mdata"): raise ExportError("an expression has exactly one known tag")
                if _nat(o["ie"], "expression id") != ne: raise ExportError(f"expression ids are dense and in order: expected {ne}, got {o['ie']}")
                t = tags[0]; v = o[t]; ok_e = lambda i: isinstance(i, int) and not isinstance(i, bool) and 0 <= i < ne
                if t == "bvar": e, kids = ("bvar", _nat(v, "a bvar index", 1 << 40)), ()
                elif t == "sort":
                    if not ok_level(v): raise ExportError("a sort does not point at an earlier level")
                    e, kids = ("sort", v), ()
                elif t == "const":
                    b = _need(v, ["name", "us"], "Expr.const")
                    if not ok_name(b["name"]) or b["name"] == 0 or not isinstance(b["us"], list) or not all(ok_level(x) for x in b["us"]) or len(b["us"]) > 64: raise ExportError("a const needs an earlier name and at most 64 earlier levels")
                    e, kids = ("const", b["name"], tuple(b["us"])), ()
                elif t == "app":
                    b = _need(v, ["fn", "arg"], "Expr.app")
                    if not (ok_e(b["fn"]) and ok_e(b["arg"])): raise ExportError("an app does not point at earlier expressions")
                    e, kids = ("app", b["fn"], b["arg"]), (b["fn"], b["arg"])
                elif t in ("lam", "forallE"):
                    b = _need(v, ["name", "type", "body", "binderInfo"], f"Expr.{t}")
                    if not (ok_name(b["name"]) and ok_e(b["type"]) and ok_e(b["body"])) or b["binderInfo"] not in BINDER: raise ExportError(f"a {t} needs an earlier name, type and body, and a known binderInfo")
                    e, kids = (t, b["name"], b["type"], b["body"]), (b["type"], b["body"])
                elif t == "letE":
                    b = _need(v, ["name", "type", "value", "body", "nondep"], "Expr.letE")
                    if not (ok_name(b["name"]) and all(ok_e(b[k]) for k in ("type", "value", "body"))) or not isinstance(b["nondep"], bool): raise ExportError("a letE needs an earlier name, type, value and body")
                    e, kids = ("letE", b["name"], b["type"], b["value"], b["body"]), (b["type"], b["value"], b["body"])
                elif t == "proj":
                    b = _need(v, ["typeName", "idx", "struct"], "Expr.proj")
                    if not (ok_name(b["typeName"]) and ok_e(b["struct"])): raise ExportError("a proj needs an earlier type name and structure")
                    e, kids = ("proj", b["typeName"], _nat(b["idx"], "a proj index", 1 << 20), b["struct"]), (b["struct"],)
                elif t == "natVal":
                    if not isinstance(v, str) or not re.fullmatch(r"(0|[1-9][0-9]{0,%d})" % (MAX_NAT_DIGITS - 1), v): raise ExportError("a natVal is a decimal string of at most 10000 digits")
                    e, kids = ("natVal", v), ()
                elif t == "strVal":
                    if not isinstance(v, str): raise ExportError("a strVal must be a string")
                    e, kids = ("strVal", len(v)), ()
                else:
                    b = _need(v, ["expr", "data"], "Expr.mdata")
                    if not ok_e(b["expr"]) or not isinstance(b["data"], dict): raise ExportError("an mdata needs an earlier expression and an object")
                    e, kids = ("mdata", b["expr"]), (b["expr"],)
                d = 1 + max((X.depth[k] for k in kids), default=0)
                if d > MAX_DEPTH: raise ExportError(f"an expression is nested deeper than {MAX_DEPTH}")
                X.exprs[ne], X.depth[ne] = e, d; ne += 1
            else:   # a declaration (a group, for inductives)
                if len(o) != 1 or next(iter(o)) not in ("axiom", "def", "opaque", "thm", "quot", "inductive"): raise ExportError("a declaration object has exactly one of axiom, def, opaque, thm, quot, inductive")
                kind = next(iter(o)); v = o[kind]
                if kind == "inductive":
                    b = _need(v, ["types", "ctors", "recs"], "an inductive declaration")
                    parts = [("inductive", x) for x in b["types"] if True] + [("ctor", x) for x in b["ctors"]] + [("rec", x) for x in b["recs"]]
                    if not all(isinstance(x, list) for x in b.values()): raise ExportError("types, ctors and recs are lists")
                else: parts = [(kind, v)]
                for k, x in parts: _decl(X, k, x, nn, nl, ne)
        except ExportError as e: raise ExportError(f"line {n}: {e}")
    X.counts = {"names": nn - 1, "levels": nl - 1, "exprs": ne, "lines": len(lines)}
    return X


def _decl(X, kind, x, nn, nl, ne):
    if not isinstance(x, dict) or not isinstance(x.get("name"), int) or isinstance(x["name"], bool) or not 0 < x["name"] < nn: raise ExportError(f"a {kind} declaration needs an earlier name")
    for f in ("type", "value"):
        if f in x and (isinstance(x[f], bool) or not isinstance(x[f], int) or not 0 <= x[f] < ne): raise ExportError(f"a {kind} declaration's {f} is not an earlier expression")
    if "type" not in x: raise ExportError(f"a {kind} declaration needs a type")
    lp = x.get("levelParams", [])
    if not isinstance(lp, list) or len(lp) > 64 or not all(isinstance(i, int) and not isinstance(i, bool) and 0 < i < nn for i in lp): raise ExportError(f"a {kind} declaration's levelParams must be earlier names")
    if kind in ("def", "opaque", "thm") and "value" not in x: raise ExportError(f"a {kind} declaration needs a value")
    safety = x.get("safety", "safe")
    if safety not in ("safe", "unsafe", "partial") or not isinstance(x.get("isUnsafe", False), bool): raise ExportError("safety is safe, unsafe or partial; isUnsafe is a boolean")
    nm = X.name(x["name"])
    if nm in X.decls: raise ExportError(f"the declaration {nm} appears twice")
    X.decls[nm] = {"kind": kind, "name_id": x["name"], "params": lp, "type": x["type"], "value": x.get("value"), "unsafe": bool(x.get("isUnsafe", False)) or safety == "unsafe", "partial": safety == "partial"}


@contextlib.contextmanager
def bounded(seconds=120, memory=4 << 30):
    """A wall-clock alarm and an address-space limit around a read of hostile data (the limit is restored afterwards); exceeding either is an ExportError, never a hang or a host-wide OOM."""
    old = resource.getrlimit(resource.RLIMIT_AS)
    def h(*_): raise TimedOut()
    signal.signal(signal.SIGALRM, h); signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        resource.setrlimit(resource.RLIMIT_AS, (memory if old[1] == resource.RLIM_INFINITY else min(memory, old[1]), old[1]))
        yield
    except TimedOut: raise ExportError(f"reading the export took over {seconds} s: stopped")
    except MemoryError: raise ExportError(f"reading the export needed over {memory >> 20} MiB: stopped")
    finally: signal.setitimer(signal.ITIMER_REAL, 0); resource.setrlimit(resource.RLIMIT_AS, old)
