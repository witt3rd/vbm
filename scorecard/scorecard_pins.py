"""Pinned libraries for the sandboxed run (design note D5). The sandbox has no network, so a subject with a pinned git dependency (a line in scripts/pinned-libs.lock, the format of vbm-llm and vbm-sse) cannot build in it
unless the pinned source is already in the subject's tree. `provision(wt)` runs HOST-SIDE, before any sandbox starts: for every lock line it fetches the package from the lake manifest's URL at the LOCK's full 40-hex rev
(never at the manifest's, never a branch), puts it at <wt>/.lake/packages/<name> and checks the checkout's HEAD and its spec_hash against the lock. The sandbox never fetches. Anything off (a manifest rev that is not the
lock's, a URL that is not an allowlisted GitHub repo, a HEAD or a hash that differs) is refused with a plain message: the run measures nothing rather than build on bytes nobody pinned. The lock and the manifest are the
subject's (untrusted) data: they are parsed strictly and only ever name something to fetch. Returns the provenance (name, rev, spec_hash, url) the card records."""
import hashlib, json, os, re, shutil, subprocess, tempfile
import scorecard_policy
LOCK, MANIFEST = "scripts/pinned-libs.lock", "lake-manifest.json"

def parse_lock(text):
    out = []
    for n, raw in enumerate(text.splitlines(), 1):
        l = raw.split("#")[0].strip()
        if not l: continue
        f = l.split()
        if len(f) != 5: raise ValueError(f"{LOCK}:{n}: want 'NAME REV SPEC_HASH ROOT SPEC_PATHS' (5 fields)")
        name, rev, h, root, paths = f
        if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", name) or not re.fullmatch(r"[0-9a-f]{40}", rev) or not re.fullmatch(r"[0-9a-f]{64}", h): raise ValueError(f"{LOCK}:{n}: bad name, rev (40 hex) or spec_hash (64 hex)")
        ps = paths.split(",")
        if any(not p or p.startswith("/") or ".." in p.split("/") for p in ps): raise ValueError(f"{LOCK}:{n}: unsafe spec path")
        out.append({"name": name, "rev": rev, "hash": h, "paths": ps})
    return out

def spec_hash(pkg, paths):
    """sha256 of the sorted '<sha256 of file> <path>' lines over every regular file under the paths (a trailing / is a directory; .git never counts): the hash scripts/pinned-lib.py of the subject computes."""
    files = []
    for p in paths:
        full = os.path.join(pkg, p)
        if p.endswith("/"):
            if not os.path.isdir(full): raise ValueError(f"spec directory {p} is missing")
            for d, dirs, fs in os.walk(full):
                dirs[:] = sorted(x for x in dirs if x != ".git")
                for x in fs:
                    q = os.path.join(d, x)
                    if os.path.islink(q) or not os.path.isfile(q): raise ValueError(f"{os.path.relpath(q, pkg)} is not a regular file")
                    files.append(os.path.relpath(q, pkg))
        elif os.path.isfile(full) and not os.path.islink(full): files.append(p)
        else: raise ValueError(f"spec file {p} is missing or not a regular file")
    lines = sorted({f"{hashlib.sha256(open(os.path.join(pkg, f), 'rb').read()).hexdigest()} {f}\n" for f in files}, key=lambda s: s.encode())
    return hashlib.sha256("".join(lines).encode()).hexdigest()

def provision(wt, env, allowlist=scorecard_policy.ALLOWLIST, allow_local=False):
    """[] when the subject pins nothing; else the provenance list. ValueError (plain message) on any refusal. allow_local: a local path or file:// URL is accepted (the test and a local fixture only)."""
    lockf = os.path.join(wt, LOCK)
    try:
        man = json.load(open(os.path.join(wt, MANIFEST)))["packages"] if os.path.isfile(os.path.join(wt, MANIFEST)) else []
        pk = {str(p.get("name")).strip("«»"): p for p in man}
        if os.path.isfile(lockf): lock = parse_lock(open(lockf).read())
        else:   # no lock file (deleted with the approvals): the manifest's own full-sha git packages are what is fetched, once, host-side
            lock = [{"name": n, "rev": p["rev"], "hash": None, "paths": None} for n, p in pk.items() if p.get("type") == "git" and re.fullmatch(r"[0-9a-f]{40}", str(p.get("rev")))]
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as e: raise ValueError(f"cannot read the pin files: {e}")
    if not lock: return []
    done = []
    for e in lock:
        p = pk.get(e["name"])
        if p is None or p.get("type") != "git" or not p.get("url"): raise ValueError(f"{e['name']}: not a git package of {MANIFEST}")
        if p.get("rev") != e["rev"]: raise ValueError(f"{e['name']}: stale rev: the manifest has {p.get('rev')}, the lock {e['rev']}")
        url = p["url"]
        if not (allow_local and (url.startswith(("/", "file://")))):
            m = scorecard_policy.GITHUB.match(url)
            if not url.startswith("https://") or not m or not os.path.isfile(allowlist) or f"{m.group(1)}/{m.group(2)}" not in scorecard_policy.tomllib.load(open(allowlist, "rb"))["repos"]: raise ValueError(f"{e['name']}: {url} is not an allowlisted https GitHub repository")
        dest = os.path.join(wt, ".lake", "packages", e["name"])
        if os.path.exists(dest): raise ValueError(f"{e['name']}: {dest} is already in the subject tree: refusing to build on a checkout nobody fetched")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        g = ["git", "-c", "core.fsmonitor=false", "-c", "core.hooksPath=/dev/null", "-c", "protocol.file.allow=" + ("always" if allow_local else "never")]
        steps = [g + ["clone", "-q", "--no-checkout", "--", url, dest], g + ["-C", dest, "checkout", "-q", "--detach", e["rev"]]]
        for argv in steps:
            r = subprocess.run(argv, capture_output=True, text=True, env=env)
            if r.returncode: shutil.rmtree(dest, ignore_errors=True); raise ValueError(f"{e['name']}: {' '.join(argv[len(g):len(g) + 2])} failed: {r.stderr.strip().splitlines()[-1:] or r.returncode}")
        head = subprocess.run(g + ["-C", dest, "rev-parse", "HEAD"], capture_output=True, text=True, env=env).stdout.strip()
        try: got = spec_hash(dest, e["paths"]) if e["hash"] else None
        except ValueError as x: shutil.rmtree(dest, ignore_errors=True); raise ValueError(f"{e['name']}: {x}")
        if head != e["rev"] or (e["hash"] and got != e["hash"]): shutil.rmtree(dest, ignore_errors=True); raise ValueError(f"{e['name']}: the fetched checkout is at {head} with spec_hash {got}; the lock says {e['rev']} and {e['hash']}")
        done.append({"name": e["name"], "rev": e["rev"], "spec_hash": e["hash"], "url": url})
    return done
