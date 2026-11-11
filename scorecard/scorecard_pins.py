"""Vendored libraries for the sandboxed run (DECISIONS 21; the earlier design note D5 fetched them). The sandbox has no network, so a subject builds only from what its own tree holds: since vbm-land 0.10 a library carries
its dependencies in vendor/NAME, locked in .land/pins.lock (`NAME URL TAG REV TREE_SHA256`). `provision(wt)` runs HOST-SIDE, before any sandbox starts, and puts nothing into the subject's tree. It uses this scorer's OWN
trusted copy of land-pin (.land/tool/bin/land-pin, hash-checked by land-check) and its OWN signers file (.land/land.signers), never the subject's, and does two things:
  1. `land-pin verify` over the subject's tree: every vendored library is exactly its lock line (the tree hash), none is unlocked, and there is one copy of each library in the closure;
  2. for every lock line, the RELEASE itself: the URL must be an allowlisted GitHub repository, and `land-pin vendor` into a scratch directory must accept the tag (annotated, signed by a key in this scorer's signers file,
     its message recording the tree hash, the exported tree matching it) and give the SAME commit and tree hash as the lock: a library cannot ship a doctored copy of a dependency, even with a self-consistent lock.
Anything else is refused with a plain message: a subject still on the retired lock (scripts/pinned-libs.lock), or with a git package in its lake manifest, has a dependency this sandbox cannot build, and the run measures
nothing rather than build on bytes nobody checked. The lock and the manifest are the subject's (untrusted) data: parsed strictly, and they only ever name something to verify. Returns the provenance
(name, tag, rev, tree_sha256, url) the card records."""
import json, os, re, shutil, subprocess, tempfile
import scorecard_policy
HERE = os.path.dirname(os.path.abspath(__file__)); REPO = os.path.dirname(HERE)
LOCK, OLD_LOCK, MANIFEST = ".land/pins.lock", "scripts/pinned-libs.lock", "lake-manifest.json"
TOOL, SIGNERS = os.path.join(REPO, ".land", "tool", "bin", "land-pin"), os.path.join(REPO, ".land", "land.signers")

def parse_lock(text):
    out = []
    for n, raw in enumerate(text.splitlines(), 1):
        l = raw.split("#")[0].strip()
        if not l: continue
        f = l.split()
        if len(f) != 5: raise ValueError(f"{LOCK}:{n}: want 'NAME URL TAG REV TREE_SHA256' (5 fields)")
        name, url, tag, rev, h = f
        if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", name) or not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+", tag) or not re.fullmatch(r"[0-9a-f]{40}", rev) or not re.fullmatch(r"[0-9a-f]{64}", h):
            raise ValueError(f"{LOCK}:{n}: bad name, tag (vX.Y.Z), rev (40 hex) or tree hash (64 hex)")
        out.append({"name": name, "url": url, "tag": tag, "rev": rev, "hash": h})
    return out

def provision(wt, env, allowlist=scorecard_policy.ALLOWLIST, allow_local=False, signers=SIGNERS, tool=TOOL):
    """[] when the subject vendors nothing; else the provenance list. ValueError (plain message) on any refusal. allow_local: a local path or file:// URL is accepted (the test and a local fixture only)."""
    if os.path.exists(os.path.join(wt, OLD_LOCK)): raise ValueError(f"{OLD_LOCK} is the retired lock: vendor the dependency with land-pin (vbm-land docs/pin.md); the sandbox cannot fetch it")
    try: man = json.load(open(os.path.join(wt, MANIFEST)))["packages"] if os.path.isfile(os.path.join(wt, MANIFEST)) else []
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as e: raise ValueError(f"cannot read {MANIFEST}: {e}")
    for p in man:
        if p.get("type") == "git": raise ValueError(f"{str(p.get('name')).strip('«»')}: a git package ({p.get('url')}) in {MANIFEST}: vendor it with land-pin (vbm-land docs/pin.md); the sandbox cannot fetch it")
    lockf = os.path.join(wt, LOCK)
    lock = parse_lock(open(lockf).read()) if os.path.isfile(lockf) else []
    r = subprocess.run([tool, "verify"], capture_output=True, text=True, env=dict(env, LAND_PIN_ROOT=wt))
    if r.returncode: raise ValueError("the vendored libraries are not exactly their lock: " + " ".join(r.stderr.split("\n")[-4:]).strip())
    done = []
    for e in lock:
        url = e["url"]
        if not (allow_local and url.startswith(("/", "file://"))):
            m = scorecard_policy.GITHUB.match(url)
            if not url.startswith("https://") or not m or not os.path.isfile(allowlist) or f"{m.group(1)}/{m.group(2)}" not in scorecard_policy.tomllib.load(open(allowlist, "rb"))["repos"]:
                raise ValueError(f"{e['name']}: {url} is not an allowlisted GitHub repository: the release cannot be checked")
        scratch = tempfile.mkdtemp(prefix="pins.")
        try:
            os.makedirs(os.path.join(scratch, ".land")); shutil.copy(signers, os.path.join(scratch, ".land", "land.signers"))
            genv = dict(env, LAND_PIN_ROOT=scratch)
            if allow_local: genv.update(GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="protocol.file.allow", GIT_CONFIG_VALUE_0="always")
            r = subprocess.run([tool, "vendor", e["name"], url, e["tag"]], capture_output=True, text=True, env=genv, timeout=600)
            if r.returncode: raise ValueError(f"{e['name']}: the release {e['tag']} of {url} is not accepted: " + " ".join((r.stderr or r.stdout).strip().split("\n")[-2:]))
            got = [l.split() for l in open(os.path.join(scratch, LOCK)).read().splitlines() if l.split()[:1] == [e["name"]]]
            if not got or got[0][3] != e["rev"] or got[0][4] != e["hash"]:
                raise ValueError(f"{e['name']}: the vendored copy does not match the published release {e['tag']}: the release is at {got[0][3] if got else '?'} with tree hash {got[0][4] if got else '?'}; the lock says {e['rev']} and {e['hash']}")
        finally: shutil.rmtree(scratch, ignore_errors=True)
        done.append({"name": e["name"], "tag": e["tag"], "rev": e["rev"], "tree_sha256": e["hash"], "url": url})
    return done
