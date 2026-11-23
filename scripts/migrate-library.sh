#!/usr/bin/env bash
# migrate-library.sh NAME [--push]   (on a build host; docs/migrating-a-library.md)
# Moves the library repository witt3rd/NAME into lib/NAME/ of the family repository with its whole history, adapts it, runs every gate, re-creates its signed tags, and (with --push) pushes a fast-forward. Without --push it stops after the verification and pushes nothing.
# For a library that uses the standard gate template and vendors no other family library; anything else is refused at the precondition, to be done by hand.
set -euo pipefail
export PATH=$HOME/.local/share/mise/shims:$PATH
N=${1:?usage: migrate-library.sh NAME [--push]}; PUSH=0; [ "${2:-}" = "--push" ] && PUSH=1
KEY=${LAND_SIGNING_KEY:-$HOME/.ssh/vbm-land-signing}; ID=witt3rd@witt3rd.com; ID_NAME=${ID_NAME:?set ID_NAME to the name the project commits under}
W=/var/tmp/mig-$N; say() { echo "[$(date +%T)] $N: $*"; }; die() { echo "[$(date +%T)] $N: STOPPED: $*" >&2; exit 1; }
rm -rf "$W"; mkdir -p "$W"; cd "$W"
say "0. preconditions"
git clone -q "git@github.com:witt3rd/$N.git" scratch; cd scratch; git checkout -q main; git fetch -q --tags
others=$(git branch -r | grep -v -E 'origin/(HEAD|main)$' | sed 's#^ *origin/##' || true)
for b in ${REVIEWED_BRANCHES:-}; do others=$(echo "$others" | grep -v -x "$b" || true); done   # a branch the owner has reviewed and decided to leave (it stays in the archived repository)
[ -z "$others" ] || die "other branches need review first: $others"
git log --all --format='%ae%n%ce' | sort -u > ../emails; grep -q loamis ../emails && die "a commit carries the other organisation's address"
say "   addresses in the history: $(tr '\n' ' ' < ../emails)"
DEPS=$(git show main:.land/pins.lock 2>/dev/null | awk '$1 ~ /^vbm-/ {print $1}' | sort -u | tr '\n' ' ' || true)
say "   family dependencies: ${DEPS:-none}"
CMD=$(git show main:.land/land.conf | sed -n 's/^LAND_TEST_CMD=//p' | head -1); GATE=${CMD##* }
[ -n "$CMD" ] && [ -f "$GATE" ] && [ -f VERSION ] || die "no usable gate: LAND_TEST_CMD='$CMD' (the script it names must exist) and VERSION"
LEAN=0; [ -f .land/lean.conf ] && LEAN=1
say "   gate: $CMD (Lean gates: $LEAN)"
for t in $(git tag); do
  [ "$(git cat-file -t "$t")" = tag ] || die "tag $t is not annotated"; git merge-base --is-ancestor "$t^{commit}" main || die "tag $t is not an ancestor of main"
  ts=$(git cat-file tag "$t" | sed -n 's/^tree_sha256=//p' | head -1); [ -z "$ts" ] || say "   tag $t records tree_sha256 ${ts:0:12} (the git tree hash is checked after the move)"
done
git rev-list main > ../commits.old; git log main --format='%at|%s' > ../meta.old
say "1. re-root every commit under lib/$N/"
git filter-branch -f --index-filter 'git ls-files -s | sed "s|\t\"*|&lib/'"$N"'/|" | GIT_INDEX_FILE="$GIT_INDEX_FILE.new" git update-index --index-info && { [ ! -f "$GIT_INDEX_FILE.new" ] || mv "$GIT_INDEX_FILE.new" "$GIT_INDEX_FILE"; }' -- main >/dev/null 2>&1 || die "the re-root failed"
git rev-list main > ../commits.new; git log main --format='%at|%s' > ../meta.new
[ "$(wc -l < ../commits.old)" = "$(wc -l < ../commits.new)" ] || die "the commit count changed"; cmp -s ../meta.old ../meta.new || die "dates or subjects changed"
paste -d' ' ../commits.old ../commits.new > ../commit-map
# every tag: tree of lib/NAME at the migrated commit == the old tree (taken from the ORIGINAL clone's objects)
git clone -q "git@github.com:witt3rd/$N.git" ../orig
for t in $(git -C ../orig tag); do oc=$(git -C ../orig rev-parse "$t^{commit}"); nc=$(awk -v o="$oc" '$1==o{print $2}' ../commit-map); [ -n "$nc" ] || die "no mapping for $t"; [ "$(git rev-parse "$nc:lib/$N")" = "$(git -C ../orig rev-parse "$t^{tree}")" ] || die "the tree at $t changed by the move"; done
say "   verified: same commits, dates, subjects; every tag's tree is identical"
say "2. merge into the family repository"
cd "$W"; git clone -q git@github.com:witt3rd/vbm.git hub; cd hub; git config user.name "$ID_NAME"; git config user.email "$ID"
tip=$(git rev-parse origin/main)
git fetch -q ../scratch main:refs/heads/migrate/$N
git merge -q --allow-unrelated-histories --no-ff -m "chore($N): migrate the library, with its history, into lib/$N" migrate/$N
[ "$(git rev-parse HEAD^1)" = "$tip" ] || die "the first parent is not the family main"
[ -z "$(git diff --name-only "$tip" HEAD | grep -v "^lib/$N/" || true)" ] || die "the merge touches paths outside lib/$N"
say "3. the adaptation"
export N CMD GATE LEAN DEPS ID_NAME SCRUB SCRUB_PRODUCT SCRUB_MACHINES; python3 - <<'PY'
import os, re, json, shutil, subprocess, sys, tomllib
N = os.environ["N"]; DEPS = os.environ.get("DEPS", "").split(); L = f"lib/{N}"; CMD = os.environ["CMD"]; GATE = os.environ["GATE"]; LEAN = os.environ["LEAN"] == "1"
def sh(*a): return subprocess.run(a, capture_output=True, text=True)
# registry entry (kept only to read what to carry into the card)
rp = f"registry/witt3rd__{N}.toml"
if not os.path.isfile(rp): sys.exit(f"STOP: no registry entry {rp}")
reg = tomllib.load(open(rp, "rb"))
lic = open(f"{L}/LICENSE").read(400)
if "Apache License" not in lic: sys.exit("STOP: the license is not Apache-2.0: write the card by hand")
# 1. delete what the library needed only for being a repository
keep_lean = open(f"{L}/.land/lean.conf").read() if LEAN else None
gl = open(f"{L}/.gitleaks.toml").read() if os.path.isfile(f"{L}/.gitleaks.toml") else ""
for p in (".github", ".githooks", ".gitleaks.toml", ".agents", "CONTRIBUTING.md", "SECURITY.md", "CODEOWNERS", ".land", "scripts/lint-public", "scripts/test_lint_public.sh", "scripts/public-banned-hashes.txt"):
    full = f"{L}/{p}"
    if os.path.isdir(full): shutil.rmtree(full)
    elif os.path.isfile(full): os.remove(full)
if LEAN:
    os.makedirs(f"{L}/.land", exist_ok=True); open(f"{L}/.land/lean.conf", "w").write(keep_lean)
# 1b. family dependencies: the vendored copy goes, the package file and the build scripts name the sibling library instead
for d in DEPS:
    if not os.path.isdir(f"lib/{d}"): sys.exit(f"STOP: lib/{d} is not in the family repository yet: migrate it first")
    if os.path.isdir(f"{L}/vendor/{d}"): shutil.rmtree(f"{L}/vendor/{d}")
    targets = [f"{L}/lakefile.lean", f"{L}/lake-manifest.json"]
    for sub in ("scripts", "tests"):
        for root, _, fs in os.walk(f"{L}/{sub}"):
            for f in fs:
                fp = os.path.join(root, f)
                try: open(fp).read(); targets.append(fp)
                except (UnicodeDecodeError, OSError): pass
    for fp in targets:
        if os.path.isfile(fp):
            t = open(fp).read()
            t2 = t.replace(f"vendor/{d}", f"../{d}").replace(f'"vendor" / "{d}"', f'".." / "{d}"')   # the path as text, and as the components a lakefile joins
            if t2 != t: open(fp, "w").write(t2)
if DEPS and os.path.isdir(f"{L}/vendor") and not os.listdir(f"{L}/vendor"): os.rmdir(f"{L}/vendor")
# 2. the lander's Lean package, at the same relative place in lib/NAME and vendor/NAME
for f, old, new in ((f"{L}/lakefile.lean", 'from ".land/tool/lean"', 'from "../../.land/tool/lean"'), (f"{L}/lake-manifest.json", '"dir": ".land/tool/lean"', '"dir": "../../.land/tool/lean"')):
    if os.path.isfile(f):
        s = open(f).read(); open(f, "w").write(s.replace(old, new))
# 3. the library's gate and tests in the new location
p = f"{L}/{GATE}"; s = open(p).read()
s = s.replace(".land/tool/bin/", "../../.land/tool/bin/").replace(".land/tool/lib/", "../../.land/tool/lib/").replace(".land/tool/docs/", "../../.land/tool/docs/")
s = re.sub(r"^(\.\./\.\./\.land/tool/bin/land-lean )", r'LAND_LEAN_ROOT="$PWD" \1', s, flags=re.M)
s = re.sub(r"^(bg \S+ )(\.\./\.\./\.land/tool/bin/land-lean )", r'\1env LAND_LEAN_ROOT="$PWD" \2', s, flags=re.M)
lines = []
for l in s.split("\n"):
    if re.match(r"^\.\./\.\./\.land/tool/bin/(land-pin verify|land-check|land-secrets)", l): continue
    if re.match(r"^par scripts/test_lint_public\.sh\s*$", l): continue
    lines.append(l)
s = "\n".join(lines)
# a library whose only test was the lint it no longer carries has no test scripts left: the declaration loops and the runner job go with them
if "tests=()" in s and not re.search(r"^par \S", s, flags=re.M) and not [f for f in (os.listdir(f"{L}/scripts") if os.path.isdir(f"{L}/scripts") else []) if f.startswith("test_") and f.endswith(".sh")]:
    s = "\n".join(l for l in s.split("\n") if not (l.startswith("for f in scripts/test_*.sh") or l.startswith('for f in "${tests[@]}"') or l.startswith("bg tests ")))
if "run-tests-parallel" in s:
    s = re.sub(r'(run-tests-parallel )"\$\{tests\[@\]\}"', r'\1"${tests[@]/#/$PWD/}"', s)
# a literal list of test scripts on a run-tests-parallel line: the runner works from the git root, so each gets an absolute path
s = "\n".join(re.sub(r"(?<![\w/$.])(scripts/[\w./-]+)", r"$PWD/\1", l) if ("run-tests-parallel" in l and "${tests" not in l and not l.lstrip().startswith("#")) else l for l in s.split("\n"))
open(p, "w").write(s)
for f in (os.listdir(f"{L}/scripts") if os.path.isdir(f"{L}/scripts") else []):   # every script, not only test_*: a selftest or a gate helper sources the same library
    fp = f"{L}/scripts/{f}"
    if f.endswith(".sh") and os.path.isfile(fp):
        t = open(fp).read(); open(fp, "w").write(t.replace(". .land/tool/lib/ran.sh", ". ../../.land/tool/lib/ran.sh"))
for sub in ("scripts", "tests"):   # every script and test of the library: the vendored lander is two levels up from the library directory
    for root, _, fs in os.walk(f"{L}/{sub}"):
        for f in fs:
            fp = os.path.join(root, f)
            try: t = open(fp).read()
            except (UnicodeDecodeError, OSError): continue
            t2 = re.sub(r"(?<![./])\.land/tool/", "../../.land/tool/", t)
            t2 = re.sub(r"(\$\{?PWD\}?)/\.land/tool/", r"\1/../../.land/tool/", t2)   # a path built from the library directory
            if t2 != t: open(fp, "w").write(t2)
if os.environ.get("SCRUB") == "1":   # opt-in. The words come from the environment (SCRUB_PRODUCT, SCRUB_MACHINES): this script is public and cannot spell the names it removes
    prod = os.environ.get("SCRUB_PRODUCT", ""); mach = os.environ.get("SCRUB_MACHINES", "").split()
    if not prod: sys.exit("STOP: SCRUB=1 needs SCRUB_PRODUCT (the word to remove) in the environment")
    P = re.escape(prod); C = re.escape(prod.capitalize()); U = re.escape(prod.upper())
    subs = [(rf"\b{C}Spec\b", "HostSpec"), (rf"\b{C}\.", "Host."), (rf"impl/{C}/", "impl/Host/"), (rf"\b{U}_([A-Z_]+)", r"HOST_\1"), (rf"\b{P}'s\b", "the host's"), (rf"\b{C}'s\b", "The host's"), (rf"\b{C}\b", "The host"), (rf"\b{P}\b", "the host")] + [(rf"\b{re.escape(m)}\b", "a build host") for m in mach]
    changed = 0
    for root, dirs, fs in os.walk(L):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in fs:
            fp = os.path.join(root, f)
            try: t = open(fp).read()
            except (UnicodeDecodeError, OSError): continue
            t2 = t
            for a_, b_ in subs: t2 = re.sub(a_, b_, t2)
            t2 = re.sub(r"\b([Tt])he the host", r"\1he host", t2)
            if t2 != t: open(fp, "w").write(t2); changed += 1
    print(f"scrubbed the named words from {changed} files", file=sys.stderr)
tl0 = f"{L}/docs/trust-ledger.md"   # a family dependency is now an in-repo sibling, proved by its own area and part of every dependent's area: the "pinned, trusted by hash" entry for it is retired
if DEPS and os.path.isfile(tl0):
    t = open(tl0).read(); parts = re.split(r"(?m)^(?=### )", t); keep = []
    for blk in parts:
        if any(f"`pin:{d}`" in blk for d in DEPS): print(f"retired the trust-ledger entry for the vendored dependency: {blk.splitlines()[0]}", file=sys.stderr); continue
        keep.append(blk)
    open(tl0, "w").write("".join(keep))
tl = f"{L}/docs/trust-ledger.md"   # the trust ledger CITES files, and the gate checks that each exists relative to the library: the lander's are two levels up
if os.path.isfile(tl):
    t = open(tl).read(); t2 = re.sub(r"(?<![./])\.land/tool/", "../../.land/tool/", t)
    if t2 != t: open(tl, "w").write(t2)
resid = sh("grep", "-rnE", r"(^|[^./])\.land/tool|lint-public|\.gitleaks|vendor/vbm-", *[x for x in (f"{L}/scripts", f"{L}/tests", f"{L}/lakefile.lean") if os.path.exists(x)]).stdout.strip()
def is_code(l):
    m = re.match(r"^[^:]+:\d+:(.*)$", l)
    body = m.group(1).split("#")[0] if m else l   # what is before a comment marker
    return bool(re.search(r"(^|[^./])\.land/tool|lint-public|\.gitleaks|vendor/vbm-", body))
code = [l for l in resid.split("\n") if l and is_code(l)]
if resid: print("residual references (comments are fine):\n" + resid, file=sys.stderr)
if code: sys.exit("STOP: a code line still refers to the old layout:\n" + "\n".join(code))
# 4. the library's allowlist moves into the hub's secret-gate configuration (anchored paths only)
if gl.strip():
    blocks = re.findall(r"\[\[allowlists\]\].*?(?=\n\[\[|\Z)", gl, flags=re.S)
    add = ""
    for b in blocks:
        m = re.search(r"paths\s*=\s*\[(.*?)\]", b, flags=re.S)
        if not m: sys.exit("STOP: an allowlist without paths in .gitleaks.toml: merge by hand")
        ps = re.findall(r"'([^']*)'", m.group(1)) + re.findall(r'"([^"]*)"', m.group(1))
        if not all(x.startswith("^") for x in ps): sys.exit("STOP: an unanchored allowlist path: merge by hand")
        b2 = re.sub(r"paths\s*=\s*\[(.*?)\]", lambda _: "paths = [" + ", ".join("'^" + f"lib/{N}/" + x[1:] + "'" for x in ps) + "]", b, flags=re.S)
        add += "\n" + b2.strip() + "\n"
    if add: open(".gitleaks.toml", "a").write(add)
# 5. the library declares its dependencies (none) and its area; the card; the registry
open(f"{L}/deps", "w").write("".join(d + "\n" for d in sorted(DEPS)))
json.dump({"version": 1, "areas": [{"name": N, "paths": ["*"], "steps": [{"run": CMD}]}]}, open(f"{L}/areas.json", "w"), indent=2); open(f"{L}/areas.json", "a").write("\n")
what = reg["what"].strip(); what = what if what.endswith(".") else what + "."
open(f"{L}/card.toml", "w").write(f'name = "{N}"\nscope = "{what}"\nkind = "{reg["kind"]}"\nstatus = "{reg["status"]}"\nlicense = "Apache-2.0"\nconsumers = []\n\n[links]\ndocs = "{L}/docs"\n' if os.path.isdir(f"{L}/docs") else f'name = "{N}"\nscope = "{what}"\nkind = "{reg["kind"]}"\nstatus = "{reg["status"]}"\nlicense = "Apache-2.0"\nconsumers = []\n')
os.remove(rp)
a = open("registry/allowlist.toml").read(); a2 = a.replace(f'"witt3rd/{N}", ', "").replace(f', "witt3rd/{N}"', ""); open("registry/allowlist.toml", "w").write(a2)
print("adapted", N)
PY
scorecard/registry-table --write README.md; scripts/hub-areas --write
DEPNOTE=(); [ -z "$DEPS" ] || DEPNOTE=(-m "The vendored family dependencies ($DEPS) are in-repo siblings now (the package file requires ../<dep>): their proofs are checked by their own areas, their paths are in this library's area, and the trust-ledger entry that called each a pinned library trusted by hash is retired.")
git add -A; git commit -q -m "chore($N): adapt the library to the family layout

The library directory is self-contained and builds on its own: the lander's Lean package is required by the relative path ../../.land/tool/lean, its Lean gates take the library directory as their root, its test runner gets absolute paths. Removed, because the family repository has each once: the vendored lander and its skills, CI and hook files, the contributor and security pages, the secret-gate configuration (its reviewed allowlist moves into the hub's), and the copy of the public lint. The library declares its area (areas.json) and its dependencies (deps: none) and describes itself with a card (unscored); its registry and allowlist entries are retired and the README table lists it from its card." "${DEPNOTE[@]}" -m "Task-ID: hub-migrate-$N" -m "Protected: .land/areas.json, .gitleaks.toml and registry/allowlist.toml are gate-defining; the owner asked for the migration of every library (2026-11-22)"
say "4. the gates (the library's, then the family repository's)"
run_lib_gate() { ( cd "lib/$N" && timeout 3000 bash -c "$CMD" ) > ../lib-tier1.log 2>&1; }
if ! run_lib_gate; then
  # a dependent library: the dependency is in-repo now, so its trusted modules need a ledger entry of their own (the old entry called it a pinned library). ONE repair, from the checker's own key lines; anything else fails.
  if [ -n "$DEPS" ] && grep -q "^trust ledger: not in the trust ledger: module:" ../lib-tier1.log; then
    sed -n 's/^trust ledger: not in the trust ledger: //p' ../lib-tier1.log | sort -u > ../missing-keys
    export N DEPS; python3 - <<'PY2'
import os, re
N = os.environ["N"]; deps = os.environ["DEPS"].split(); keys = [l.strip() for l in open("../missing-keys") if l.strip()]
p = f"lib/{N}/docs/trust-ledger.md"; t = open(p).read()
n = max([int(x) for x in re.findall(r"(?m)^### T(\d+)\.", t)] or [0]) + 1
dl = ", ".join(deps)
entry = f"""
### T{n}. The in-repo dependency {dl}: the modules this library reaches outside its proofs
- **What:** the family library {dl} (`lib/<dependency>` of this repository, required by the relative path `../<dependency>` in `lakefile.lean`): the dependency's modules named below are the code of it that this library's compiled closure reaches outside the proofs (its shims, models and specifications, as the gate classifies them).
- **Enters:** `lakefile.lean` (the `require`); the modules on the Covers line.
- **Assumes:** the dependency's own specification, trust ledger and gates (`docs/trust-ledger.md` of the dependency): its proofs are checked by its own area, and every change to it also runs this library's area (its paths are in it). This entry adds no assumption of its own.
- **Test:** `scripts/tier1.sh` (the import scan: only the intended modules import the dependency, and never its proofs) and the dependency's own gate, run from its directory.
- **Owner:** the owner.
- **Plan:** verify, because the dependency's shims and models are verified by its own proofs and tests; this entry only records that this library's closure reaches them.
- **Covers:** {" ".join("`" + k + "`" for k in keys)}
"""
open(p, "w").write(t.rstrip("\n") + "\n" + entry)
print("trust ledger: added T%d covering %d module keys of the in-repo dependency" % (n, len(keys)))
PY2
    git add -A; git commit -q --amend --no-edit; say "   repaired the dependency's ledger entry ($(wc -l < ../missing-keys) module keys); re-running the library gate once"
    run_lib_gate || { tail -15 ../lib-tier1.log >&2; die "the library's gate still fails after the ledger repair (log $W/lib-tier1.log)"; }
  else tail -15 ../lib-tier1.log >&2; die "the library's gate fails in the hub layout (log $W/lib-tier1.log)"; fi
fi
say "   library gate: ok ($(grep -c . ../lib-tier1.log) lines)"
( timeout 3000 mise exec -- scripts/tier1.sh && timeout 900 mise exec -- scripts/repo-gates.sh ) > ../hub-tier1.log 2>&1 && say "   family gate and repo-gates: ok" || { tail -15 ../hub-tier1.log >&2; die "the family repository's gate fails (log $W/hub-tier1.log)"; }
.land/tool/bin/land-areas validate; [ "$(git ls-files | .land/tool/bin/land-areas unmapped | tail -1)" = "unmapped paths: 1" ] || die "unexpected unmapped paths"
[ "$(printf 'M\tlib/%s/VERSION\n' "$N" | .land/tool/bin/land-areas touched | python3 -c 'import sys,json; print(",".join(json.load(sys.stdin)["areas"]))')" = "$N" ] || die "a change inside the library does not select only its area"
say "   areas: sound (a change in lib/$N selects only $N)"
say "5. the signed tags"
for t in $(git -C ../orig tag); do
  oc=$(git -C ../orig rev-parse "$t^{commit}"); nc=$(awk -v o="$oc" '$1==o{print $2}' ../commit-map)
  git -C ../orig cat-file tag "$t" > "../tag.$t.raw"; sed '1,/^$/d' "../tag.$t.raw" | sed '/^-----BEGIN SSH SIGNATURE-----$/,$d' > "../tag.$t.body"
  tn=$(sed -n 's/^tagger \(.*\) <.*$/\1/p' "../tag.$t.raw"); te=$(sed -n 's/^tagger .* <\(.*\)> .*$/\1/p' "../tag.$t.raw"); td=$(sed -n 's/^tagger .*> \([0-9]* [+-][0-9]*\)$/\1/p' "../tag.$t.raw")
  GIT_COMMITTER_NAME="$tn" GIT_COMMITTER_EMAIL="$te" GIT_COMMITTER_DATE="$td" git -c gpg.format=ssh -c user.signingkey="$KEY" tag -s -F "../tag.$t.body" "$N/$t" "$nc"
  git -c gpg.format=ssh -c gpg.ssh.allowedSignersFile=.land/land.signers verify-tag "$N/$t" 2>&1 | head -1
  [ "$(git rev-parse "$N/$t^{tree}")" = "$(git rev-parse "$nc^{tree}")" ] || die "tag tree"
  [ "$(sed -n 's/^tree_sha256=//p' "../tag.$t.body" | head -1)" = "$(git cat-file tag "$N/$t" | sed -n 's/^tree_sha256=//p' | head -1)" ] || die "tree_sha256 differs for $t"
  say "   $N/$t on ${nc:0:9}: signed, same tree_sha256, ancestor of HEAD: $(git merge-base --is-ancestor "$N/$t^{commit}" HEAD && echo yes || echo NO)"
done
say "6. verified. new hub tip $(git rev-parse --short HEAD) (first parent ${tip:0:9})"
[ "$PUSH" = 1 ] || { say "DRY RUN: nothing pushed"; exit 0; }
[ "$(git ls-remote origin refs/heads/main | cut -f1)" = "$tip" ] || die "the family main moved: nothing pushed"
git push -q origin HEAD:main && say "pushed main (fast-forward)"
for t in $(git -C ../orig tag); do git push -q origin "refs/tags/$N/$t"; say "pushed tag $N/$t"; done
say "DONE"
