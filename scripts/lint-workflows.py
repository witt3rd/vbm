#!/usr/bin/env python3
"""Structural validity of .github/workflows/*.yml (Tier 1): the file parses, has a trigger and at least one job, every job has steps (or `uses`),
and every step has exactly one of `uses` / `run`, and `with:` only on a `uses` step (a step inserted between a `uses` and its `with` broke a workflow once:
zero jobs ran). Uses actionlint too when it is on PATH. Usage: lint-workflows.py [file|dir ...]  (default .github/workflows)"""
import glob, os, shutil, subprocess, sys
try:
    import yaml
except ImportError:  # setup-python's interpreter has no PyYAML; the system one does
    if os.environ.get("LINT_WORKFLOWS_REEXEC") != "1" and os.path.exists("/usr/bin/python3"):
        os.environ["LINT_WORKFLOWS_REEXEC"] = "1"; os.execv("/usr/bin/python3", ["/usr/bin/python3", *sys.argv])
    print("lint-workflows: PyYAML is missing (apt install python3-yaml)", file=sys.stderr); sys.exit(2)

def check(path):
    errs = []
    try:
        d = yaml.safe_load(open(path))
    except Exception as e:
        return [f"{path}: does not parse: {e}"]
    if not isinstance(d, dict):
        return [f"{path}: not a mapping"]
    if True not in d and "on" not in d:  # PyYAML reads the key `on` as True
        errs.append(f"{path}: no `on:` trigger")
    jobs = d.get("jobs")
    if not isinstance(jobs, dict) or not jobs:
        errs.append(f"{path}: no jobs (zero jobs would run)")
        return errs
    for jn, j in jobs.items():
        if not isinstance(j, dict):
            errs.append(f"{path}: job {jn} is not a mapping"); continue
        if "uses" in j:
            continue
        if "runs-on" not in j:
            errs.append(f"{path}: job {jn} has no runs-on")
        steps = j.get("steps")
        if not isinstance(steps, list) or not steps:
            errs.append(f"{path}: job {jn} has no steps"); continue
        for i, s in enumerate(steps):
            if not isinstance(s, dict):
                errs.append(f"{path}: job {jn} step {i} is not a mapping"); continue
            nm = s.get("name") or s.get("uses") or s.get("run") or "?"
            if ("uses" in s) == ("run" in s):
                errs.append(f"{path}: job {jn} step {i} ({str(nm)[:40]}) must have exactly one of uses/run")
            if "with" in s and "uses" not in s:
                errs.append(f"{path}: job {jn} step {i} ({str(nm)[:40]}) has `with:` but no `uses:`")
    return errs

def main(args):
    files = []
    for a in args or [".github/workflows"]:
        files += sorted(glob.glob(os.path.join(a, "*.y*ml"))) if os.path.isdir(a) else [a]
    if not files:
        print("lint-workflows: no workflow files found", file=sys.stderr); return 1
    errs = [e for f in files for e in check(f)]
    if not errs and shutil.which("actionlint") and subprocess.run(["actionlint", "-version"], capture_output=True).returncode == 0:
        r = subprocess.run(["actionlint", *files], capture_output=True, text=True)
        if r.returncode: errs.append("actionlint:\n" + r.stdout + r.stderr)
    for e in errs: print("lint-workflows:", e, file=sys.stderr)
    if not errs: print(f"lint-workflows: {len(files)} workflow file(s) ok")
    return 1 if errs else 0

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
