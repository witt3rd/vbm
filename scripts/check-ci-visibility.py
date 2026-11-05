#!/usr/bin/env python3
"""Tier 1 check (DECISIONS 16): a PUBLIC repo must not run a workflow job on a self-hosted runner (a stranger's pull request would run on our machine). Usage: check-ci-visibility.py [workflow-dir ...] (default .github/workflows)
A job is self-hosted when its `runs-on` mentions `self-hosted` or names no GitHub-hosted image (ubuntu, windows, macos). With no such job it passes without asking anything. Otherwise the repo's visibility is read with
`gh api repos/<owner>/<repo> --jq .private` ($GITHUB_REPOSITORY, else the origin URL; $SCORECARD_GH is the gh binary, for the self-test): public, or unknown (fail closed), fails. Exit 0 ok, 1 fails."""
import glob, json, os, re, subprocess, sys
try:
    import yaml
except ImportError:
    if os.environ.get("LINT_WORKFLOWS_REEXEC") != "1" and os.path.exists("/usr/bin/python3"):
        os.environ["LINT_WORKFLOWS_REEXEC"] = "1"; os.execv("/usr/bin/python3", ["/usr/bin/python3", *sys.argv])
    print("check-ci-visibility: PyYAML is missing", file=sys.stderr); sys.exit(2)


def self_hosted_jobs(files):
    out = []
    for f in files:
        jobs = (yaml.safe_load(open(f)) or {}).get("jobs") or {}
        for name, j in jobs.items():
            ro = json.dumps(j.get("runs-on", "")).lower() if isinstance(j, dict) else ""
            if "self-hosted" in ro or not re.search(r"ubuntu|windows|macos", ro): out.append(f"{f}: job {name}")
    return out


def repo_slug():
    s = os.environ.get("GITHUB_REPOSITORY", "")
    if not s:
        u = subprocess.run(["git", "remote", "get-url", "origin"], capture_output=True, text=True).stdout.strip()
        m = re.search(r"github[A-Za-z0-9.-]*[/:]([^/]+/[^/]+?)(?:\.git)?/?$", u); s = m.group(1) if m else ""
    return s


def main(args):
    files = []
    for a in args or [".github/workflows"]: files += sorted(glob.glob(os.path.join(a, "*.y*ml"))) if os.path.isdir(a) else [a]
    jobs = self_hosted_jobs(files)
    if not jobs: print("check-ci-visibility: no self-hosted job: ok"); return 0
    slug = repo_slug()
    r = subprocess.run([os.environ.get("SCORECARD_GH", "gh"), "api", f"repos/{slug}", "--jq", ".private"], capture_output=True, text=True) if slug else None
    private = r.stdout.strip() if r and r.returncode == 0 else None
    if private == "true": print(f"check-ci-visibility: {slug} is private: {len(jobs)} self-hosted job(s) allowed (DECISIONS 16)"); return 0
    why = "is PUBLIC" if private == "false" else "has a visibility that could not be read (failing closed)"
    print(f"check-ci-visibility: {slug or 'the repo'} {why} and runs on a self-hosted runner: {'; '.join(jobs)}. Flip Tier 1 back to GitHub-hosted runners first (DECISIONS 16).", file=sys.stderr); return 1


if __name__ == "__main__": sys.exit(main(sys.argv[1:]))
