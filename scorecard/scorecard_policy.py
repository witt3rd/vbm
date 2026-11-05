"""The registry allowlist, as the RUNNER enforces it (SPEC rule 10; registry-validate enforces the same file for entries). Until the Level 2 isolation exists only allowlisted repos are scored.
A repo whose origin is a remote URL must be a GitHub URL of an allowlisted <owner>/<repo>; a repo with a local-path origin or none is a local fixture, which only the operator of this machine can pass (the scoring job always clones the entry's URL)."""
import os, re, subprocess, tomllib

ALLOWLIST = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "registry", "allowlist.toml")
GITHUB = re.compile(r"^(?:https://|ssh://git@|git@)github[A-Za-z0-9.-]*[/:]([A-Za-z0-9][A-Za-z0-9._-]*)/([A-Za-z0-9][A-Za-z0-9._-]*?)(?:\.git)?/?$")
REFUSED = "not allowlisted: outside submissions wait for the Level 2 isolation (scorecard/SPEC.md, 'Level 2 isolation (the required design)')"


def check(repo, env, path=ALLOWLIST):
    """None when the repo may be scored, else the plain refusal message."""
    url = subprocess.run(["git", "-C", repo, "remote", "get-url", "origin"], capture_output=True, text=True, env=env).stdout.strip()
    if not url or url.startswith(("/", ".", "file://")): return None
    try: repos = tomllib.load(open(path, "rb"))["repos"]
    except (OSError, KeyError, tomllib.TOMLDecodeError): return f"the allowlist {path} is unreadable: refusing to score anything"
    m = GITHUB.match(url)
    return None if m and f"{m.group(1)}/{m.group(2)}" in repos else f"{url} is {REFUSED}"
