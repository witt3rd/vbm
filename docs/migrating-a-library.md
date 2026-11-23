# Migrating a library into the family repository: the playbook

Status: verified once, on `vbm-rng` (2026-11-22). It is the practical companion of the contract (`vbm-land` `docs/family-repo.md`, section 6): the contract says WHAT must hold; this page says HOW, with the commands that worked and the mistakes that cost time. Where this page and the contract differ, the contract is amended, not this page ignored. Update this page after every migration that taught something.

## 0. Rules that apply to every step

1. **Identity.** Commits in this repository and in every `vbm-*` repository carry the project identity: the address `witt3rd@witt3rd.com`, as author AND committer. Set it IN THE CLONE before the first commit (`git config user.name` and `user.email`; the build hosts' global configuration is not the project's) and check `git log -1 --format=%ae` before landing. The other address belongs to a different organisation's repositories only. A commit under the wrong identity can only be corrected by rewriting `main`, which is a major operation.
2. **Build hosts, never the desktop.** Lean, Lake and the lander run on a build host (`ssh <host>`); the desktop only runs git and `gh`. Put scripts on the host with `scp` and run them there: a command with nested quotes through `ssh` fails to parse (it did, twice).
3. **A quiet trunk.** Migrate one library at a time, with nothing else landing in the family repository. Pool workers keep their own clones; ask the pool to drain (`pool.off`) if work on this repository is in flight.
4. **Nothing is pushed until everything is green and verified locally.** The merge is pushed last, as a plain fast-forward, never forced.
5. **Detach anything that runs long** (`setsid nohup ... &`) and poll the log; a Lean gate takes minutes.
6. **A script run with `set -e` must not contain a `grep` that is allowed to find nothing**, nor a pipeline whose last command may return 1 (`a && echo x` at the end of a loop): both abort the script silently. Use `|| true` on purpose.

## 1. Pick the library, check the preconditions

Order is leaves first (section 7). For library `NAME` with old repository `OLD`:

* every old release tag is an ANNOTATED tag whose commit is an ancestor of `main`, and where the tag message has `tree_sha256=` it equals the old tree hash (`git rev-parse TAG^{tree}`): `git cat-file tag TAG`;
* the old `main` is green (run its own gate on a build host);
* no other branch with unique work: for each, `git log main..BRANCH` and `git cherry main BRANCH` (a `-` is already in main). An unmerged branch is archived as a diff with its reason in the old repository before migration, never silently dropped;
* no commit carries a wrong address: `git log --all --format='%ae%n%ce' | sort | uniq -c`;
* every family library it vendors has already migrated (its `deps`).

## 2. Move the history under `lib/NAME/` (local, nothing pushed)

`git-filter-repo` is not installed on the build hosts; the documented `filter-branch` recipe does the same for a repository of this size. Use `|` as the sed delimiter (a library name contains `-`, which breaks `s-...-...-`):

```
git clone --no-local git@github.com:witt3rd/OLD.git scratch && cd scratch && git checkout main
git rev-list main > ../commits.old
git filter-branch -f --index-filter '
  git ls-files -s | sed "s|\t\"*|&lib/NAME/|" |
  GIT_INDEX_FILE="$GIT_INDEX_FILE.new" git update-index --index-info &&
  mv "$GIT_INDEX_FILE.new" "$GIT_INDEX_FILE"' -- main
git rev-list main > ../commits.new ; paste -d' ' ../commits.old ../commits.new > ../commit-map
```

**Verify before going on** (all four must hold, and are the reason the later steps can be trusted):
1. same number of commits; 2. for every old tag commit `C` with new commit `C'` from the map: `git rev-parse C':lib/NAME` equals the old `C^{tree}` (the directory's tree hash is unchanged by the move); 3. authors and dates preserved (`git log --format='%ae %ad'`); 4. no address other than the project identity.

## 3. Merge into a clone of the family repository (still local)

```
git clone git@github.com:witt3rd/vbm.git hub && cd hub     # set the identity now
git fetch ../scratch main:refs/heads/migrate/NAME
git merge --allow-unrelated-histories --no-ff -m "chore(NAME): migrate the library, with its history, into lib/NAME" migrate/NAME
```
Verify: the first parent is the family `main`; `git diff --name-only origin/main HEAD` names nothing outside `lib/NAME/`; `git log --oneline -- lib/NAME` shows the old history. This merge commit is the one commit not made by the lander: it cannot be (the lander flattens, and a flattened history loses the old commits).

## 4. The adaptation commit (a second commit on top of the merge)

What the library needed only for being a standalone repository goes; the family repository has each once.

| Delete from `lib/NAME/` | Because |
|---|---|
| `.land/` (the vendored lander, its config, signers, hooks) EXCEPT `.land/lean.conf` | the family repository vendors the lander once; `lean.conf` is the library's own Lean gate configuration and stays |
| `.agents/`, `.github/`, `.githooks/`, `.gitleaks.toml`, `CONTRIBUTING.md`, `SECURITY.md` | the family repository has them |
| the library's copy of the public lint (`scripts/lint-public`, `test_lint_public.sh`, `public-banned-hashes.txt`) | it is a gate over the WHOLE repository, run by `scripts/repo-gates.sh` |
| any `vendor/<family-lib>/` and its lock lines | replaced by the path requirement `../<dep>` (section 4.2) |

Keep: sources, tests, `VERSION`, `CHANGELOG.md`, `README.md`, `LICENSE`, `NOTICE`, the package file, `lean-toolchain`, `mise.toml`, `.gitignore`, `docs/`, `scripts/` (what the library's own gate needs).

**4.1 The lander's Lean package.** If the library requires `land-ledger` from the vendored lander, change `lakefile.lean` to `from "../../.land/tool/lean"` and `lake-manifest.json` `"dir": "../../.land/tool/lean"`. The path is the same in `lib/NAME` and in a consumer's `vendor/NAME`, which is why it works in both.

**4.2 Family dependencies.** `lib/NAME/deps` lists them, one per line (the file exists even when empty). The package file requires each ONLY as `../<dep>`.

**4.3 The library's own gate (`scripts/tier1.sh`) in the new location.** It runs with the library directory as its working directory:
* tool paths `.land/tool/bin/X` become `../../.land/tool/bin/X`;
* the Lean gates take the library directory as their root: `LAND_LEAN_ROOT="$PWD" ../../.land/tool/bin/land-lean axiom|trust|recheck|ledger ...` (and `env LAND_LEAN_ROOT="$PWD"` for one run in the background), reading the library's own `.land/lean.conf`;
* **`run-tests-parallel` works from the git root, not the library**: give it absolute paths: `"${tests[@]/#/$PWD/}"`. Test scripts that do `cd "$(dirname "$0")/.."` need no change;
* delete the repository-level gates from the library gate (`land-pin verify`, `land-check`, `land-secrets`): they are the family repository's (`scripts/repo-gates.sh`), not one library's.

**4.4 The area and the card.** `lib/NAME/areas.json` (section 5 of the contract: one area `NAME`, or `NAME:<part>` areas, paths relative to the library, `steps` with `cwd`), `lib/NAME/card.toml` (`docs/hub-cards.md`; NO `[scores]` section until the library has a `score` command: unscored is a state, never invented numbers). Add the area to `.land/areas.json` by hand until `compose` exists, **and put the whole-repository step first in it**: `{"run":"mise exec -- scripts/repo-gates.sh"}` is a step of EVERY area, or a change inside one library skips the public lint and the secret scan.

**4.5 The old registry entry is deleted** (`registry/<owner>__NAME.toml`), its name removed from `registry/allowlist.toml`, and the README family-table link points at `lib/NAME`. A library appearing in both `lib/NAME/` and the registry is an error (`docs/hub-cards.md` rule 5).

`.land/areas.json` and `registry/allowlist.toml` and `.gitleaks.toml` are gate-defining: the commit that edits them carries `Protected: <reason>`.

## 5. Verify the candidate (this is the release-candidate check)

On a build host, in the merged-and-adapted tree, before any push:
1. the library's own gate: `cd lib/NAME && mise exec -- scripts/tier1.sh` (must end `tier1: ok`);
2. the family repository's gate: `mise exec -- scripts/tier1.sh` at the root, and `scripts/repo-gates.sh`;
3. the areas file is sound: `.land/tool/bin/land-areas validate` is valid; `git ls-files | land-areas unmapped` and `... overlap` report 0; `printf 'M\tlib/NAME/x\n' | land-areas touched` selects ONLY `NAME`; a registry change selects only `hub`; a `.land/` change selects everything.

## 6. Tag, push, verify

**Tags** (one per old tag; the contract's `land-release --retag` will replace this): on the host that holds the release key, create a NEW signed tag `NAME/vX.Y.Z` on `C'` (the commit-map image of the old tag commit, BEFORE the adaptation commit) with the SAME message body (so `tree_sha256=` and `manifest_sha256=` are identical), the same tagger and date (`GIT_COMMITTER_NAME/EMAIL/DATE`), signed with the release key: `git -c gpg.format=ssh -c user.signingkey=$KEY tag -s -F body NAME/vX.Y.Z C'`. Verify: `git -c gpg.format=ssh -c gpg.ssh.allowedSignersFile=.land/land.signers verify-tag NAME/vX.Y.Z` says `Good "git" signature`; the recorded tree hash equals the old one. The tag-protection ruleset covers `refs/tags/v*` and `refs/tags/*/v*`; confirm before the first push of a new library tag.

**Push:** `git ls-remote origin refs/heads/main` still equals the merge's first parent; `git push origin HEAD:main` (a fast-forward, no force); then the tags. **Verify from a FRESH clone on another machine**, not the build host's: commits touching `lib/NAME` (old history + 1), `git blame` reaches the old history, the tag verifies and peels to a commit on `main`, no wrong address anywhere in the history, both rulesets active.

**Afterwards, in this order:** (1) the old repository gets a last landing that replaces its `README.md` with a notice (where the library lives, which tags stay, how to re-point a pin), through ITS OWN lander; (2) the old repository is archived (`gh api -X PATCH repos/OWNER/OLD -f archived=true`); never deleted, no tag removed; (3) each consumer is re-pointed, one landing per consumer, with `land-pin vendor NAME <family URL> NAME/vX.Y.Z` (same version: the vendored files come out byte for byte as before, so the diff is the lock line alone); (4) update this page.

## 7. Order and the special cases (as of 2026-11-22; `deps` from each repository's `.land/pins.lock`)

Only 17 libraries have repositories (the registry's seven `coming soon` entries have none: they are born in `lib/`). Done: **vbm-rng**. The lander `vbm-land` stays a separate repository.

| Wave | Library | Commits | Tags | Notes |
|---|---|---:|---:|---|
| 1 (no family deps) | vbm-areas | 8 | 0 | no tag, so no retag; has no `VERSION` history to check |
| | vbm-prob, vbm-decision, vbm-scoreboard, vbm-forecast, vbm-memory, vbm-work, vbm-context | 9 to 52 | 1 (vbm-work 4) | plain Lean; vbm-work has four tags to re-create |
| | vbm-journal | 36 | 1 | has a `native/` C directory: its area needs a C step; check the C gate in `scripts/tier1.sh` |
| | vbm-simd | 72 | 2 | one unmerged branch to review; C substrate |
| | vbm-rt | 20 | 1 | C and headers only, no Lean: a different gate; do it after a plain-Lean one has proved the flow |
| 2 | vbm-json | 133 | 1 | needs vbm-simd; Lean plus C; one old branch is already in `main` (delete) |
| | vbm-sse | 114 | 1 | needs vbm-simd; **four unmerged branches** (archive each as a diff first) and Python scripts |
| | vbm-dispatcher, vbm-orchestrator | 9, 15 | 3, 8 | need vbm-work; orchestrator has eight tags to re-create |
| 3 | vbm-llm | 83 | 1 | needs vbm-json; one obsolete branch (a superseded lander update) to delete |

Consumers are re-pointed after each wave: the largest consumer pins most of these (`.land/pins.lock`); `land-pin outdated` lists what is left on an archived repository.

## 8. Mistakes that cost time (symptom, cause, fix)

| Symptom | Cause | Fix |
|---|---|---|
| `sed: unknown option to 's'` in the re-root | a hyphen in the library name used as the sed delimiter | use `|` |
| a script stops after printing a header, no error | `set -e` and a `grep` / `a && b` that returned 1 on purpose | `|| true` where "no match" is fine |
| the library's tests: `no such script` | `run-tests-parallel` changes to the git root | pass absolute paths (4.3) |
| the public lint fails on `.lake/...trace` | the library's build wrote the lander's package output under `.land/tool/lean/.lake`, untracked and not ignored | `.lake/` in the root `.gitignore` |
| a change inside a library would skip the public lint and the secret scan | the whole-repository gates were in one area only | `scripts/repo-gates.sh` as the first step of every area |
| a hub landing is refused on `.land/areas.json` / `.gitleaks.toml` | gate-defining files | a `Protected: <reason>` trailer, and the owner's word |
| `gh`/ssh commands with nested quotes fail to parse | quoting through `ssh` | write the script to a file, `scp`, run it |
| a commit shows on the wrong forge account | the wrong author address | rule 0.1; check before landing |
| two libraries at the same version collide on a candidate branch | `land-release --declare` names it `rc/v<VERSION>` without the library | a lander fix (queued): `rc/<NAME>/v<VERSION>`; until then declare one library at a time |
