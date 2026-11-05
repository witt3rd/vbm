---
name: flip-checklist
description: >-
  Flip a private vbm-* repo to public: scans, README, container proof, hosted runners, settings, and the one-line registry entry flip. Use when the owner says to publish a vbm-* repo.
---

# Flip a vbm-* repo public

Publishing is irreversible (history and forks cannot be recalled): run every step, then stop and get the owner's explicit word before the visibility change.

## Steps
1. **Scan the tree and the history.** The repo's public-readiness lint must pass (`mise exec -- scripts/lint-public`, or the repo's equivalent): no private name, host, path or number. History from before the decision may still hold earlier wording: publish from a fresh history (a squashed, re-rooted copy) and scan that.
2. **Scan for secrets.** Run a secret scanner over the full history of what will be published (for example `gitleaks detect --source . --log-opts=--all`); zero findings. Rotate anything that was ever found, even if removed.
3. **README.** It states what the library is, its honest score (link the card, or say unscored), how to build it, the trust ledger, and the licence. Remove "private" and "coming soon" wording.
   - Before going public, review `registry/scores` for cards of repos that are not public yet (move them to the private notes or hold them back): a card of a private repo is never linked or scored, so its JSON and page must not ship in the published history.
4. **Licence.** Add the licence file the owner chose (Apache-2.0 for code by default).
5. **Container proof.** In a clean container with no credentials and no network after dependency fetch, clone the fresh-history copy and run the fast gate: `git clone <copy> /work && cd /work && mise exec -- <fast gate>`. It must pass from nothing.
6. **Hosted runners.** A public repo must not run on a self-hosted runner. Switch workflows to hosted runners and run them once; `scripts/check-ci-visibility.py` style checks must pass.
   - A repo that ran its CI on a self-hosted runner while it was private: BEFORE the visibility change, `runs-on` returns to `ubuntu-latest`, and its runner is deregistered (`gh api repos/<owner>/<repo>/actions/runners` must then list none). Then `LAND_RED_MODE` in `scripts/land.conf` stays `push` (unchanged: the red check keeps reading the hosted run), and the repo's own `.github/visibility`, where it has one (its `scripts/lint-workflows.py` / Tier 1 fails a self-hosted workflow unless it says `private`), is set to `public` in the same change. This repo is enforced by `scripts/check-ci-visibility.py`. Explicit step: before going public: runs-on back to hosted + runner removed + red-check unchanged.
7. **Settings (public-repo checklist).** Apply each, then read it back:
   - Main protection: `gh api -X POST repos/<owner>/<repo>/rulesets --input skills/flip-checklist/ruleset-protect-main.json` (deletion and non-fast-forward on the default branch; no required pull request, no bypass list, so a direct fast-forward landing still works). After creating it, make one real landing with `scripts/land-direct` to prove it still lands.
   - Release tags: `gh api -X POST repos/<owner>/<repo>/rulesets --input skills/flip-checklist/ruleset-protect-tags.json` (no delete, no update of `v*` tags).
   - Fork pull-request workflows need approval for ALL outside contributors (Settings, Actions, General).
   - Workflow token read-only by default, and Actions cannot approve pull requests (`gh api -X PUT repos/<owner>/<repo>/actions/permissions/workflow -f default_workflow_permissions=read -F can_approve_pull_request_reviews=false`).
   - Private vulnerability reporting on (`gh api -X PUT repos/<owner>/<repo>/private-vulnerability-reporting`).
   - Secret scanning and push protection on (Settings, Code security).
   - Delete branch on merge on (`gh repo edit <owner>/<repo> --delete-branch-on-merge`).
   - No stale secrets or deploy keys; a security reporting address in the repo.
8. **Owner's word.** Report the checklist results and wait for the explicit go-ahead.
9. **Flip visibility** with the forge's command (for example `gh repo edit <owner>/<repo> --visibility public --accept-visibility-change-consequences`), then confirm an anonymous clone works.
10. **Flip the registry entry:** in `registry/<owner>__<repo>.toml` set `status = "live"` and add the repo link and the scoring keys (see `register-in-the-registry`); then `mise exec -- scorecard/registry-table --write README.md`, and land with `scripts/land-direct`.

## Verify
Anonymous clone and fast gate pass; the registry table shows the repo as `live` with a link; Tier 1 is green.

## Do not
- Give a repo that is not live a `repo` key: the validator rejects it.
- Flip without the owner's word, or from the old history.
- Edit the README tables by hand.
- Add a bypass actor to a ruleset, or require pull requests: the landing is a direct fast-forward by the owner.
