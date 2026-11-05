# Going public: the record

This repository started private and was made public by its owner. This page records what was checked, what the published history carries, and the order of the flip, so that a reader can see what "public-ready" meant here.

## A fresh history

The history of the earlier private repository was **not** published. The standard's own rule (`AGENTS.md`: "publish from a fresh history") and the flip checklist ask for it, and a scan of the earlier history showed why: it carried names of private machines and projects and an earlier project name in commits that cannot be changed, two pull-request refs that GitHub keeps after a flip and the owner cannot delete, and the cards of two repositories that are not public yet. So:

- the earlier repository was renamed (it stays private, as the archive: its history, its pull-request refs, its old CI runner registration);
- this repository is new. Its history starts with **one root commit**, authored by a neutral identity (`vbm-maintainers`), whose tree is the prepared public tree. Landings after that are ordinary commits made with the repository's own lander.

Consequences for a reader:

- Commit hashes of the earlier repository do not exist here. The scorecard cards `vbm-json-v1` to `v9` in `docs/cards/` were produced by the scorecard of that history; the scorecard commit each one records does not resolve in this repository. They are kept as the published results they were. `vbm-json-v10` is a re-run on this repository's history: its scorecard commit is the root commit.
- Cards of repositories that are not public yet are not in this repository, and no registry row links or scores one: those rows read "unscored" and have no link until the repository is public and has a card.
- The first release tags of the tools vendored here (`scripts/land/`) are unchanged: nothing is re-pinned.

## What was checked

| Check | Result |
|---|---|
| the earlier history (every ref of a fresh mirror, 81 commits), the same hash list and patterns as below | not publishable as is (hence the fresh history); no secret in it either |
| gitleaks 8.30.1, every ref of a fresh mirror of this repository, and the working tree | 0 findings |
| trufflehog 3.99.8, same scope | 0 verified, 0 unverified |
| the VBM public-readiness lint (`scripts/lint-public`: hashes of private names, path patterns, retired names) over the tree | clean |
| a scan of every commit message, author line, path and changed line of all refs for the same hashes plus plain patterns (host names, home paths, e-mails, addresses, internal tool names) | only the accepted items below |
| `scripts/tier1.sh` (the gate every change passes) in a fresh `ubuntu:24.04` container after dependencies were fetched, with the network disconnected, as an unprivileged user | passes |

Accepted by the owner, with reasons (no secret among them):
- text that matches the plain e-mail pattern by accident (a decorator, a symbol version, an ssh URL form in tests and docs);
- the public release-signing key of the vendored lander (`scripts/land.signers`) and the update workflow's bot address;
- the neutral no-reply author of the root commit, and the owner's name and address as author of landed commits (the same identity is already public in the owner's other repositories).

## The container proof

A clean `ubuntu:24.04` (image digest recorded with the evidence), run with an init process: packages fetched with the network up (`git jq util-linux procps openssh-client python3 python3-yaml bubblewrap gcc libc6-dev gh sudo systemd-coredump`), the repository cloned, the network disconnected, then `scripts/tier1.sh` as an unprivileged user. Needs a writable tmpfs for `/tmp`, and for the sandbox tests permission to create nested user namespaces and mount `/proc` (the container runs with the default seccomp and AppArmor profiles lifted and `/proc` unmasked); hosted runners provide the same. Four earlier attempts failed only for missing prerequisites (no free inodes in the container's `/tmp`, no C compiler, no `coredumpctl`, `/proc` masked), each fixed in the harness or in the workflow's package list, none by weakening a gate.

## The flip, in order

The workflows already say `runs-on: ubuntu-latest` (this repository never ran its CI on the owner's machines after it was created), and `scripts/check-ci-visibility.py` refuses a self-hosted job in a public repository.

1. The owner changes the visibility and checks that an anonymous `git clone` works.
2. At once, the settings below (the API refuses the fork-pull-request policy on a private repository, so it can only be set now).
3. Run the `tier1` workflow once (`gh workflow run tier1.yml`) and read it: it must be green on a hosted runner. (While the repository is private, hosted jobs cannot start; that is why this is the first CI run.)
4. Deregister the old CI runner of the archived repository.
5. Tell the consumers: the `vbm-json` README text about its card, and the registry row of `vbm-land`.

## Settings at the flip (each has a read-back)

1. Fork pull-request workflows need approval from **all outside collaborators**: `gh api -X PUT repos/witt3rd/vbm/actions/permissions/fork-pr-contributor-approval -f approval_policy=all_external_contributors`; read back `gh api repos/witt3rd/vbm/actions/permissions/fork-pr-contributor-approval --jq .approval_policy`.
2. Read-only workflow token that cannot approve pull requests: `gh api -X PUT repos/witt3rd/vbm/actions/permissions/workflow -f default_workflow_permissions=read -F can_approve_pull_request_reviews=false`; read back `gh api repos/witt3rd/vbm/actions/permissions/workflow`.
3. Private vulnerability reporting: `gh api -X PUT repos/witt3rd/vbm/private-vulnerability-reporting`; read back `gh api repos/witt3rd/vbm/private-vulnerability-reporting --jq .enabled`.
4. Secret scanning and push protection: `gh api -X PATCH repos/witt3rd/vbm -F 'security_and_analysis[secret_scanning][status]=enabled' -F 'security_and_analysis[secret_scanning_push_protection][status]=enabled'`; read back `gh api repos/witt3rd/vbm --jq .security_and_analysis`.
5. Delete head branches on merge: `gh api -X PATCH repos/witt3rd/vbm -F delete_branch_on_merge=true`; read back `--jq .delete_branch_on_merge`.
6. Protect `main` from deletion and non-fast-forward updates (no required pull request, no bypass list, so landing still works): `gh api repos/witt3rd/vbm/rulesets --input skills/flip-checklist/ruleset-protect-main.json`; read back `gh api repos/witt3rd/vbm/rules/branches/main --jq '.[].type'`; then one real landing with `scripts/land-direct`.
7. Protect release tags (`v*`) if this repository ever cuts releases (none exist today): `gh api repos/witt3rd/vbm/rulesets --input skills/flip-checklist/ruleset-protect-tags.json`.
8. No workflow uses `pull_request_target`, every workflow declares read-only `permissions:`, no deploy key, hook or stale secret exists (`gh api repos/witt3rd/vbm/keys`, `.../hooks`, `.../actions/secrets` list none).

## Consumers

- `vbm-json` states its card in its README (commit, verdicts); it links the card page of this repository, which keeps its URL. After the flip its text should say what `registry/scores/witt3rd__vbm-json.md` says now, and "the VBM standard (coming soon)" becomes a plain link.
- The `vbm-land` row of the registry becomes `live` once the owner approves it (`registry/allowlist.toml` is gate-defining); until then it reads "coming soon" with no link.
