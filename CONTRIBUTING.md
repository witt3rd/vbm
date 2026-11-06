# Contributing

Thank you for looking. A short, honest note about how this repository works.

## Who lands changes

**Only the owner lands changes on `main`**, directly, with the repository's own lander (`scripts/land-direct`, from [vbm-land](https://github.com/witt3rd/vbm-land)): no pull request is merged in the GitHub sense. That is the method this repository describes ([no pull requests for a single owner](guidelines/no-pull-requests-for-a-single-owner.md)), not a lack of interest in your work.

**Outside contributions are welcome** as proposals: open an issue, or a pull request from a fork. If the change is accepted it lands as a commit made by the owner (your authorship is kept where the change is applied as is; otherwise the commit says where it came from), and the pull request may be closed.

## Getting scored

Anyone may run the scorecard on their own repository and publish the card ([run-the-scorecard](skills/run-the-scorecard/SKILL.md)). To be listed in the registry, open an issue or a pull request that adds `registry/<owner>__<repo>.toml` and its card; `scorecard/registry-validate` checks it. Listing without review waits for the isolation that makes it safe to run a stranger's code ([register-in-the-registry](skills/register-in-the-registry/SKILL.md)).

## Checks

- CI runs only on a push to `main` and on manual dispatch, on GitHub-hosted runners; it does not run on pull requests. Run the gate yourself: `mise exec -- scripts/tier1.sh` (see the README for the tools it needs).
- Small changes (about 150 production lines), one idea each, Conventional Commits subjects (`feat(scorecard): ...`, `docs: ...`).
- Every metric and every gate has a negative self-test: a fixture shown to fail it.
- Metric definitions, floors, the adapter schema and the gates are never changed to make a number pass; a change lands when Tier 1 passes.
- No private names, hosts or local paths anywhere: `scripts/lint-public` refuses them.

## Licence

By submitting a contribution you agree that it is licensed under the Apache License 2.0 (section 5 of the licence).

## Security

Report vulnerabilities privately: [SECURITY.md](SECURITY.md).
