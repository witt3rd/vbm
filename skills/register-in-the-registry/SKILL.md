---
name: register-in-the-registry
description: >-
  Get a repo listed in the registry: run the scorecard, publish the card, open an issue with it. Use when a library is ready to be listed.
---

# Register in the registry

What is true today: the registry lists repos we have scored. Anyone may run the scorecard on their own repo (Level 1: certify from a proof export, nothing runs) and publish the card. To be listed, open an issue here with the card. Listing without our review waits for the isolation that makes Level 2 safe. You cannot write a score yourself.

The entry-file steps below are what a maintainer (or an allowlisted repo) uses: one PR adding exactly ONE file.

## Steps
1. In your repo, commit a valid `scorecard.toml`, and note the full SHA to score.
2. Locally dry-run the scorecard (see `run-the-scorecard`) and fix adapter errors (exit 2 names the key).
3. In a fork or branch of this repository add `registry/<owner>__<repo>.toml`:
   ```toml
   kind = "library"
   status = "live"
   what = "<one line>"
   milestone = "<first milestone>"
   depends_on = []
   repo = "https://github.com/<owner>/<repo>"
   commit = "<full sha>"
   manifest = "vbm-proof.toml"
   targets = ["C", "WebAssembly"]

   [latest]
   date = ""
   correctness = "unscored"
   landedness = "unscored"
   level = "unscored"
   card = ""
   ```
   (Copy `registry/witt3rd__vbm-json.toml` for the shape; unknown keys are rejected. A piece that is not public yet is an entry with only `kind`, `status` (`coming soon` or `planned`), `what`, `milestone` and `depends_on`: no `repo`, and it shows as unscored; a live entry with `correctness` and `landedness` `"unscored"` shows as unscored too. A live entry whose fresh card is on its way may carry both `"pending"`, `level = "pending"`, empty `date` and `card`: it shows as pending, is not a failure and needs no scoring.)
4. Validate: `mise exec -- scorecard/registry-validate registry/<owner>__<repo>.toml`
5. Open the PR with only that file.

## Verify
`registry-validate` exits 0. Today the registry accepts only allowlisted repos (`registry/allowlist.toml`); an outside entry is refused with a message naming the Level 2 isolation section of the spec.

## Do not
- Change the README table (generated: `scorecard/registry-table --write README.md`), a card, `[latest]` of an existing entry, or any other file in the same PR.
