---
name: consume-a-pinned-library
description: >-
  Depend on a VBM library (or tool) by pin: version plus commit hash, vendored copy, a drift check. Use when one repo uses another VBM library.
---

# Consume a pinned library

Pin the version AND the commit hash (tags can move). Vendor the pinned copy so a fresh worktree is self-contained and offline. Do not use submodules (they break fresh worktrees) or fetch at run time.

## Steps
1. Choose the release tag and resolve its commit: `git ls-remote <url> refs/tags/<tag>`.
2. Vendor the files at that commit into a fixed directory (for example `vendor/<name>/`).
3. Write the lock file `<name>.pin`: `version`, full `commit`, and the SHA-256 of every vendored file (`sha256sum $(find vendor/<name> -type f | sort) > <name>.manifest`).
4. Add an offline drift check to the fast gate: re-hash the vendored files and compare with the manifest; a local edit fails it.
5. Add an online check to the scheduled slow tier: fetch the manifest at the pinned commit and compare; report a newer release, never force it.
6. Record the dependency in the trust ledger if its claims are not proved by you, and do not advertise a better score than the dependency's.
7. To update: change the pin, re-vendor, regenerate the manifest in one commit.

## Verify
`sha256sum -c <name>.manifest` passes; editing a vendored file makes the gate fail.

## Do not
- Patch vendored files locally (add a parameter or hook upstream).
- Pin to a branch or an unqualified tag.
