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

## Lean packages (Lake)

A Lean library is vendored as source and required by path, never fetched. Proven offline, with no `.lake/packages` directory, on a standalone package, a consumer, and a diamond (two packages that both need a third).
1. Vendor each DIRECT dependency at `vendor/<name>/` (steps 2 to 4 above). Its own vendored dependencies come along inside it; do not flatten them.
2. Require it by path: `require «vbm-x» from "vendor/vbm-x"`. Never `from git`, and never a `.lake/packages` path anywhere (build file, compile flags, scripts).
3. Refer to a dependency's files, such as a C header passed with `-include`, as `__dir__ / "vendor" / "vbm-x" / ...`. Never write code in a build file to find a sibling: Lake has not fetched or placed anything yet when the build file is read, so such a lookup guesses.
4. The closure has ONE version of each package. A package vendored at several depths (a diamond) must have identical content hashes at every depth; the fast gate recomputes them and fails on a difference.
5. A pin names a signed release tag, its commit, and the manifest; an untagged pin is refused.

## Verify
`sha256sum -c <name>.manifest` passes; editing a vendored file makes the gate fail.

## Do not
- Patch vendored files locally (add a parameter or hook upstream).
- Pin to a branch or an unqualified tag.
- Use `from git` requires, `.lake/packages` paths, or a nested copy made by a prep command.
