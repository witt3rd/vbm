---
name: release-a-library
description: >-
  Cut a signed release tag on a VBM library: confirm the commit landed, sign the tag with the release key, push it, verify it, never move it. Use when a library has a version to publish or a consumer needs something to pin.
---

# Release a library

A release is a signed, annotated tag on a commit that already landed on main through the lander (its fast gate green). Consumers pin the tag AND its commit (see consume-a-pinned-library), so a tag on anything else is untrustworthy.

Versioning: before 1.0, a change to anything a consumer can see (exported names, the ABI, a specification clause) is a minor version; a change that alters none of it is a patch. The first release is `v0.1.0`.

## Steps
1. Fetch, and confirm the commit to release is on `origin/main`: `git merge-base --is-ancestor <sha> origin/main`. It must have landed through the lander, never been pushed around it.
2. If the build file declares a version, it equals the tag (without the `v`).
3. Sign on the host that holds the release key; the key never leaves that host. Use an annotated, SSH-signed tag:
   `git -c gpg.format=ssh -c user.signingkey=<release key>.pub tag -s vX.Y.Z <sha> -m "<name> vX.Y.Z"` then `git push origin vX.Y.Z`.
4. Verify from a scratch clone, with the signers file of the standard: `git -c gpg.ssh.allowedSignersFile=<signers> tag -v vX.Y.Z`, and `git ls-remote <url> 'refs/tags/vX.Y.Z^{}'` returns the commit you meant.
5. Update the registry entry's `commit` and the consumers' pins, each in its own change.

## Do not
- Move or delete a pushed tag (the repository rules forbid it); cut a new version.
- Tag a commit that did not land through the lander.
- Copy the release key off its host or put it in a repository.
- Announce a release before step 4 passes.
