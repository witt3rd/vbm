# Vendor and pin: one way to take a dependency, one way to release

A library takes another by vendoring a SIGNED RELEASE of it at `vendor/NAME/` and locking it in `.land/pins.lock` (tag, commit, and the tree hash of the whole directory). Nothing is fetched at build time, so a clean clone builds offline and a sandbox needs no network.
The release tag is signed and records the tree hash; `land-pin vendor` refuses anything else, `land-pin verify` is a step of every fast gate (an edited, added or deleted file, an unlocked library, or two different copies of one library fail it), and a scorer re-checks each vendored library against the release it names, so a repository cannot ship a doctored dependency.
A vendored library is never patched: change it upstream, release it, bump the pin. The lock names the public https URL, because it is shared data.
A library releases `vX.Y.Z` tags made by `land-release` on a commit that already landed; a tag is never moved or deleted (a fix is a new version); before 1.0 a change a consumer can see is a minor version.
Why: a build that fetches can change under you, a dependency you cannot hash is a hole in the trust, and copies of one script drift (seven copies in five variants was the family's count).
