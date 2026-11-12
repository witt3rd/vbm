# Where things live: one layout convention

A tool keeps what belongs to it in one hidden folder, pins in a lock file, vendors source in `vendor/`, turns on by the presence of its config file, and versions with tags, a version file and a changelog: the habit of `.github/`, `.cargo/`, `Cargo.lock`, `go.sum`, `rustfmt.toml`.
In a vbm repository: the vendored tool and its pin, the lander's and each language's settings (`.land/land.conf`, `.land/lean.conf`), hooks, the signers file and the library lock live in `.land/`; vendored libraries in `vendor/NAME/`; the repository's own gate and tests in `scripts/` (`scripts/tier1.sh`); the version in `VERSION`, a `vX.Y.Z` tag and `CHANGELOG.md`.
A file a tool reads lives in `.land/` and its name is defined once; a config file's presence is its opt-in; there is one config format; a repository's own scripts and data stay where they are.
The full table and the rules are in vbm-land `docs/payload.md`, section 1a.
