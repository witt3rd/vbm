# vbm-json: adapter notes

Notes for the subject's adapter (`vbm-json.toml`). They describe the adapter, not the subject; nothing here changes the subject.

## Decisions in the adapter

- **No scenario files.** Every test file of the subject loads its documents from the generated vectors (rows of `vbm-json-vectors-1`, the 100000-deep documents included) and builds no input of its own. `tests/abi_test.c` judges crafted export results by ENUMERATION over the boundary values of the result layout against a model of the layout contract (a driver: the card lists it), not a list of cases. A scenario file would be declared in `[tests] scenario_files`; none is.
- **Six corpora, one floored.** The floor ("within 2x of the best scalar comparator") is judged on the scorecard corpus only (DECISIONS 1). Five more corpora (two synthetic, three public) are reported per corpus with the percent of the best scalar comparator, never floored and never averaged in. Every corpus is verified against a pinned sha256 before anything is measured; the three public ones are fetched once outside the sandbox and mounted read-only (`$VBM_CORPORA`).
- **Gates and evidence.** `[tier1] gates` names each gate of the fast gate and the output line only its negative self-test prints. The test scripts print `ok scripts/test_NAME.sh` when the script, which holds the gate's negative self-tests, passed.
- **Attack suite.** `attack_cmd` runs the subject's relabel-attack suite without the attacks that rebuild Lean modules (`--no-lean`: a cold Lean build per attack does not fit the sandbox; the subject's second tier and its lander run them); `attack_sabotage_cmd` runs it with the gates each attack relies on replaced by stubs, which must make it fail.
- **Fast gate under the memory cap.** The sandbox caps memory at 4 GB and the fast gate starts three Lean gates at once (2 to 4 GB each). A `lake` shim serialises the `lake env lean --run` gates; the subject's `scripts/tier1.sh` is unchanged and the extra wall seconds are part of the timed result.

## Host-local setup (not in the repository)

`scorecard/sandbox-bwrap.binds` (git-ignored) lists the toolchains mounted read-only, the prebuilt comparators directory (`VBM_COMPARATORS`), the corpus directory (`VBM_CORPORA`) and the shared library simdjson needs. The comparators are built outside the sandbox by `scorecard/comparators/build.sh` and pinned by the hashes printed on the card.
