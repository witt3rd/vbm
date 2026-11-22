# The Family Hub as a Composed Repository

Status: normative contract (2026-11-22).

The VBM family hub is a single composed repository. Each family library lives in `lib/<name>/`, self-describes in `lib/<name>/card.toml`, and computes its own advisory scorecard. Everything that lists libraries—the `README.md` family section, `registry.json`, and the per-library site pages—is composed automatically from the cards by `hub compose`. Nothing is duplicated by hand.

---

## 1. The Card (`lib/<name>/card.toml`)

Every in-repo library has exactly one metadata file: `lib/<name>/card.toml`.

### 1.1 Required fields

| Key | Type | Meaning |
|---|---|---|
| `name` | string | Library name (e.g. `"vbm-alpha"`). Must equal `<name>` in `lib/<name>/`. |
| `scope` | string | One-sentence description of what the library is. No newlines, non-empty. |
| `kind` | string | One of `"library"`, `"foundation"`, `"tool"`. |
| `status` | string | One of `"live"`, `"coming soon"`, `"planned"`. |
| `license` | string | SPDX license identifier (e.g. `"Apache-2.0"`). |
| `links` | table | Named URLs or repo-relative paths (`spec`, `docs`, `issues`, `package` — all optional; `hub` is derived). |
| `consumers` | array of strings | Family consumers that use this library (each must name a known library or component in `lib/` or `registry/external/`). |

Unknown top-level keys are rejected.

### 1.2 Derived fields (FORBIDDEN in `card.toml`)

A fact lives in exactly one file. The following are derived from sibling files and MUST NOT appear in `card.toml` (`hub compose` fails if any is present):

- **`version`**: read from `lib/<name>/VERSION` (one line, semantic version `MAJOR.MINOR.PATCH`).
- **`deps`**: read from `lib/<name>/deps` (one in-repo dependency `<dep>` per line, `#` comments and blank lines ignored; an absent or empty `deps` file means `[]`). Every `<dep>` must exist in `lib/` (or `registry/external/` during transition), and the dependency graph must be acyclic.

### 1.3 The `[scores]` section

`[scores]` records how the library is doing against the aspiration that its code is generated from a proved specification.

**Advisory rule (non-gating):** Scores are **advisory only**. A score NEVER gates a landing (`.land/land-direct`) or a release (`land-release`), and there are no pass/fail score floors on cards. A landing or release is gated only by the library's own correctness/build checks and freshness (`hub compose --check`), never by a scorecard threshold.

#### Common core metrics (required for every library)

Every library reports the following fields under `[scores]`, each with a fixed unit:

| Field | Type | Unit | Meaning |
|---|---|---|---|
| `spec_lines` | integer >= 0 | lines | Lines of pure specification. |
| `code_lines` | integer >= 0 | lines | Lines of executable/compiled code. |
| `proof_lines` | integer >= 0 | lines | Lines of machine-checked proofs. |
| `generated_share_pct` | number (0.0..100.0) | percent | Share of shipped code generated from the proved specification. |
| `proved_claims` | integer >= 0 | count | Obligation-ledger claims currently proved. |
| `total_claims` | integer >= 0 | count | Total obligation-ledger claims. |
| `unproved_escapes` | integer >= 0 | count | Occurrences of unproved escapes (`sorry`, `admit`, non-standard axioms). |
| `trusted_native_lines` | integer >= 0 | lines | Lines of trusted native boundary code (e.g. C shim). |
| `trust_ledger_entries` | integer >= 0 | count | Named entries in the library's trust ledger. |

#### Custom metrics (`[scores.custom]`)

A library may report additional library-specific metrics under `[scores.custom]` (for example `throughput_mb_s`, `wasm_bytes`, `max_rss_kb`). Every custom key MUST carry its unit in its name suffix (`_bytes`, `_mb_s`, `_seconds`, `_lines`, `_count`, `_pct`) and hold a numeric value (never prose).

#### Provenance (`[scores.provenance]`)

Every `[scores]` block MUST include `[scores.provenance]`:

| Field | Type | Meaning |
|---|---|---|
| `commit` | string | 40-hex git commit SHA of the tree from which the scores were computed (or `"working-tree"` only before first commit, never in landed state). |
| `tool_version` | string | Version of the scoring/measurement tool (e.g. from `VERSION` or tool pin) that produced the numbers. |

No wall-clock timestamp is recorded in `[scores]` or `[scores.provenance]`: identical inputs produce identical bytes.

#### Standard score command

Each library exposes a standard executable command:

```
lib/<name>/score [--write]
```

- Running `lib/<name>/score` runs the library's own deterministic measurement steps (proof-line/spec-line counts, closure/axiom checks, trust-ledger count, optional custom benchmarks) and prints the `[scores]` and `[scores.provenance]` TOML block to stdout.
- With `--write`, it updates `[scores]` and `[scores.provenance]` in `lib/<name>/card.toml` in place without altering the hand-written fields above `[scores]`.
- Deterministic: given the same library tree and tool version, `lib/<name>/score` produces byte-identical output.
- Advisory: `lib/<name>/score` exits 0 whenever measurement completes, regardless of metric values.

---

## 2. Composition (`hub compose`)

`hub compose` is the single composition script (e.g. `scripts/hub-compose`). It reads:
- `lib/*/card.toml`, `lib/*/VERSION`, `lib/*/deps`
- `registry/external/*.card.toml` (during transition)

It executes nothing inside any library and makes no network calls.

### 2.1 Modes

- `hub compose --write`: validates all inputs and writes all generated outputs deterministically.
- `hub compose --check`: validates all inputs, computes all outputs in memory, and exits non-zero if any committed generated file differs from what `--write` would produce, or if any stale generated page exists.

### 2.2 Validation rules

`hub compose` fails (exit non-zero) if:
1. Any `card.toml` is missing a required key, has an unknown key, or includes a derived key (`version`, `deps`).
2. `name` does not match the directory name `lib/<name>/` (or `<name>.card.toml` for external stubs).
3. `lib/<name>/VERSION` is missing or not valid `MAJOR.MINOR.PATCH`.
4. Any entry in `lib/<name>/deps` or `consumers` is unknown, or `deps` contains a cycle.
5. A library appears in both `lib/<name>/` and `registry/external/<name>.card.toml`.
6. Any `[scores]` field is missing, has the wrong type, or `[scores.provenance]` is incomplete.

### 2.3 Deterministic sort order

All lists and tables are sorted in `LC_ALL=C` byte order:
- Libraries are sorted by `(kind_rank, name)` where `kind_rank` is `0` for `tool` and `foundation`, `1` for `library`.
- `deps` and `consumers` arrays are sorted lexicographically.
- JSON keys are emitted in sorted order (`sort_keys=True`), 2-space indent, trailing newline.

### 2.4 Generated outputs

1. **`README.md` (family section):**
   `README.md` contains hand-written sections (the standard, the principles, build/contributing, license) and a generated family section delimited by markers:
   ```markdown
   <!-- hub:begin (generated by hub compose; do not edit by hand) -->
   ...
   <!-- hub:end -->
   ```
   `hub compose --write` replaces only the text between the markers. The generated section is NEVER edited by hand.

2. **`registry.json`:**
   A machine-readable JSON file at the repository root containing an array of all libraries (in-repo and external stubs), each with:
   - all fields from `card.toml` (`name`, `scope`, `kind`, `status`, `license`, `links`, `consumers`, `scores`),
   - derived `version` (from `VERSION`, or `null` for external stubs) and `deps` (from `deps`, or `[]` for external stubs),
   - `path` (`"lib/<name>"` for in-repo libraries, `null` for external stubs).

3. **Per-library pages (`docs/libraries/<name>.md`):**
   One Markdown page per in-repo library, generated from its `card.toml`, `VERSION`, and `deps`, containing: scope, version, kind, status, license, dependencies, consumers, links, and the full `[scores]` table with provenance. Orphan pages in `docs/libraries/` whose library no longer exists are deleted by `--write` and rejected by `--check`.

---

## 3. Freshness and Conflicts

A committed generated file is a conflict by construction (`guidelines/factor-for-disjointness.md`). The hub prevents merge pain and stale outputs using the lander's generated-file mechanism (`.land/tool/bin/land-direct`):

### 3.1 Lander configuration (`.land/land.conf`)

- `LAND_GENERATED_LIST=.land/generated-files.txt`: lists the pure generated paths (`registry.json`, `docs/libraries/*.md`).
  *(Note: `README.md` has hand-written prose outside its markers, so it is NOT blindly overwritten on conflict via `--ours`; instead, `LAND_GEN_CMD` refreshes the delimited section after any rebase.)*
- `LAND_REGEN_CMD="mise exec -- hub compose --write"`: runs when a rebase conflict occurs **only** in files listed in `LAND_GENERATED_LIST`. During rebase, `land-direct` takes `main`'s version of those conflicted files, completes the rebase, and runs `LAND_REGEN_CMD`. If any non-generated file conflicts, `land-direct` aborts and exits 11 for manual resolution.
- `LAND_GEN_CMD="mise exec -- hub compose --write"`: runs unconditionally after every rebase on the rebased tree, so two concurrent landings that each regenerated cleanly on their own branch cannot produce a combined tree with stale outputs.

### 3.2 Freshness gate (pre-push)

- `scripts/tier1.sh` runs `mise exec -- hub compose --check` on the rebased, regenerated tree **before** the push (nothing runs after the push).
- If any generated file (`README.md` delimited section, `registry.json`, `docs/libraries/*.md`) differs from what `hub compose` produces from the cards, `VERSION`, and `deps`, Tier 1 fails and the landing is refused.

---

## 4. Hub Areas

Changes in the hub are partitioned into areas so independent library work does not trigger unrelated checks:

| Area | Paths | Steps |
|---|---|---|
| `lib-<name>` (one per library) | `lib/<name>/**` plus `lib/<dep>/**` for every `<dep>` in the transitive closure of `lib/<name>/deps` | Build, proofs, conformance vectors, and `lib/<name>/score --check` (library's own Tier 1). |
| `generated` | `registry.json`, `docs/libraries/**`, `README.md`, `lib/*/card.toml`, `lib/*/VERSION`, `lib/*/deps`, `registry/external/*.card.toml` | `mise exec -- hub compose --check` |
| `docs` | `docs/**` (excluding `docs/libraries/**`), `guidelines/**`, `MANIFESTO.md`, `CONTRIBUTING.md`, `README.md` | `scripts/lint-public`, relative-link check, guidelines index check. |
| `tooling` | `scripts/**`, `.land/**`, `mise.toml`, `project.toml` | Full Tier 1 (`scripts/tier1.sh`), including negative self-tests for `hub compose` and `lint-public`. |

**Overlap and why:**
- **`lib-<name>` includes its dependencies (`lib/<dep>/**`):** A change in a dependency can break a consumer's proofs or build, so `lib-<name>` must re-validate when any of its dependencies changes. Sibling libraries that do not depend on each other remain disjoint (`guidelines/factor-for-disjointness.md`).
- **`generated` overlaps with card inputs (`card.toml`, `VERSION`, `deps`):** Editing any card, version, or dependency list requires freshness verification, without re-running unrelated library proofs.
- **`tooling` overlaps with everything:** Changing the composition script or gate runners can affect every area, so it runs the full Tier 1 suite.

---

## 5. What Is Deleted

Nothing is added without deleting what it replaces. Every duplicated place in the hub today has one disposition:

| Current item | Disposition | Replacement / Reason |
|---|---|---|
| `README.md` hand-written library status paragraph & old `<!-- registry:begin -->` table | **Becomes generated** | Replaced by `hub compose` delimited section (`<!-- hub:begin -->` ... `<!-- hub:end -->`). |
| `registry/*__*.toml` and `registry/allowlist.toml` | **Deleted** | Replaced by `lib/<name>/card.toml` (and temporarily `registry/external/<name>.card.toml`). External submission allowlists are obsolete once libraries live in-repo. |
| `registry/scores/` (`*.json`, `*.md`) | **Deleted** | Scores live in `[scores]` inside `lib/<name>/card.toml` and are reflected into `registry.json` and `docs/libraries/<name>.md`. |
| `scorecard/` (`scorecard`, `scorecard_*.py`, `adapters/`, `registry-table`, `registry-validate`, `card-to-page`, `sandbox-bwrap`) | **Deleted** | Libraries compute their own scores via `lib/<name>/score`; `hub compose` replaces `registry-table`, `registry-validate`, and `card-to-page`. |
| `scorecard/SPEC.md`, `scorecard/DECISIONS.md` | **Deleted** (after distilling relevant principles) | Replaced by this contract (`docs/hub-cards.md`) and the guidelines. |
| `docs/cards/` (versioned snapshot dirs and PDFs) | **Deleted** | Historical cards live in git history; current pages are generated at `docs/libraries/<name>.md`. |
| `ROADMAP.md` duplicated library lists, status tables, and dependency prose | **Deleted** | Library lists, statuses, and dependencies live in `card.toml` and `deps` and are rendered into `README.md` and `registry.json`. Architectural notes not tied to a single library may remain or move to `docs/`. |
| `docs/static-site.md` / separate site data pipeline | **Deleted** | Replaced by `registry.json` and `docs/libraries/*.md` generated directly by `hub compose`. |
| `guidelines/`, `MANIFESTO.md`, `CONTRIBUTING.md`, `SECURITY.md` | **Stays hand-written** | Not about any single library; these define the standard, principles, and governance. |

---

## 6. Transition (External Stubs)

Libraries not yet migrated into `lib/<name>/` are represented by a stub card at:

```
registry/external/<name>.card.toml
```

### Stub schema

| Key | Type | Meaning |
|---|---|---|
| `name` | string | Library name; must match `<name>` in `<name>.card.toml`. |
| `scope` | string | One-sentence description. |
| `kind` | string | `"library"`, `"foundation"`, or `"tool"`. |
| `status` | string | Must be `"external"`. |
| `repo` | string | Repository URL (optional if not yet public). |

No `[scores]`, `VERSION`, or `deps` are required for an external stub.

### Transition rules

1. `hub compose` reads both `lib/*/card.toml` and `registry/external/*.card.toml`, so `README.md` and `registry.json` remain complete throughout the migration.
2. A library MUST NOT exist in both `lib/<name>/` and `registry/external/<name>.card.toml`.
3. **Deletion on migration:** Migrating a library into `lib/<name>/` MUST delete `registry/external/<name>.card.toml` in the same landing. Once all libraries are migrated, `registry/external/` and `registry/` are removed completely.

---

## 7. The Scorecard Redesign

1. **Purpose:** A scorecard reports how a library is doing against the aspiration that its code is generated from a proved specification. It is **advisory**: it informs authors and readers, and never gates a landing or release.
2. **Minimal common set:** Every library reports the nine core metrics in Section 1.3 (`spec_lines`, `code_lines`, `proof_lines`, `generated_share_pct`, `proved_claims`, `total_claims`, `unproved_escapes`, `trusted_native_lines`, `trust_ledger_entries`).
3. **Library-specific extensions:** A library adds domain-specific metrics (e.g. throughput, binary size) under `[scores.custom]` with explicit unit suffixes, produced by its own `lib/<name>/score` command.
4. **History:** History is **derived from git**, never stored in a second file. Each landing that updates `lib/<name>/card.toml` commits the new `[scores]` and `[scores.provenance]`; the time series is read from `git log -p lib/<name>/card.toml`.
5. **Retiring the old scorecard:** The external `scorecard/` runner, its adapters, `registry/scores/`, and `docs/cards/` are deleted rather than maintained in parallel.

---

## 8. Sequence of Landings

Each step lands independently, small and green on Tier 1:

1. **Contract:** Land `docs/hub-cards.md` (this document).
2. **Composer + gates:** Land `hub compose` (`--write`, `--check`, negative self-tests in `scripts/test_compose.sh`), add `.land/generated-files.txt`, and wire `LAND_GENERATED_LIST`, `LAND_REGEN_CMD`, and `LAND_GEN_CMD` in `.land/land.conf` and `scripts/tier1.sh`.
3. **External stubs + README switch:** Create `registry/external/<name>.card.toml` for all current entries, switch `README.md` markers to `hub compose`, and delete `registry/*__*.toml` and `registry/allowlist.toml`.
4. **Migrate libraries (one landing per library):** Move each library into `lib/<name>/` with `card.toml`, `VERSION`, `deps`, and `score`, deleting `registry/external/<name>.card.toml` in the same landing.
5. **Delete old scorecard & duplicated docs:** Delete `scorecard/`, `registry/scores/`, `docs/cards/`, `docs/static-site.md`, and duplicated library lists in `ROADMAP.md`.
6. **Hub areas:** Enable per-area routing in `.land/` (`lib-<name>`, `generated`, `docs`, `tooling`) once areas support is active.

---

## 9. Worked Example (Two Generic Libraries)

Consider two generic libraries: `vbm-alpha` (a leaf foundation library) and `vbm-beta` (a protocol library depending on `vbm-alpha`).

### `lib/vbm-alpha/`

`lib/vbm-alpha/VERSION`:
```text
0.3.0
```

`lib/vbm-alpha/deps` (empty):
```text
# no in-repo dependencies
```

`lib/vbm-alpha/card.toml`:
```toml
name = "vbm-alpha"
scope = "Verified byte-stream framing primitives with a freestanding C ABI."
kind = "foundation"
status = "live"
license = "Apache-2.0"
consumers = ["vbm-beta"]

[links]
docs = "docs/libraries/vbm-alpha.md"

[scores]
spec_lines = 420
code_lines = 310
proof_lines = 1180
generated_share_pct = 94.5
proved_claims = 14
total_claims = 14
unproved_escapes = 0
trusted_native_lines = 48
trust_ledger_entries = 3

[scores.custom]
wasm_bytes = 24576

[scores.provenance]
commit = "1111111111111111111111111111111111111111"
tool_version = "0.3.0"
```

### `lib/vbm-beta/`

`lib/vbm-beta/VERSION`:
```text
0.1.0
```

`lib/vbm-beta/deps`:
```text
vbm-alpha
```

`lib/vbm-beta/card.toml`:
```toml
name = "vbm-beta"
scope = "Verified request/response state machine over framed byte streams."
kind = "library"
status = "live"
license = "Apache-2.0"
consumers = []

[links]
spec = "https://example.org/spec/beta"
docs = "docs/libraries/vbm-beta.md"

[scores]
spec_lines = 680
code_lines = 540
proof_lines = 1950
generated_share_pct = 100.0
proved_claims = 19
total_claims = 21
unproved_escapes = 0
trusted_native_lines = 0
trust_ledger_entries = 2

[scores.custom]
throughput_mb_s = 312.4

[scores.provenance]
commit = "2222222222222222222222222222222222222222"
tool_version = "0.1.0"
```

### Generated `README.md` section (`hub compose --write`)

```markdown
<!-- hub:begin (generated by hub compose; do not edit by hand) -->
| Name | Version | Kind | Status | Scope | Generated % | Card |
|---|---|---|---|---|---|---|
| vbm-alpha | 0.3.0 | foundation | live | Verified byte-stream framing primitives with a freestanding C ABI. | 94.5% | [card](docs/libraries/vbm-alpha.md) |
| vbm-beta | 0.1.0 | library | live | Verified request/response state machine over framed byte streams. | 100.0% | [card](docs/libraries/vbm-beta.md) |
<!-- hub:end -->
```

### Generated `registry.json` (excerpt)

```json
{
  "libraries": [
    {
      "consumers": ["vbm-beta"],
      "deps": [],
      "kind": "foundation",
      "license": "Apache-2.0",
      "links": {
        "docs": "docs/libraries/vbm-alpha.md"
      },
      "name": "vbm-alpha",
      "path": "lib/vbm-alpha",
      "scope": "Verified byte-stream framing primitives with a freestanding C ABI.",
      "scores": {
        "code_lines": 310,
        "custom": {
          "wasm_bytes": 24576
        },
        "generated_share_pct": 94.5,
        "proof_lines": 1180,
        "provenance": {
          "commit": "1111111111111111111111111111111111111111",
          "tool_version": "0.3.0"
        },
        "proved_claims": 14,
        "spec_lines": 420,
        "total_claims": 14,
        "trust_ledger_entries": 3,
        "trusted_native_lines": 48,
        "unproved_escapes": 0
      },
      "status": "live",
      "version": "0.3.0"
    },
    {
      "consumers": [],
      "deps": ["vbm-alpha"],
      "kind": "library",
      "license": "Apache-2.0",
      "links": {
        "docs": "docs/libraries/vbm-beta.md",
        "spec": "https://example.org/spec/beta"
      },
      "name": "vbm-beta",
      "path": "lib/vbm-beta",
      "scope": "Verified request/response state machine over framed byte streams.",
      "scores": {
        "code_lines": 540,
        "custom": {
          "throughput_mb_s": 312.4
        },
        "generated_share_pct": 100.0,
        "proof_lines": 1950,
        "provenance": {
          "commit": "2222222222222222222222222222222222222222",
          "tool_version": "0.1.0"
        },
        "proved_claims": 19,
        "spec_lines": 680,
        "total_claims": 21,
        "trust_ledger_entries": 2,
        "trusted_native_lines": 0,
        "unproved_escapes": 0
      },
      "status": "live",
      "version": "0.1.0"
    }
  ]
}
```

### Hub areas for the example

- Area `lib-vbm-alpha`: watches `lib/vbm-alpha/**`. Runs `vbm-alpha`'s build, proofs, vectors, and `lib/vbm-alpha/score --check`.
- Area `lib-vbm-beta`: watches `lib/vbm-beta/**` and `lib/vbm-alpha/**` (from `lib/vbm-beta/deps`). Runs `vbm-beta`'s build, proofs, vectors, and `lib/vbm-beta/score --check`.
- Area `generated`: watches `lib/*/card.toml`, `lib/*/VERSION`, `lib/*/deps`, `registry.json`, `docs/libraries/**`, and `README.md`. Runs `hub compose --check`.
