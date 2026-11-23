# The Family Hub as a Composed Repository

Status: normative contract (2026-11-22).

The VBM family hub is a single composed repository. Each family library lives in `lib/<name>/`, self-describes in `lib/<name>/card.toml`, and computes its own advisory scorecard. Everything that lists libraries—the family table, `registry.json`, the per-library pages, and the scorecard views—is composed from the cards by `hub compose` at publish time and deployed to GitHub Pages. Nothing generated is committed. `README.md` is short and hand-written (what the family is, the standard, the principles, and a single link to the site) and lists no library.

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

**Unscored is a state, not a number.** Until a library has its `lib/<name>/score` command (below), its card has NO `[scores]` section and the library is shown as *unscored*. A card must never carry invented, placeholder or zero-filled numbers to satisfy the shape. A `[scores]` section that IS present must be complete (every required field) and carry its provenance; the rule that refuses an incomplete one (section 2.2, rule 6) applies only to a section that is present.

`[scores]` records how the library is doing against the aspiration that its code is generated from a proved specification.

**Advisory rule (non-gating):** Scores are **advisory only**. A score NEVER gates a landing (`.land/land-direct`) or a release (`land-release`), and there are no pass/fail score floors on cards. A landing or release is gated only by the library's own correctness/build checks and card validation (`hub compose --check`), never by a scorecard threshold.

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
- `lib/*/card.toml`, `lib/*/VERSION`, `lib/*/deps`, and `lib/*/README.md` (when present)
- `registry/external/*.card.toml` (during transition)
- `guidelines/` (for publishing the guidelines on the site)

It executes nothing inside any library and makes no network calls.

### 2.1 Modes

- `hub compose --out <dir>`: validates all inputs and builds the complete static site (including `registry.json`) into `<dir>` deterministically. Nothing under `<dir>` is committed.
- `hub compose --check`: runs pre-push in Tier 1. It parses every card, checks every derived fact (`VERSION`, `deps`), runs the full composition into a scratch directory, and fails (exits non-zero) on any error—so a bad card is refused before it lands and the publish step can only receive valid input.

### 2.2 Validation rules

`hub compose` fails (exit non-zero) if:
1. Any `card.toml` is missing a required key, has an unknown key, or includes a derived key (`version`, `deps`).
2. `name` does not match the directory name `lib/<name>/` (or `<name>.card.toml` for external stubs).
3. `lib/<name>/VERSION` is missing or not valid `MAJOR.MINOR.PATCH`.
4. Any entry in `lib/<name>/deps` or `consumers` is unknown, or `deps` contains a cycle.
5. A library appears in both `lib/<name>/` and `registry/external/<name>.card.toml`.
6. A `[scores]` section is PRESENT and any required field is missing or has the wrong type, or `[scores.provenance]` is incomplete (an absent `[scores]` section is valid: the library is unscored).

### 2.3 Deterministic sort order

All lists and tables are sorted in `LC_ALL=C` byte order:
- Libraries are sorted by `(kind_rank, name)` where `kind_rank` is `0` for `tool` and `foundation`, `1` for `library`.
- `deps` and `consumers` arrays are sorted lexicographically.
- JSON keys are emitted in sorted order (`sort_keys=True`), 2-space indent, trailing newline.

### 2.4 The published site (`hub compose --out <dir>`)

Nothing generated is committed to `main`. `hub compose --out <dir>` builds a deterministic, HTML-escaped static site for GitHub Pages containing:

1. **Family table (`index.html`):**
   All libraries (in-repo and external stubs) with client-side filters (kind, status, dependencies) derived directly from the cards, linking to each library's page.
2. **Per-library pages (`libraries/<name>/index.html`):**
   One page per library composed from its `card.toml`, `VERSION`, `deps`, and `lib/<name>/README.md` (when present): scope, version, kind, status, license, dependencies, consumers, links, README prose, and the full scorecard view.
3. **Scorecard views (on each library page and at `scores/index.html`):**
   Rendered from each library's own `[scores]`, `[scores.custom]`, and `[scores.provenance]` in `card.toml`.
4. **Machine-readable registry (`registry.json`):**
   Served at a stable URL (`<site-root>/registry.json`) for tools and consumers. It contains an array of all libraries (in-repo and external stubs), each with:
   - all fields from `card.toml` (`name`, `scope`, `kind`, `status`, `license`, `links`, `consumers`, `scores`),
   - derived `version` (from `VERSION`, or `null` for external stubs) and `deps` (from `deps`, or `[]` for external stubs),
   - `path` (`"lib/<name>"` for in-repo libraries, `null` for external stubs).
   A consumer or tool reads it directly via HTTPS GET from `<site-root>/registry.json` (no git clone or GitHub API token required).
5. **Guidelines (`guidelines/`):**
   Rendered from `guidelines/` into static HTML pages on the same site.

All generated HTML is deterministic (identical inputs produce identical bytes, no build timestamps) and escapes all card text and README/guideline inputs against injection.

### 2.5 The committed `README.md`

`README.md` is **short and hand-written**: what the family is, the standard, the principles, and **a single link to the published site** (the family list). It lists no library, has no generated markers, and has no shields/badges (badge-free: status and scores live on the published site and in `registry.json`, avoiding external badge requests and README churn).

---

## 3. Publishing by Construction (Pre-Push Validation, One Deploy Job)

Because nothing generated is committed, two concurrent library landings never touch a shared generated file (`README.md`, `registry.json`, or `docs/libraries/*.md`), eliminating generated-file rebase conflicts by construction (`guidelines/factor-for-disjointness.md`).

### 3.1 Deleted from the contract (and what each deletion saves)

Nothing is added without deleting something:

- **Generated-paths declaration (`.land/generated-files.txt`, `LAND_GENERATED_LIST`) — deleted:** saves maintaining a list of generated paths and special-casing conflict resolution in the lander.
- **Regeneration hook (`LAND_REGEN_CMD`, `LAND_GEN_CMD` in `.land/land.conf`) — deleted:** saves running composition as a rebase/post-rebase side effect and mutating the working tree during `land-direct`.
- **Committed-output freshness gate (`--write` / `--check` diffing committed files) — deleted:** saves checking committed generated files for drift and saves `--ours`/regenerate dance on concurrent landings.
- **Generated-file conflict handling — deleted:** two libraries landing concurrently touch only their own `lib/<name>/` directories and never conflict.

### 3.2 Validation stays pre-push

- `scripts/tier1.sh` runs `mise exec -- hub compose --check` on the rebased tree **before** the push.
- `hub compose --check` parses every card, verifies every derived fact (`VERSION`, `deps`, acyclic graph), and runs the full composition into a scratch directory (discarded afterward).
- Any invalid card, missing version, broken dependency, or composition error fails Tier 1 and refuses the landing before it reaches `main`. The post-push deploy step can therefore only ever receive valid input.

### 3.3 The one post-push job (GitHub Pages deploy)

A single GitHub Actions workflow (`.github/workflows/pages.yml`) runs on push to `main`:

- **Why this is allowed beside the rule that nothing runs after the push:** That rule forbids *validation* or *mutation* after the push (CI that tests `main`, opens fixups, or pushes back). This workflow is a **deploy**, not validation: it cannot change `main`, it runs no tests, and if it fails, `main` is untouched and the previous published site stays live.
- **Permissions and tokens:** Needs only `contents: read` (the repository's read-only default `GITHUB_TOKEN` stays), `pages: write`, and `id-token: write`. No PAT, no deploy key, and no repository secret.
- **Workflow shape:**
  1. `on: push: branches: [main]` (plus `workflow_dispatch`), `concurrency: group: pages, cancel-in-progress: false`.
  2. Job `deploy` with `permissions: contents: read, pages: write, id-token: write` and `environment: name: github-pages, url: ${{ steps.deployment.outputs.page_url }}`.
  3. Steps: `actions/checkout` -> setup toolchain / `mise exec -- hub compose --out _site` -> `actions/upload-pages-artifact` (`path: _site`) -> `actions/deploy-pages` (`id: deployment`).
- **Public-repo settings required:** In repository **Settings -> Pages**, set **Source** to **GitHub Actions** (the workflow). The owner enables this setting once when the repository is public.

---

## 4. Hub Areas

Changes in the hub are partitioned into areas so independent library work does not trigger unrelated checks:

| Area | Paths | Steps |
|---|---|---|
| `lib-<name>` (one per library) | `lib/<name>/**` plus `lib/<dep>/**` for every `<dep>` in the transitive closure of `lib/<name>/deps` | Build, proofs, conformance vectors, and `lib/<name>/score --check` (library's own Tier 1). |
| `compose` | `lib/*/card.toml`, `lib/*/VERSION`, `lib/*/deps`, `lib/*/README.md`, `registry/external/*.card.toml`, `guidelines/**` | `mise exec -- hub compose --check` |
| `docs` | `docs/**`, `guidelines/**`, `MANIFESTO.md`, `CONTRIBUTING.md`, `README.md` | `scripts/lint-public`, relative-link check, guidelines index check. |
| `tooling` | `scripts/**`, `.land/**`, `.github/workflows/pages.yml`, `mise.toml`, `project.toml` | Full Tier 1 (`scripts/tier1.sh`), including negative self-tests for `hub compose` and `lint-public`. |

**Overlap and why:**
- **`lib-<name>` includes its dependencies (`lib/<dep>/**`):** A change in a dependency can break a consumer's proofs or build, so `lib-<name>` must re-validate when any of its dependencies changes. Sibling libraries that do not depend on each other remain disjoint (`guidelines/factor-for-disjointness.md`).
- **`compose` watches card and site inputs (`card.toml`, `VERSION`, `deps`, `lib/*/README.md`, `guidelines/**`):** Editing any card, version, dependency list, or guideline runs `hub compose --check` (parsing cards, checking derived facts, and composing into a scratch directory) without re-running unrelated library proofs.
- **`tooling` overlaps with everything:** Changing the composition script, Pages workflow, or gate runners can affect every area, so it runs the full Tier 1 suite.

---

## 5. What Is Deleted

Nothing is added without deleting what it replaces. Every duplicated place in the hub today has one disposition:

| Current item | Disposition | Replacement / Reason |
|---|---|---|
| `README.md` hand-written library status paragraph & old `<!-- registry:begin -->` table | **Deleted** | `README.md` is short and hand-written with a single link to the published site; it lists no library. |
| `registry/*__*.toml` and `registry/allowlist.toml` | **Deleted** | Replaced by `lib/<name>/card.toml` (and temporarily `registry/external/<name>.card.toml`). External submission allowlists are obsolete once libraries live in-repo. |
| `registry/scores/` (`*.json`, `*.md`) and its drift check (`scorecard/registry-table --check` / `scripts/test_registry.sh` drift checks) | **Deleted** (once the site publishes) | Scores live in `[scores]` inside `lib/<name>/card.toml` and are published to the site's scorecard views and `registry.json`. |
| `scorecard/` (`scorecard`, `scorecard_*.py`, `adapters/`, `registry-table`, `registry-validate`, `card-to-page`, `sandbox-bwrap`) | **Deleted** | Libraries compute their own scores via `lib/<name>/score`; `hub compose` replaces `registry-table`, `registry-validate`, and `card-to-page`. |
| `scorecard/SPEC.md`, `scorecard/DECISIONS.md` | **Deleted** (after distilling relevant principles) | Replaced by this contract (`docs/hub-cards.md`) and the guidelines. |
| `docs/cards/` (versioned snapshot dirs and PDFs) | **Deleted** | Historical cards live in git history; current pages are published on the site at `libraries/<name>/index.html`. |
| `ROADMAP.md` duplicated library lists, status tables, and dependency prose | **Deleted** | Library lists, statuses, and dependencies live in `card.toml` and `deps` and are published on the site and in `registry.json`. Architectural notes not tied to a single library may remain or move to `docs/`. |
| `docs/static-site.md` (earlier design note) | **Superseded / Deleted** | Its principle ("a second render of the same files, nothing committed") is now implemented directly by `hub compose --out <dir>` and the Pages deploy workflow. |
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

1. `hub compose` reads both `lib/*/card.toml` and `registry/external/*.card.toml`, so the published family table and `registry.json` remain complete throughout the migration.
2. A library MUST NOT exist in both `lib/<name>/` and `registry/external/<name>.card.toml`.
3. **Deletion on migration:** Migrating a library into `lib/<name>/` MUST delete `registry/external/<name>.card.toml` in the same landing.
4. **Retiring `registry/scores/*.md` and its drift check (nothing is ever missing):** The committed `registry/scores/` (`*.json`, `*.md`) pages and the `scorecard/registry-table --check` drift check remain intact until the Pages site is live and publishing from `hub compose --out _site`. Only *after* the site publishes are `registry/scores/`, `scorecard/`, and the drift check deleted, and `README.md` switched to its short hand-written form linking to the site. Once all libraries are migrated, `registry/external/` and `registry/` are removed completely.

---

## 7. The Scorecard Redesign

1. **Purpose:** A scorecard reports how a library is doing against the aspiration that its code is generated from a proved specification. It is **advisory**: it informs authors and readers, and never gates a landing or release.
2. **Minimal common set:** Every library reports the nine core metrics in Section 1.3 (`spec_lines`, `code_lines`, `proof_lines`, `generated_share_pct`, `proved_claims`, `total_claims`, `unproved_escapes`, `trusted_native_lines`, `trust_ledger_entries`).
3. **Library-specific extensions:** A library adds domain-specific metrics (e.g. throughput, binary size) under `[scores.custom]` with explicit unit suffixes, produced by its own `lib/<name>/score` command.
4. **History:** History is **derived from git**, never stored in a second file. Each landing that updates `lib/<name>/card.toml` commits the new `[scores]` and `[scores.provenance]`; the time series is read from `git log -p lib/<name>/card.toml`.
5. **Retiring the old scorecard:** The external `scorecard/` runner, its adapters, `registry/scores/`, and `docs/cards/` are deleted rather than maintained in parallel.

---

## 8. Sequence of Landings

Each step lands independently, small and green on Tier 1, ordered so nothing is ever missing:

1. **Contract:** Land `docs/hub-cards.md` (this document).
2. **Composer + pre-push validation:** Land `hub compose` (`--out <dir>`, `--check`, negative self-tests in `scripts/test_compose.sh`) and wire `mise exec -- hub compose --check` into `scripts/tier1.sh`. Nothing generated is committed.
3. **External stubs:** Create `registry/external/<name>.card.toml` for all unmigrated libraries so `hub compose` has the complete family from day one.
4. **Pages deploy workflow + owner setting:** Land `.github/workflows/pages.yml`; owner sets **Settings -> Pages -> Source = GitHub Actions** and verifies the site (family table, library pages, scorecard views, `registry.json`, guidelines) publishes live.
5. **Switch README + delete old registry/scorecard:** Replace `README.md`'s generated table with the short hand-written README linking to the live site, and delete `registry/*__*.toml`, `registry/allowlist.toml`, `registry/scores/` (`*.json`, `*.md`), `scorecard/` (including `registry-table` and its drift check), `docs/cards/`, `docs/static-site.md`, and duplicated library lists in `ROADMAP.md`.
6. **Migrate libraries (one landing per library):** Move each library into `lib/<name>/` with `card.toml`, `VERSION`, `deps`, `README.md`, and `score`, deleting `registry/external/<name>.card.toml` in the same landing. Once all libraries are migrated, delete `registry/external/` and `registry/`.
7. **Hub areas:** Enable per-area routing in `.land/` (`lib-<name>`, `compose`, `docs`, `tooling`) once areas support is active.

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
docs = "https://example.org/libraries/vbm-alpha/"

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
docs = "https://example.org/libraries/vbm-beta/"

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

### Published `registry.json` (`_site/registry.json`, excerpt)

```json
{
  "libraries": [
    {
      "consumers": ["vbm-beta"],
      "deps": [],
      "kind": "foundation",
      "license": "Apache-2.0",
      "links": {
        "docs": "https://example.org/libraries/vbm-alpha/"
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
        "docs": "https://example.org/libraries/vbm-beta/",
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
- Area `compose`: watches `lib/*/card.toml`, `lib/*/VERSION`, `lib/*/deps`, `lib/*/README.md`, and `guidelines/**`. Runs `hub compose --check`.
