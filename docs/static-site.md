# Design note: a static site from the same JSON (not before the flip)

Status: a note only. Nothing here is built, and nothing is built before the repository is public and Pages is available.

Today the human-first view of a card is `registry/scores/<owner>__<repo>.md`, rendered from the card JSON by `scorecard/registry-table --write` (GitHub renders Markdown, so it works while the repository is private and after it is public). The registry's Card column links to that page; the raw JSON link lives inside it.

When the repository is public and Pages is available:
- A second render of the SAME files (`registry/*.toml` and the card JSON), never a second source: a generator in `scorecard/` writes the site into a build directory; nothing under it is committed.
- The registry as one HTML table with filters (kind, status, each verdict); each card as a page with the same content as `card.md` (verdict lines first, a table per ideal, the comparison, the trust ledger, how to reproduce, the PDF, the JSON, previous cards).
- Same gates as the Markdown pages: deterministic output, all card text escaped, a drift check in Tier 1 with a negative test (a JSON edit without regenerating fails), the public-ready lint stays green.
- The Markdown page stays: it is what the README links to and it works without Pages.
