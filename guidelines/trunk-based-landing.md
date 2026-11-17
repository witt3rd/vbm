# Trunk-based landing

A small change reaches `main` within minutes, and a mechanical gate (never a person's mood or a queue of reviewers) decides. A push to `main` is **best-effort**: it says the fast gate passed on that combination, not that `main` is green. Go fast in development; release with caution.

Four things make it work: a fast gate (minutes, not an hour), landing decoupled from release (unfinished work lands switched off), small changes, and a **release candidate** that carries the caution. Before a release, a candidate branch is declared, the project's FULL suite runs on it (nothing cached, selected or skipped), and fixes are made on the branch and on `main` until it is green; only then is it tagged. The slow, complete checks belong to the candidate, once per release, not to every landing.

Agents start from a snapshot of the repository, so a long-lived branch is a growing semantic conflict even when git merges it cleanly. The trunk is the shared memory; keep it current. The candidate branch lives only as long as a release takes and moves only by fixes.
