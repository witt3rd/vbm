# Trunk-based landing

A small change reaches `main` within minutes, `main` is always green, and a mechanical gate (never a person's mood or a queue of reviewers) decides.

Three things make it work: a fast gate (minutes, not an hour; slow checks run after the merge), landing decoupled from release (unfinished work lands switched off; a release is a separate, reversible act), and small changes.
Agents start from a snapshot of the repository, so a long-lived branch is a growing semantic conflict even when git merges it cleanly. The trunk is the shared memory; keep it current.
