# Revert first, debug second

If Tier 2 fails on `main`, revert the offending commit immediately and push the revert to restore green; then fix the regression in an isolated worktree with the failure trace attached. Never fix forward on a red trunk: every agent that pulls from it is poisoned.
While `main` is red, only a fix or a revert may land. Conventional Commit subjects and trailers let a watchdog find the offending change and its blast radius without asking a model.
