# One lander

Workers never push to `main` themselves. A single lander holds a lock, rebases the worker's commits onto the current `main`, runs Tier 1 on that exact combination, fetches again (if `main` moved, rebase and check again), and pushes a plain fast-forward.
There is no force anywhere in it; a refused push runs the loop again. A hold marker stops every landing at once. Each commit lands as itself with a Conventional Commit subject (`type(scope): summary`), so history is linear and machine-readable.
The lander's last line of output is machine-readable (sha, commits, gate seconds, result) so a supervisor can read it.
