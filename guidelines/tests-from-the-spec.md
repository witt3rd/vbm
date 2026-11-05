# Tests come from the specification

Prefer generated evidence to hand-written tests: vectors generated from the specification, a vendored public conformance corpus, differential runs against independent implementations, and fuzzing with a fixed seed.
A hand-written test is any executable case or expected-output file not produced by a generator from the specification at the pinned commit. It is not forbidden, it is counted, and the count is reported.
Report the mutation score as the substitute: mutate the code or the specification and show that a proof or a generated vector breaks. No tool can prove a repo has no tests; say what is countable and say what is not.
