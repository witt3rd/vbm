# The boundary never decides

Boundary code does not parse domain data, choose an action, interpret a result or render policy. The test: if a different correct implementation of this definition could change what the system does, it is deciding, and it belongs in the specification.
Calling deciding code a "handler" is relabeling, not verification. Inspect boundary definitions for decisions (branching on domain types, parsing, choosing actions) and fail the change when found.
A binding in another language that re-implements a decoder is boundary: counted, tested against the shared vectors, and never trusted.
