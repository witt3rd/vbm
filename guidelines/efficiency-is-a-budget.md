# Efficiency is a budget

Correctness comes first; efficiency second, and it is measured, not assumed. Pick the yardstick that matches the goal (for many small agents: footprint per agent; for a codec: throughput against the best independent implementation on a fixed corpus) and ratchet it: it may only improve.
Measure on a pinned host with no other load so numbers are comparable over time. Allocation-site counts and similar proxies are diagnostics, not the yardstick.
Move toward bare metal (freestanding build, no libc, caller-owned buffers) only when a measured shortfall asks for it.
