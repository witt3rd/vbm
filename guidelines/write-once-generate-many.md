# Write once, generate many

Write the core once in the proof language and generate the artifacts for every other language (C, WebAssembly, Rust, TypeScript, C#, Python) from it. Bindings are generated from a machine-readable description of the interface plus, at most, a small hand-written loader.
The interface is described in the proof language itself; an interface change is an expand-and-contract change (add, migrate, remove), never an in-place edit. Shared vectors come from the reference implementation and run in every binding.
The point is that there is one place where behaviour is decided, and every artifact is a translation of it.
