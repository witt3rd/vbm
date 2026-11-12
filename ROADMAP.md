# VBM roadmap: the next verified bare-metal libraries (draft, revision 2)

Status: draft, revised 2026-11-12. The tooling layers drawn below are built (one way to land, vendor, pin and release across eleven repositories; see docs/family-design.md), and so are the libraries already released; none of the libraries LISTED below as next is. It lists the libraries we intend to write next in the `vbm-<name>` family, in dependency order, with an honest estimate of what each can prove, what it cannot, and how it is likely to score.

## Target architecture

Everything in this roadmap is ordered to reach one factoring. A VBM library is a thin layer of verified specification on top of shared foundation pieces, which sit on a language-neutral process layer, under a small set of conventions.

```
 libraries     vbm-json  vbm-sse  vbm-jsonrpc  vbm-acp  vbm-mcp  vbm-http1 ...    Lean specification + proofs, compiled to C and WebAssembly, generated bindings
                  |   every claim carries a clause tag and a review tier
 foundation    vbm-rt (freestanding runtime, ABI description and generators)   vbm-simd (live)
                  |   the shared machinery is the vbm-land payload, vendored by every repository
 process       vbm-land      the landing tool (lander, one red definition, freeze marker, revert-first watchdog) and what every repository shares: the test-running runtime, land-pin, land-release
 conventions   spec-clause tags  |  two tiers: fidelity-reviewed / agent-built  |  claim and blueprint for outside contributors
```

| piece | what it is | state today | when |
|---|---|---|---|
| **`vbm-land`** | the language-neutral landing tool and the guide to using it (the how-we-land document is its README) | exists as seven hand-made copies in four language ecosystems; no two identical | **first** (section below) |
| **`vbm-rt`** (0.2) | the freestanding Lean runtime shim (allocator, `mem*` replacements, trap, WebAssembly and native variants) and the ABI description and generators (item 0.3 folded in) | one consumer | at the second library |
| **`vbm-simd`** (0.4) | a bit-vector model of vector instructions, a trusted shim per instruction set, proved kernels | nothing yet | after the first SIMD measurements |
| **conventions** (0.5) | clause tags, two review tiers, claim-and-blueprint | nothing yet | adopt now |

Dependency rule: libraries depend on foundation pieces; foundation pieces depend only on `vbm-land`'s hook interface; `vbm-land` depends on nothing but a shell, `git` and the forge's command-line client, and names no language. No cycles.

## What a VBM library is (the shape every item below shares)

Every candidate is the same kind of thing: a **protocol codec plus a state machine over it**, written *sans-I/O*. The library is a pure Lean specification (types, a grammar as a relation, a reference implementation, a fast implementation, theorems). The code that runs is that specification, compiled to C, WebAssembly and generated bindings. The only code outside the proofs is a small boundary that moves bytes and time in and out and decides nothing.

Rules every library follows:
- **Bytes in, bytes out.** Caller-owned buffers, no allocator across the ABI, a "needed size" return.
- **Time and randomness are inputs.** A tick, a byte string of entropy. Nothing reads a clock or a random device.
- **Parameters, not primitives.** A hash or a MAC is a function argument; collision resistance is a hypothesis of a theorem, never an axiom.
- **Every limit is named** (maximum depth, line length, table size) and every refusal is a typed value.
- **Vectors come from the reference**, never from the fast code, and run unchanged in every generated binding.
- **The trust ledger counts what is not proved**: the compiler, the runtime, the operating system, each binding, each vendored artifact; each entry has an owner and a plan.

## The proof ladder, and what it has cost so far

The first library, `vbm-json`, is the measured exemplar. Its proofs follow a ladder that the rest of this roadmap reuses:

| rung | what is written and proved | measured in `vbm-json` |
|---|---|---|
| 1 | typed value, the **grammar as a relation**, the policies | ~250 lines of specification |
| 2 | a **reference recogniser** derived from the grammar; soundness, completeness, totality, unambiguity | ~1,400 lines of change in one landing |
| 3 | a **printer**, a round-trip theorem, vectors generated from the reference | ~400 lines |
| 4 | a **fast implementation** (iterative, bounded, in place) and a **refinement theorem** to the reference | ~1,600 lines; proofs are about 8x the size of the code here, the expensive rung |
| 5 | a flat ABI with a layout theorem | ~500 lines, then ~1,600 more to fuse the fast path |
| 6 | boundary: freestanding runtime, WebAssembly and native builds, generated bindings, public vector suites, mutants | ~3,500 lines, 8 landings, none of it Lean |

Overall: ~1,300 lines of specification and code, ~3,800 lines of proofs (2.9 : 1), 46 commits of which only 18 were library work. The rest was gates, CI, ledgers and performance infrastructure. That is the argument for the shared kit below: the second library should not pay that again.

**Honest status of the exemplar.** Its own scorecard card currently fails five of six ideals, and 5 of its 18 obligation-ledger claims are fully `proved` (8 partial, 1 open, 4 are limits no machine decides). A new library should expect the same shape at its first milestone: claims about a model, or examples, before the general theorem. Dependents must not advertise a better score than their foundation.

## Scorecard prospects, in general

The scorecard has two levels. **Level 1, Certified**, runs none of a candidate's code: it rechecks a proof export with an independent kernel, reads the claims, axioms, escapes and non-vacuity evidence, checks artifact symbols, trust-ledger entries and hand-written test counts, and reads history metrics. **Level 2, Measured**, runs the artifact: throughput against comparators, mutation score, differential agreement, reproducible builds, a second compiler.

- Every library below should aim at **Level 1 Certified** at its first public milestone. That is realistic, with one measured precondition: the proof export is capped at 64 MiB and 1,000,000 lines, and the full export of the exemplar is much larger. The first shared-kit slice must measure and, if needed, shrink the export to the closure of the named claims.
- **Level 2 passes should not be expected at first milestone.** Throughput within 2x of the best scalar comparator is the hard one; the exemplar is currently about 3x off.
- Two gaps in the scorecard itself, which this roadmap exposes and proposes to fix upstream: **(1) ideal 5 (efficiency) has no meaning for a state machine**: there is no comparator for a JSON-RPC peer or an OAuth client. We propose a substitute: resident bytes per session and nanoseconds per transition on a fixed generated trace. Without it every state-machine library fails the floor as `not-measurable`. **(2) ideal 1 (specified share 100 %) has no class for an externally verified boundary** such as a vendored, formally verified cryptographic library. We propose a separately counted class: pinned by hash, with the claim stated by its authors and named in the ledger.

## Summary table

Scoring (1-5, 5 best): **R** reuse beyond the first consumer; **T** trust-surface reduction; **F** proof feasibility end to end; **S** size (5 = small); **N** how many known consumers need it now.

| order | library | R | T | F | S | N | slices | first milestone |
|:-:|---|:-:|:-:|:-:|:-:|:-:|:-:|---|
| first | **`vbm-land`** (a tool, see below) | 5 | 3 | 5 | 3 | 5 | 21-28 | install by one command, pinned copy, drift check; then one red definition, watchdog |
| done | `vbm-json` (+ newline-delimited framing module) | 5 | 4 | 4 | 2 | 5 | +1-2 | Level 1 card; framing module |
| 1 | `vbm-sse` | 4 | 3 | 5 | 5 | 4 | 6-9 | reference + whole-buffer theorems |
| 2 | the shared foundation: `vbm-rt` (0.2-0.3 below), pinned by signed tag; there is no `vbm-kit` bundle | 5 | 2 | 5 | 3 | 5 | 6-8 | a third library scaffolds from it |
| 3 | `vbm-jsonrpc` | 5 | 2 | 4 | 4 | 5 | 6-9 | codec + peer machine |
| 4 | `vbm-acp` | 3 | 3 | 3 | 2 | 5 | 12-18 | pinned core profile |
| 5 | `vbm-mcp` | 4 | 3 | 3 | 1 | 5 | 16-24 | pinned client profile over stdio |
| 6 | `vbm-http1` | 5 | 5 | 4 | 3 | 3 | 10-14 | response framing + body length |
| 7 | `vbm-oauth` | 4 | 3 | 4 | 3 | 5 | 10-12 | device authorization grant |
| 8 | `vbm-uri` | 5 | 3 | 4 | 3 | 3 | 8-10 | RFC 3986 parse + resolve |
| 9 | `vbm-baseN` | 4 | 1 | 5 | 5 | 3 | 3-4 | base64/base64url/base16 |
| 10 | `vbm-journal` | 3 | 3 | 5 | 4 | 2 | 4-6 | generic chain checker |
| 11 | crypto boundary | 4 | 4 | 2 | 4 | 3 | 4-6 | verified-primitive boundary package |
| 12 | `vbm-utf8` | 4 | 2 | 5 | 5 | 1 | 4-5 | extracted from `vbm-json` |
| 13 | `vbm-ring` | 3 | 1 | 5 | 5 | 2 | 3 | bounded FIFO with a byte ABI |
| 14 | `vbm-jsonschema` | 4 | 2 | 3 | 2 | 2 | 8-12 | validated core subset |
| not now | `vbm-time`, `vbm-semver`, TLS, HTTP/2, a vendor LLM codec | | | | | | | see "Evaluated and not planned" |

A slice is one landing of at most ~400 lines including proofs, roughly one agent-lane day. Ranges are low to high; the order follows dependency and need, with the score sum as a sanity check. Total: roughly 150-215 slices including `vbm-land` and the optional SIMD package.

## The libraries

### `vbm-json` (done), plus a framing module
- **What it is.** Verified JSON (RFC 8259): typed values, grammar relation, reference and fast parsers, printer, flat tape ABI, WebAssembly and native builds, generated bindings.
- **Next step.** A `Lines` module: newline-delimited JSON framing. Spec sources: the NDJSON and JSON Lines pages, plus the stdio rules of the protocols below. Theorems: the printer never emits a newline or carriage return; split/join round trip; a torn final fragment is refused; splitting is invariant under how the byte stream is chunked. About 100 specification lines, 1-2 slices.
- **Why not a separate repo.** One small module, and every consumer already depends on JSON.

### `vbm-land`: the landing tool (first; a tool, not a proof library)
- **What it is.** The code that gets a change onto `main` under a mechanical gate, with no pull request: one lander (rebase onto current `main`, regenerate generated files, run the fast gate on the exact combination that will land, plain fast-forward push, one lock), **one** definition of a red `main` (the fast-gate job of the latest push failed; an infrastructure failure is not red; not knowing is not green), a hold marker and a freeze marker with an owner and an expiry, a revert-first post-merge watchdog, a known-flaky list whose entries are debt, and the installer and drift check below. It is language-neutral: it knows a command that runs the fast gate and nothing about what the gate checks.
- **Why first.** It already exists, seven times. Seven private repositories in four language ecosystems (Lean and C, Python, Rust, Ansible and shell) each took a copy on the same day, by hand. Measured: no two copies are identical; only 35 normalized lines are common to all seven (of 80-194 per copy); the copies range from 8 to 25 KB, together 92 KB, with 111 KB of tests and 73 KB of related scripts in one of them (~278 KB for one design); fixes do not propagate (six of seven still prune the shared clone's worktree records, only two accept the revert commit that `git revert` itself writes, one has the watchdog and the known-flaky list); a template copy taken in the morning was 26-31 % behind the live copy the next day. Every new library would be copy number eight, with its own divergence.
- **Design of the extraction.** One source repository. A consumer **vendors a pinned copy** into `.land/tool/` (so a worktree is self-contained and offline, and history shows which version landed what) and installs it with **one command** that also writes a three-line stub, a pin file and a parameters file. The pin records the version **and the commit hash** (tags can move) and a manifest of file hashes. A **drift check** runs offline in the fast gate (the vendored files must hash to the manifest: a local edit fails it) and online on the slow, scheduled tier (the manifest at the pinned commit is fetched and compared; a newer release is reported, never forced). An `audit` command lists every repository's pin and lag, replacing a hand-kept table. Rules: no local patches (a repository needing something different adds a parameter or a hook upstream); the lander never lands a commit that changes itself with the new copy (the old copy lands the new one). Rejected: submodules (they break fresh worktrees), a language package manager (not language-neutral), fetching at run time (a lander that changes under a landing).
- **Parameters and hooks, measured.** What differs between the copies reduces to about fourteen parameters (base branch, CI workflow and job names, fast-gate and regeneration commands, production paths for the size budget, lock wait, locale, required trailers, red-check mode, step timeouts) and four hook points: `pre-rebase`, `post-rebase` (receives the touched files; refusing stops the landing), `post-tier1`, and extra fields for the result line. Language-specific checks are hooks, not branches of the core.
- **README.** The how-we-land document is the README: the one idea, the three things trunk-based work needs, how to choose a mechanism, the template (agent-instruction block, two gate tiers, the lander, red exactly, freeze and watchdog, archive-then-discard, escalation threshold), the three metrics; plus install, parameters and drift. Repository-specific status tables and partner-specific sections are not part of the public edition.
- **Size.** 12-16 slices for the tool (core lander, options the copies have separately, a bare-remote test suite run against a matrix of parameter sets, install and pin and drift check, the red definition, known-flaky, watchdog and revert, hooks, templates, self-hosting) plus 9-12 migration slices, one per consuming repository, ordered smallest and lowest-risk first and the most heavily extended copies last. About 21-28 slices in all. A first version that two repositories can adopt (installer, lander, parameters, tests, offline drift check) is about 5-7 slices; the red definition, known-flaky and watchdog are the next 6-10.
- **Dependencies.** None.
- **Scorecard prospects.** Not scored as a library (it proves nothing); it determines whether every other repository lands cheaply and without drift. Its own tests are a bare-remote suite that can fail: lands, two racing workers (one waits), a conflict aborts naming files, a failing gate lands nothing, `main` moving during the gate re-runs it, no force push, a hold stops it.
- **First milestone.** A new repository installs it with one command, lands its first commit through it, and the drift check passes offline; a second repository in a different language does the same.
- **Risks.** A public tool that pushes to `main` and reverts is sensitive: the README states its preconditions (a repository worked by agents alone, `main` not deployed, a fast gate) and the watchdog is opt-in. Linux first (it uses `flock`). Behavioural differences between copies (lock wait, which runs count for red) are real decisions and become parameters, not noise.

### 1. `vbm-sse`: server-sent event streams
- **What it is.** The `text/event-stream` format used by streaming web APIs and by the streaming HTTP transport of agent protocols.
- **Spec source.** WHATWG HTML Living Standard, "Server-sent events" and "Parsing an event stream": a precise line-oriented algorithm (byte-order mark, CRLF/CR/LF, comment lines, field/value split, `data` lines joined with a line feed, `id` and `retry` rules, dispatch on a blank line).
- **Why reusable.** Every streaming HTTP client; chat and agent APIs; log tailing.
- **Size.** ~1,100-1,600 lines of Lean (about a quarter of `vbm-json`), 6-9 slices.
- **Verification plan.** Types and grammar relation; a reference interpreter; **chunk-split invariance** (`feed (a ++ b) = feed a` then `feed b`, including a carriage return at the end of a chunk, the classic bug); an unfinished event is never dispatched; `id` with NUL ignored; `retry` digits only; bounded buffers with a named line limit and typed refusal; a fast incremental scanner that refines the reference. Vectors from the web-platform-tests event-stream corpus plus generated rows.
- **Residue (ledger).** Only the shared kit's: compiler, runtime, bindings.
- **Targets.** C, WebAssembly, Python, Rust.
- **Dependencies.** None (it consumes an already decoded byte stream).
- **Scorecard prospects.** Level 1: likely. Level 2: a line scanner is where a Lean-compiled loop is most likely to land within 2x of a scalar comparator, but this is unmeasured. The incremental-parser proof is new effort (the exemplar is whole-buffer), so the 6-9 estimate is also the calibration point for HTTP framing.
- **First milestone.** Reference interpreter, whole-buffer theorems and generated vectors; then the chunk-invariance theorem.

### 2. The shared foundation, `vbm-rt` (items 0.2-0.3, see "Foundation layer"; no `vbm-kit` bundle)
- **What it is.** What `vbm-json` had to build around its proofs, extracted once: the ABI description generator, the vector driver for every binding, the generated binding scaffolds, the freestanding runtime and the mutation harness. The landing scripts and the language-neutral CI templates are not part of it: they are `vbm-land`, and the checks they run plug into it through hook points.
- **Why it exists.** 28 of the exemplar's 46 commits were this infrastructure. The first library copies it; the second is the right moment to extract it, so that the parameter list comes from two real consumers instead of a guess.
- **Size.** 6-8 slices of extraction (interface generators 3-4, runtime 3-4; +2 for the TypeScript and C# generators), mostly moving and parameterising existing code.
- **Verification plan.** The kit is a boundary and tooling package, not a proof library; its own gates have negative self-tests. First task: measure the size of the proof export restricted to the closure of the named claims against the scorecard's Level 1 cap, and add the restriction to the build.
- **Dependencies.** Two existing libraries to extract from.
- **Scorecard prospects.** Not itself scored as a library; it determines whether the others reach Level 1 cheaply.
- **First milestone.** A third library scaffolds, builds, passes its gates and produces generated bindings with no hand-copied scripts.

### 3. `vbm-jsonrpc`: JSON-RPC 2.0 codec and request/response matching
- **What it is.** The message layer under most agent and tooling protocols.
- **Spec source.** The JSON-RPC 2.0 specification (frozen since 2010) for the codec; matching rules come from the protocols that use it (identifiers unique among outstanding requests, no null identifiers, cancellation notifications, no or optional batches).
- **Why reusable.** Editor protocols, agent protocols, many RPC systems.
- **Size.** 6-9 slices.
- **Verification plan.** (a) *Classification*: a JSON value is exactly one of request, notification, result response, error response or invalid (total and exclusive); reserved error codes; encode/decode round trip over the verified JSON value. (b) *Peer machine*: a bounded outstanding-request table and `step : Peer x Event -> Peer x Effects` with events send, receive, cancel and tick. Theorems: every response is delivered to exactly one pending request or refused with a typed protocol error; no identifier is reused while pending; every pending request ends as response, error, cancellation or timeout within a stated tick bound; the table never exceeds its cap.
- **Residue (ledger).** Transport framing, the tick source, the peer's honesty.
- **Targets.** C, WebAssembly, Rust, Python, TypeScript.
- **Dependencies.** `vbm-json` and its framing module; `vbm-rt`.
- **Scorecard prospects.** Level 1: plausible. Level 2 efficiency: not measurable until the state-machine substitute exists.
- **First milestone.** Codec classification, round trip and vectors from the specification's own examples; then the peer machine.

### 4. `vbm-acp`: Agent Client Protocol
- **What it is.** The protocol between a code editor (client) and an AI agent: initialization and version negotiation, session setup, prompt turns, streamed updates, permission requests, cancellation.
- **Spec source.** The protocol's public repository: its JSON schema (v1 stable, v2 draft) and protocol documents. JSON-RPC 2.0 over stdio.
- **Why reusable.** Any agent or editor that speaks the protocol, and any test harness for either side.
- **Size.** 12-18 slices for a pinned core profile and the version-2 delta.
- **Verification plan.** Typed messages with round trip; version negotiation as a total function (highest mutual version or the exact error); **agent-side machine**: no prompt before initialization and session setup, at most one prompt in flight per session (v1), a cancel always ends the turn as cancelled within a bounded number of steps, every permission request answered or the turn cancelled; **client-side reducer (v2)**: a deterministic fold of session updates into a timeline, with entities keyed by (type, id), position fixed at first receipt, per-field upsert semantics (omitted unchanged, null cleared, value replaced, chunks append), a chunk arriving before its entity creates it and is never dropped, unknown variants preserved and ignored; the foreground state machine accepts only documented transitions and an unrecognised state never reads as idle. The headline application-level theorem lives in the consumer: *an agent runtime driven through the adapter only produces legal agent traces*.
- **Residue (ledger).** Fidelity to the specification (a stated limit, narrowed by pinning the schema by hash and generating conformance vectors from it); the peer's behaviour; transport.
- **Moving-target risk.** Two major versions side by side and a draft: the library ships one module per version over the shared JSON-RPC core, each pinned to its schema hash, failing closed on unknown input.
- **Targets.** C, WebAssembly, Rust, TypeScript.
- **Dependencies.** `vbm-jsonrpc`, the JSON framing module.
- **Scorecard prospects.** Level 1: plausible. Efficiency: state-machine gap above.
- **First milestone.** v1 core profile (initialize, new session, prompt, cancel, message and tool-call updates, permission request) with schema-derived vectors.

### 5. `vbm-mcp`: Model Context Protocol
- **What it is.** The protocol between an AI application and tool, resource and prompt servers.
- **Spec source.** The dated specification revisions and their machine-readable schemas. Note the shape: the newest revision (2026-07-28) **removed the connection handshake**: every request carries its protocol version and is accepted or rejected independently, with a `server/discover` call and a multi-round-trip request pattern; earlier revisions use an `initialize`/`initialized` lifecycle with sessions. Implementations may be dual-era.
- **Why reusable.** Every MCP client and server, and tests for both.
- **Size.** 16-24 slices for a client profile including the HTTP transport.
- **Verification plan.** Typed messages for a pinned profile (discovery/initialize, tools, resources, prompts, notifications, cancellation, progress, multi-round-trip input requests); version negotiation total and maximal; **capability gating** (a request is never sent for a feature the peer did not advertise); the modern per-request machine and the legacy lifecycle machine (no request before `initialized`, one `initialize` per session, shutdown terminates); the multi-round-trip loop bounded by a named limit; stdio framing from the JSON framing module; the HTTP transport's header and body rules as predicates over `vbm-http1` messages and `vbm-sse` events.
- **Residue (ledger).** Fidelity to the specification (prose with RFC 2119 words plus a schema: a stated limit); the behaviour of servers and tools; JSON Schema validation of tool arguments (see `vbm-jsonschema`, or refuse unvalidated calls); transport and TLS.
- **Moving-target risk.** Five dated revisions in about 20 months and a stateless redesign: one module per era, schema-hash pinned, unknown input refused.
- **Targets.** C, WebAssembly, Rust, TypeScript.
- **Dependencies.** `vbm-jsonrpc`, JSON framing; later `vbm-http1`, `vbm-sse`, `vbm-oauth`, `vbm-jsonschema`.
- **Scorecard prospects.** Level 1 plausible; efficiency gap as above.
- **First milestone.** Modern-era client profile over stdio, vectors from the schema's own examples; legacy lifecycle second; HTTP last.

### 6. `vbm-http1`: HTTP/1.1 message framing
- **What it is.** Parsing and framing of HTTP/1.1 messages: start line, header fields, body-length determination, chunked coding.
- **Spec source.** RFC 9112 (message syntax, body length, chunked coding) with field syntax from RFC 9110; ABNF per RFC 5234 and 7405. Verify section numbers at the first milestone.
- **Why reusable.** Any HTTP client or proxy that wants its parser proved, not fuzzed. It replaces a hand-written C parser of untrusted network bytes, the largest trust-surface reduction among the codecs.
- **Size.** 10-14 slices, the largest codec here.
- **Verification plan.** Parse iff grammar for a pinned subset; **body-length determination is a total function** (the decision table for HEAD, informational, 204, 304, transfer-encoding, content-length, close-delimited) and a theorem that a message with both `Transfer-Encoding` and `Content-Length` is refused or resolved by the stated rule (the request-smuggling class); chunked decode/encode round trip; truncation detected; named limits on header count and size; incremental feed invariant under chunking. Vectors: the corpora of mature independent parsers as the independent set.
- **Residue (ledger).** Sockets, TLS, DNS, the clock; semantics of a server.
- **Targets.** C, WebAssembly, Rust.
- **Dependencies.** `vbm-uri`, `vbm-rt`.
- **Scorecard prospects.** Level 1 plausible. Efficiency against the fast scalar and SIMD-assisted parsers is genuinely uncertain.
- **First milestone.** Response framing with body-length determination and chunked decoding.

### 7. `vbm-oauth`: OAuth client state machines
- **What it is.** The client side of the device authorization grant, the authorization-code grant with PKCE, token refresh, and discovery metadata.
- **Spec source.** RFC 8628 (device grant), RFC 6749 and 6750, RFC 7636 (PKCE), RFC 9700 (security best current practice), RFC 8414, 9728, 7591, 8707, 9207, and the IETF draft for OAuth 2.1 (still a draft: cite the RFCs it consolidates; check its status at the first milestone).
- **Why reusable.** Every CLI and agent that logs in to a service.
- **Size.** 10-12 slices: device flow 4-5, PKCE and authorization code 3-4, metadata and registration 3.
- **Verification plan.** Device flow: never polls faster than the server's interval; a slow-down response raises the interval monotonically; terminates by the expiry; denial and expiry are terminal; the machine is total over the response alphabet and an unrecognised response is a typed refusal. PKCE: the verifier is 43-128 characters of the unreserved alphabet (entropy is an input); `challenge = base64url(H(verifier))` with `H` a parameter; the verifier is never part of the authorization request; `state` is checked before the code is exchanged; the redirect URI is compared exactly; a code is used once; refresh rotation is monotone.
- **What is not claimed.** No theorem that OAuth is secure against a network attacker: that needs a symbolic protocol model, a different project. We prove the client machine is correct and total.
- **Residue (ledger).** Randomness (input), the hash (crypto boundary), HTTP (a port), the clock (input), the user, the authorization server.
- **Targets.** C, WebAssembly, Rust, TypeScript.
- **Dependencies.** `vbm-json`, `vbm-uri`, `vbm-baseN`, crypto boundary.
- **Scorecard prospects.** Level 1 plausible; efficiency gap as above.
- **First milestone.** Device authorization grant machine and vectors.

### 8. `vbm-uri`: URI parsing and resolution
- **What it is.** Generic URI syntax, reference resolution, normalization, percent-encoding, and the form-urlencoded format.
- **Spec source.** RFC 3986 (ABNF, reference resolution, normalization); `application/x-www-form-urlencoded` from the WHATWG URL Standard. A WHATWG URL parser is a separate later module with a differential against a mature implementation, because the two standards differ on purpose.
- **Verification plan.** Parse iff grammar, soundness and completeness. **Unambiguity is false** for RFC 3986 as written (it resolves overlaps by a longest-match rule), so the reference implements the stated disambiguation and that claim is `partial` by design. `remove_dot_segments` is idempotent and leaves no dot segments; resolving an absolute reference is normalization; percent-encoding round trip; exact scheme/host/port comparison functions for allow-lists.
- **Residue (ledger).** Internationalised host names and DNS stay out of scope.
- **Size.** 8-10 slices. **Targets.** C, WebAssembly, Rust, TypeScript. **Dependencies.** `vbm-utf8` optional, `vbm-rt`.
- **Scorecard prospects.** Level 1 plausible; efficiency against `ada`-class parsers unlikely at first.
- **First milestone.** RFC 3986 parse and resolve with the RFC's own reference-resolution examples as vectors.

### 9. `vbm-baseN`: base64, base64url, base16
- **Spec source.** RFC 4648 (base64, base64url, base16; non-alphabet characters; canonical encoding).
- **Verification plan.** `decode (encode b) = b`; `encode (decode s) = s` for canonical `s`; length formulas; the decoder rejects non-zero padding bits (the classic malleability bug) under the strict policy, with a lenient decoder as a separate named function; chunk invariance on 3-byte/4-character boundaries. Fully provable, no residue.
- **Size.** 3-4 slices. **Dependencies.** `vbm-rt`. **Needed by.** PKCE, binary fields in the protocols above, token formats.
- **Scorecard prospects.** Level 1 likely; efficiency comparators exist (scalar and SIMD base64 libraries); within 2x of the scalar best is plausible but unmeasured.
- **First milestone.** Strict base64/base64url/base16 with RFC 4648 vectors and malleability rows.

### 10. `vbm-journal`: append-only, hash-chained log and verifier
- **What it is.** A newline-delimited record format where each record carries a hash chained to the one before, an optional signed head, and a checker that reports exactly why a log is not accepted. There is no external standard: this library defines the format, and its fidelity claim is to its own specification.
- **Verification plan.** Chain check iff valid chain, for any hash function parameter; every single-record edit, deletion, reorder or insertion is detected **under the hypothesis that the hash is collision-free** (a theorem hypothesis, not an axiom); a torn final fragment is dropped, not accepted; the signature verdict combines four conditions (readable, correct MAC, not cut back, head matches) with a distinct refusal for each; the head binds the whole prefix.
- **Residue (ledger).** Atomic append and `fsync` behaviour of the operating system; the hash and MAC (crypto boundary); key custody.
- **Value.** A portable verifier: a Python or TypeScript auditor generated from the proved core.
- **Size.** 4-6 slices. **Dependencies.** `vbm-json` framing, crypto boundary. **First milestone.** Chain checker with tamper-detection theorems and vectors.

### 11. The crypto boundary: a verified boundary, not a reimplementation
- **What it is.** A package that gives Lean programs SHA-256, HMAC (later Ed25519 and ChaCha20-Poly1305) by binding to a **vendored, hash-pinned release of a formally verified C library** (HACL*, whose proofs of memory safety, functional correctness and secret independence are checked in F*, outside our kernel). We do not reimplement cryptography in Lean and do not claim to verify it.
- **What we write and prove.** A Lean *reference specification* (FIPS 180-4, RFC 2104/4231, RFC 8032, RFC 8439), executable and slow; padding and length encoding; the streaming wrapper over the block function (`hash (a ++ b)` equals chunked update-then-finish); HMAC as a construction over an abstract hash. Conformance: NIST CAVP vectors, RFC test vectors, Wycheproof, and a differential test of the C against the Lean reference on generated inputs; mutation tests of the binding.
- **What stays a named ledger entry.** The verified library itself (correct by its authors' proofs), the extraction tool, the C compiler (an optimiser can break constant-time code), timing side channels (Lean has no timing model: constant-time is not a claim we can prove), the F* toolchain. **We cannot prove that the C equals the Lean reference** with the verification tooling available today.
- **Scorecard prospects.** Poor by definition under the current rules (see gap 2): the code that runs is not Lean. Build it for the trust-ledger gain; present it as a boundary, not as a card-seeking library, unless an external-verification class is added.
- **Size.** 4-6 slices. **First milestone.** SHA-256 and HMAC-SHA-256 behind the boundary, with vectors, differential and mutants.

### 12. `vbm-utf8`: UTF-8
- **Spec source.** RFC 3629 and the Unicode Standard's table of well-formed byte sequences. Mostly an extraction from `vbm-json`, which already proves the relation for examples (its general "every invalid input is rejected" claim is open).
- **Verification plan.** Validator iff grammar; decode/encode round trip; every decoded value is a Unicode scalar; overlong and surrogate forms rejected; a fast validator (ASCII word fast path or DFA) refines the reference; error position is the first invalid byte.
- **Size.** 4-5 slices. **Scorecard prospects.** Level 1 likely; strong comparators exist (the standard library scalar validator; a SIMD library as the stated gap). **Dependencies.** `vbm-rt`; `vbm-json` then imports it (expand and contract).

### 13. `vbm-ring`: bounded FIFO
- **Spec.** None needed (textbook); the model is a list with fixed capacity and a typed refusal when full. Theorems: FIFO order, capacity never changes, refused exactly when full, memory bounded by capacity times item bound. A byte-specialised ring over a byte array provides an ABI.
- **Not claimed.** Concurrent (lock-free) variants: a different research problem.
- **Size.** 3 slices; mostly packaging of an existing proved structure. **Scorecard.** Level 1 likely; low differentiation, so a good second-repo trial of the kit rather than a showcase.

### 14. `vbm-jsonschema`: a validated core subset of JSON Schema
- **Why.** Agent protocols describe tool inputs with JSON Schema; validating before sending keeps the boundary from deciding.
- **Verification plan.** A `Satisfies` relation and a checker proved sound and complete for `type`, `properties`, `required`, `additionalProperties`, `items`, `enum`, `const`, numeric and length bounds, local references and the boolean combinators. **Unsupported keywords refuse (fail closed).** The official JSON Schema test suite is the independent corpus.
- **Size.** 8-12 slices; after the MCP milestone.

## Foundation layer: what is shared, and when to extract it

The "bare metal" part of a VBM library is mostly the same every time. This section says what is shared today, what each shared piece would be as its own package, and whether to extract it now or at the second library. The rule used: extract when a second consumer exists, the copies differ by a short parameter list, and the extracted piece has a test that can fail.

| item | what it is | shared today | size | recommendation |
|---|---|---|---|---|
| 0.2 `vbm-rt` | the freestanding Lean runtime shim: allocator, `mem*` replacements, trap, WebAssembly and native variants | one consumer; ~350 hand-written trusted C lines and one ledger entry | 3-4 slices | **at the second library**; prepare now by removing library-specific names and writing its contract |
| 0.3 `vbm-rt` (ABI part) | the interface description (buffers, needed-size return, options struct, error enum, versioning) and generators for the C header and Python, Rust, TypeScript, C# bindings | one consumer; generators exist for Python and Rust only | 3-4 slices + 2 for TypeScript and C# | **at the second library** |
| 0.4 `vbm-simd` | a Lean bit-vector model of vector instructions, a trusted shim per instruction set with differential tests, proved kernels (byte classification, UTF-8 validation, prefix-xor) | nothing | 12-16 slices (+2 research) | **after the first SIMD measurements** (a design memo and a prototype classifier with timings, in progress); deferred until they exist |
| 0.5 conventions | spec-clause tags, reviewed vs agent-built claims, claim-and-blueprint for outside contributors | nothing | docs + ~3 slices | **adopt now** |

Captain's ruling: there is no `vbm-kit` bundle and no `vbm-abi` repository. `vbm-rt` (early: the repository exists, nothing extracted yet; it carries the ABI description and generators too) is consumed by a pinned, signed tag through the one update flow.

**`vbm-rt` honesty.** The runtime is not as generic as its names suggest: it replaces exactly the pieces of the Lean runtime that one library's closure calls, stubs initialisation because that closure uses no standard-library constants, traps on big numbers, is single-threaded and uses a fixed static arena. A second library with a different closure will show what must grow. The contract is therefore a rule: a library's closure stays small and its naturals stay small, enforced by a gate. One shared runtime is the right shape for the trust ledger (one entry, one mutation suite, one pin).

**ABI honesty (part of `vbm-rt`).** Bindings are generated from an interface description, but today that description is itself hand-written and checked against a hand-written header, so the first link of "generated from the proofs" is not yet proved or derived. Moving the description into Lean is part of the extraction.

**`vbm-simd` honesty.** SIMD is the largest efficiency lever (the exemplar is roughly 3x off the best scalar JSON parser and far more off SIMD parsers). It is also the weakest to verify: Lean has no unboxed vector type, so kernels must be C functions at block granularity, bound to the Lean bit-vector model by differential testing rather than by a refinement theorem, with one named ledger entry per instruction set. What would be proved is the model's kernels against a scalar reference; the claim that the model matches the hardware is a stated limit. Libraries share the model and the shim harness, not the kernels. Defer until those measurements exist and show the classifier fits and the proof tool can discharge a 64-byte block.

### Conventions borrowed from large agent-built formalizations (0.5)

A large public Lean formalization of an existing reference work shows three practices that fit VBM.

1. **Spec-clause tags.** Each theorem carries a reference to the clause it formalizes (for example `rfc 8259 "6.4"`, with a comment when only part is covered), and a command lists coverage. For VBM this turns "the grammar matches the RFC" from an unrecorded review into a table, and yields a coverage metric: the share of grammar productions, schema types and normative sentences with a tagged theorem. Constraint: an attribute needs the full Lean import, which a specification module with a minimal import closure may not have, so tags live in the claims ledger module, with a gate that the cited theorem exists. Coverage shows traceability, not that a statement is faithful.
2. **Two tiers, per claim.** A *fidelity-reviewed* claim has a recorded attestation (module, clauses, reviewer, date, hash of the specification files) that is valid only while the hash matches; an *agent-built* claim has none. Reviewers read the specification diff only; proofs are machine-checked. The scorecard would display the reviewed share and never floor it: an agent-only library stays first-class. Named "reviewed" rather than "certified" because Level 1 already uses that word for machine rechecking.
3. **Claim and blueprint for outside contributors.** A contribution starts with an issue: the exact clause, the intended Lean statement, the dependencies and a proof outline; a maintainer approves it; then a pull request closes it. The blueprint is the specification diff, so this matches the rule that specifications change only deliberately. Proof-only and documentation fixes need no claim. The standing rules are shared with that project: state a result in its generality and never weaken it to make it provable; only the three standard axioms.

## Evaluated and not planned
- **Semantic-version parsing (`vbm-semver`): dropped.** The precedence rule is fully provable, but no consumer needs it, and range syntax is not standardised (package ecosystems differ), so "fidelity to which ranges?" has no answer. Revisit if a consumer appears.
- **TLS: not a library.** No production-grade verified TLS stack exists, and one cannot be written here. The honest design is a **sidecar** process: it removes certificate and record parsing from the agent's address space, shares one TLS context, and can attach credentials per allow-listed host so the agent never holds a key. What can be verified is the small framed contract between agent and sidecar (bounded, cancellable, typed errors). The sidecar is a named, sandboxed ledger entry and never our code.
- **A vendor chat-completions codec: kept private.** No authoritative specification, frequent drift and per-vendor quirks make a public claim of fidelity impossible. The generic part, an index-keyed chunk-fold algebra, belongs in the ACP reducer.
- **Time formats (`vbm-time`): watch.** RFC 3339 and HTTP-date with calendar-arithmetic proofs; 3-4 slices when a consumer needs them.
- **HTTP/2 and HPACK: dropped** (large, no consumer). **YAML:** dropped.

## Dependency graph

```
vbm-land ---------------------------> every repository (landing; the gates plug in by hooks)
vbm-rt -----------------------------> every library (runtime, ABI, vectors, bindings)
vbm-json (+ framing) <- vbm-jsonrpc <- vbm-acp
                     <- vbm-jsonschema <- vbm-mcp <- vbm-jsonrpc
                     <- vbm-oauth, vbm-journal
vbm-sse   <- vbm-mcp (HTTP transport)    vbm-http1 <- vbm-mcp (HTTP transport)
vbm-uri   <- vbm-http1, vbm-oauth, vbm-mcp
vbm-baseN <- vbm-oauth, vbm-acp, vbm-mcp (binary fields)
crypto boundary <- vbm-journal, vbm-oauth
vbm-utf8, vbm-ring: leaves
```

## Order and rationale

0. `vbm-land`: the landing tool, extracted from its seven copies; first, because it is language-neutral, already runs, and every later repository would otherwise copy it again.
1. `vbm-sse`: small, precisely specified, needed now by streaming clients, and the pilot for the incremental-parser proof pattern; the second library, installing `vbm-land` on day one.
2. `vbm-rt` (the runtime and the ABI): extracted from the two real libraries, at the second library.
3. `vbm-jsonrpc`: the base of both agent protocols.
4. `vbm-acp`, 5. `vbm-mcp`: the new capabilities; modern-era stdio first.
6. `vbm-http1`: the largest trust-surface reduction; unblocks HTTP transports. If trust surface matters more than capability, move it ahead of `vbm-acp`.
7. `vbm-oauth`, 8. `vbm-uri`, 9. `vbm-baseN`, 10. `vbm-journal`, 11. crypto boundary, 12. `vbm-utf8`, 13. `vbm-ring`, 14. `vbm-jsonschema`.

Where the first consumer of a codec already has the code, the library is a **lift**: the specification lands in the consumer first, written against only `Init` and the verified JSON library, then moves to its own repository with its proofs and is pinned back. That keeps release schedules independent of any one consumer's deadlines.

## Risks, stated plainly
- **Specification drift** (the agent protocols revise often): one module per era, schema-hash pins, unknown input refused.
- **Proof export cap**: Level 1 needs the export of the claims' closure to fit 64 MiB; unmeasured until the kit slice.
- **Unmeasured effort**: chunk-split invariance. The `vbm-sse` result recalibrates `vbm-http1` and stdio framing.
- **A card is not a proof**: counting a pinned library raises a consumer's specified share by its mass, not by effort; every slice names the theorem that makes it more than a relabeling.
- **Fidelity to prose specifications is a limit claim**, never `proved`: we say so on each card.

## The family design

The dispatcher, the orchestrator, the packages between them, the release-tag and pinning rules, and the build order are in [docs/family-design.md](docs/family-design.md).
