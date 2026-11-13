# The VBM family: packages, dependencies, and the dispatcher and orchestrator

Status: approved by the owner, 2026-11-11. Nothing below is built yet; the sequence in section 7 builds it.
It EXTENDS the standard (the guidelines, the registry, the pinned-library skill); it replaces nothing in it.

## 1. What the standard already says (so we extend, not duplicate)

- **Sans-I/O shape** (ROADMAP): a library is a pure Lean specification; bytes in, bytes out; time and randomness
  are inputs; every limit is named; every refusal is a typed value; test vectors come from the reference.
- **The boundary never decides** (guideline): code at the edge moves bytes; it does not choose.
- **Specification first** (guideline): the spec lands before the implementation.
- **Layering rule** (ROADMAP): libraries depend on foundation pieces; foundation depends only on vbm-land's hook
  interface; vbm-land depends on nothing but a shell, git and the forge client.
- **Registry** (`registry/*.toml`): one entry per package with `kind`, `status`, `what`, `depends_on`.
- **Pinned dependencies** (vbm-land `docs/pin.md`, tool `land-pin`): a library is vendored at `vendor/NAME/` and locked by
  tag, commit and tree hash; the signed tag records the tree hash; nothing is fetched at build time; `land-pin verify` is
  the offline fast-gate check.

## 2. What we found (facts, 2026-11-11)

1. Only vbm-land has release tags. The Lean libraries (vbm-simd, -json, -sse, -journal, -context, -llm, -memory, -rt)
   have none, so nothing can be pinned by version.
2. The first assembling application consumes libraries through Lake git requires plus its own lock script, not the vendored pin the standard
   prescribes. That is the source of the pain: nested `.lake/packages` layouts, a path hard-coded in vbm-json's build
   file, per-host "prep" commands, and sandboxed agents that cannot fetch.
3. The shared vocabulary (typed outcomes, sessions, money, route, judge, host life) lives INSIDE the first assembling application: about 38,000
   lines of spec in about 150 modules. The dispatcher's and the orchestrator's specs mostly exist there already.
4. The registry already drifts from the build files: it lists `vbm-sse` as a dependency of `vbm-llm`, whose build
   file requires only `vbm-json`. Nothing checks this.
5. In the first application the logic of the dispatcher and the orchestrator is in shell: one dispatch script (queue,
   capacity, checkout, model choice, worker start, repair loop, landing, outcome mapping, all tangled) and a task
   script.

## 3. The two machines

**Dispatcher** manages one host's work. It knows load and capacity, claims items from the queue, and hands each to an
orchestrator. It can run several orchestrators at once. It knows nothing about agents, tests or reviews.

**Orchestrator** runs ONE task end to end:
1. runs the worker agent (which is told the project's principles, so it conforms from the start);
2. runs the lints and tests; on failure, cycles back to the worker with the full output;
3. runs the reviewer agents, built from the lander's definitions; on criticism, cycles back to the worker;
4. closes out: lands the change, records the typed outcome, keeps the evidence.

A **worker** and a **reviewer** are roles of the same agent program (a role is data: instructions and tools).

**The lander** (vbm-land) DEFINES, as project-owned data: the principles, the reviewer definitions, the checks to
run. It also performs the landing step. It runs nothing agentic and knows nothing of reviewers' execution.

## 4. The packages

```
 assembly     application     the agent core + the bindings: queue (pgmq), jail (bwrap), git, vbm-land, the model provider
                |  supplies the ports below
 machines     vbm-dispatcher  host capacity, claim, lease, heartbeat, hand-over                       (sans-I/O state machine)
              vbm-orchestrator the task cycle: worker, checks, reviewers, repair, close-out           (sans-I/O state machine)
                |  both depend only on vbm-work; neither depends on the other (the dispatcher reaches the orchestrator through a port)
 vocabulary   vbm-work        Task in, typed Outcome out; the review words; the kinds of block
              vbm-judge, vbm-money, vbm-route, vbm-host    extracted from the application when a second consumer needs them
 libraries    vbm-json  vbm-sse  vbm-journal  vbm-context  vbm-llm  vbm-memory                          (exist)
 foundation   vbm-rt  vbm-simd                                                                         (exist)
 process      vbm-land                                                                                 (exists)
```

Names and grouping are for you to confirm. Rule for new packages: a package is created when its specification is
ready and a second consumer exists; it is never created empty.

### 4a. The whole system (decided 2026-11-12)

The two machines are two of several components, and the same rule applies to all of them: each is its own repository, specified and verified alone, then assembled; the application that uses them ends as the composition root (the bindings to the real world, the wiring, the command line, and the statement of what the assembly guarantees). The planned components, none created yet (each when its specification is ready and a second consumer exists):

| component | what it is | a port it owns |
|---|---|---|
| vbm-capacity | the capacity of all the hosts, fixed and elastic: the host lifecycle and a pure reconcile of policy and observed state into actions | `Provider` (provision, status, terminate, list) |
| vbm-agent | the agent core: the session, context, tools and parallel calls, memory use, recovery; extracted last | `Model`, `Tools`, `Journal`, `Memory` |
| gateways | how an outside channel (a chat service, mail) meets the one inbox: what must happen to a message in and an event out | `Channel` |
| vbm-observer | a read-only view of the hosts, the runs and the journals: the pure projection from typed state to a view; the interface itself is a boundary | `Feed` |

Rules that make them fit: **a port is owned by the component that calls it** (the consumer states the contract it needs, as a type with laws; any implementation that meets the laws is correct, and the component's theorems hold for all of them), and shared data lives in vbm-work, which depends on nothing. A gateway or an interface is mostly a boundary: what is verified is what it must do, not the channel's own protocol. The assembly proves no new fact about a component; what holds of the whole is a theorem over the composed specifications.

**Ports** (each a contract in the spec, one reference implementation, generated conformance vectors; the package
names no concrete backend):
- Orchestrator: `Agent` (run a role with instructions and tools, get a typed result), `Lander` (check; land),
  `Definitions` (read the principles, the reviewers, the checks), `Evidence` (keep what a run produced), `Clock`.
- Dispatcher: `Queue` (claim, acknowledge, heartbeat), `Host` (capacity and load), `Orchestrator` (Task to Outcome),
  `Admission` (money ceiling), `Clock`.

**Theorems the specs must carry** (illustrative, final list written with the spec):
- A change lands only if the checks passed on the final tree AND the last review round had no `fix` finding.
- An unreviewed change never lands; an unreachable reviewer ends in a typed block, never a landing.
- Every task ends in exactly one typed outcome; the cycle terminates under the fuse.
- The dispatcher never exceeds the host's capacity; an item is held by at most one dispatcher (the lease).
Each conditional theorem carries a non-vacuity witness.

## 5. Dependencies and releases

1. **Signed release tags on every package**, existing and new, starting at `v0.1.0`, made by `land-release` (vbm-land
   v0.10.0), whose message records the tree hash. A tag is cut only on a commit that landed through the lander, and is
   never moved or deleted (a fix is a new version). A pin is the tag + its commit + the tree hash in `.land/pins.lock`,
   added or bumped only by `land-pin vendor` (it refuses an unsigned tag or a tree that does not match the signed hash).
2. **A vendored, offline closure** (proven by the M1 spike): each package vendors its direct dependencies at
   `vendor/NAME`, requires them by path, and refers to their files relative to its own directory. A fresh worktree
   builds with no network and no per-host prep; `land-pin verify` also refuses two different copies of one library in
   the closure.
3. **The registry is the one manifest.** `depends_on` in `registry/*.toml` is checked by a gate that recomputes the
   dependencies from each package's build file and compares (the scorecard's rule: every number recomputed, never
   trusted from a document).
4. **Layering is checked by the import scan**: no cycles; a library imports only the core language and its declared
   dependencies.
5. Each package's proof ledger travels with it; the verified closure is read off the dependency graph.

## 6. The discipline (new guideline: `logic-lives-in-the-spec.md`)

- Logic lives in a Lean specification with a pure core. Shell or Python may only be a BINDING of a port: it moves
  data and effects and decides nothing.
- A new file in `scripts/` requires deleting one.
- A change that adds behaviour lands its specification first, in an application as in a library.
- A temporary patch is allowed only when something is losing money or doing damage now. It is labelled
  `TEMPORARY(until: <what replaces it>)` and listed; the reviewer asks for the list.
- Logic added in shell is a `fix`-level finding for a reviewer.

## 7. Sequence, and what each step deletes (status 2026-11-12)

| step | what | deletes |
|---|---|---|
| M0 (done 2026-11-11) | this design approved; planned registry entries and the guideline land | nothing |
| M1 (done: the vendored closure works, proven by experiment) | the vendored-closure spike (section 5.2) | the per-host `prep` commands, if it works |
| M1b (done: every repository has a signed release) | cut `v0.1.0` on each existing library, after the spike (which may touch their build files); `land-pin` and `land-release` (vbm-land v0.10.0) and their skills are the mechanism | untagged pins |
| M2 (S1 done 2026-11-12) | `vbm-work`: the typed outcome (four tags, fourteen kinds, well-formedness) and the review words, with new proofs; v0.1.0 released and public. Reading the specifications corrected the plan: the run's end machinery and the session's rounds stay in the agent core, `WorkerOutcome` is deleted not extracted (the application's decision 0037). Next: the task, one list of the kinds of block, the application depends on it by expand-and-contract | the application's duplicates, `WorkerOutcome` |
| M3 (S1 done 2026-11-12) | `vbm-orchestrator`: the cycle as a pure state machine, specification first: `step : Config → State → Event → State × List Action`, total, with the money ceiling and a deadline as the only hard stops and a decision model's judgment (a Judge port) deciding whether a failing task is still converging: NO cap on rounds or on revalidations. v0.4.0 released and public: ten claims proved (a task reports at most once; cleans up exactly once on every path; lands only a done-type outcome after validation and review; an unreachable reviewer never lets it land; the worker runs at most `fuse` times whatever the Judge answers; and control never depends on prose: two runs over events that differ only in their words ask for the same actions and end in the same phase) with computed witness runs. Next: the reference model and the conformance vectors | nothing yet |
| M4 (planned) | the orchestrator's interpreter and the application's bindings; the dispatch script calls it | the application's task script; the worker, repair and landing parts of its dispatch script |
| M5 (planned) | `vbm-dispatcher` from the application's pool, claim-plan, lease, heartbeat and host-life specifications; its interpreter | the application's dispatch script |
| M6 (planned) | vocabulary extracted as second consumers appear (judge, money, route, host); the application's agent core extracted LAST | the application's copies |

Each step: specification, proofs, reference model, conformance vectors, release, then the binding. A step is done
when what it replaced is deleted.

## 8. What this does not do

- The boundary stays unverified (starting processes, SQL, HTTP, git); it is small, named, counted in the trust
  ledger, and checked against its contract.
- vbm-land stays shell; it is the process layer.
- Extracting the whole agent core is the largest move and is last.

## 9. Decisions (owner, 2026-11-11)

1. The package names and grouping in section 4: as drafted.
2. Vendored closure for the family, subject to the spike (section 5.2).
3. `vbm-work` is created first.
4. Every package uses release tags (section 5.1).
