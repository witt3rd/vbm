# The trust ledger

What vbm-scoreboard relies on without proof: the facilities outside this repository that every proof and every run assumes. vbm-scoreboard is Lean (specifications, proofs, a reference model) and one command-line tool: it has no C, no foreign function and no vendored dependency, so nothing in its own tree is foreign code; its trusted base is the toolchain that checks and compiles it, the tools its scripts run, and the calls the tool `vbm-scoreboard` (`VbmScoreboardTool/Main.lean`, the boundary) makes to the machine (T3 to T6). `scripts/trust-keys.sh` derives those calls from the tool's source, so a new kind of call cannot be left out unseen.

Entry format: **What** it is; **Enters** where it enters; **Assumes** what we assume of it (the contract); **Test** the test that can fail; **Owner**; **Plan** (verify, replace, sandbox or accept, with a reason); **Covers** the keys it accounts for. `land-lean trust` derives what must be covered from the tree and `.land/lean.conf`, so a trusted thing cannot be left out unseen (vbm-land `docs/lean-gates.md`, guideline `mark-what-is-trusted.md` of the hub).

### T1. The Lean toolchain and the build pins
- **What:** the Lean compiler and kernel, the runtime (`lean.h`, `libleanrt`) and the bundled clang and ld.lld, pinned by `lean-toolchain` and `mise.toml`; `lakefile.lean` drives the build.
- **Enters:** `lean-toolchain`, `mise.toml`, `lakefile.lean`; the kernel checks every proof and the compiler produces every artifact built from this library.
- **Assumes:** the kernel is sound and the compiler is faithful (a miscompile would void what the proofs say about the compiled code): no written contract beyond the Lean project's own documentation.
- **Test:** the axiom gate (`.land/tool/bin/land-lean axiom`, configured by `.land/lean.conf`) fails when any constant depends on an axiom beyond the three standard ones; `lake build` re-checks every proof.
- **Owner:** the owner
- **Plan:** accept because the kernel and the compiler are outside this repository and every claim in it assumes them.
- **Covers:** `file:lean-toolchain` `file:mise.toml` `file:lakefile.lean` `lean-compiler` `lean-runtime` `clang-lld`

### T2. The tools the scripts run
- **What:** `lake` builds the library and its proofs; `mise` provides the pinned toolchain; `git` lists the files the checks read; `python3` runs the trust-ledger checker of the landing tool.
- **Enters:** `scripts/tier1.sh`, `lakefile.lean`.
- **Assumes:** each behaves as documented (a wrong build would be caught by the proofs, a wrong checker by its own negative self-tests): no written contract.
- **Test:** none beyond the tools' own; a wrong build fails the proofs.
- **Owner:** the owner
- **Plan:** accept because they are the host's own tools and nothing from them executes in an artifact.
- **Covers:** `tool:git` `tool:lake` `tool:mise` `tool:python3`

### T3. The file reads and writes of the tool
- **What:** `IO.FS.readFile`, `IO.FS.writeFile`, `IO.FS.rename`, `IO.FS.removeFile` and `System.FilePath.pathExists`, called by `VbmScoreboardTool/Main.lean` on the baseline file and the history file; the operating system's file system under them.
- **Enters:** `VbmScoreboardTool/Main.lean` (`readText`, `writeNew`, `renameTo`, `replaceBoth`).
- **Assumes:** a write to a new file beside the old followed by a rename over it is atomic for each file (POSIX `rename`), and a read returns the bytes last written: no written contract in this repository. The baseline and the history are two files, so they change together by two renames in a row, the first put back if the second fails; a crash or a power loss between the two renames leaves the new baseline with the old history (the one window that is not closed, and that `bank` repairs by recording nothing: the next `bank` finds no floor to move). The text read is decoded by `VbmScoreboardWire` (proved), never trusted.
- **Test:** `scripts/test_tool.sh` (a refused bank changes no file; a bank into an unwritable directory changes nothing; no temporary file is left).
- **Owner:** the owner
- **Plan:** accept because the file system is the host's, and the tool writes no file that the format library did not render.
- **Covers:** `io:files`

### T4. The process spawn of the tool
- **What:** `IO.Process.spawn` of `sh -c CMD` (the provider), its pipe, `Child.tryWait` and `Child.kill`, `IO.Process.output` of `kill -KILL -- -PID` (stopping the provider's process group after the timeout), and `IO.Process.getPID` (the name of a temporary file).
- **Enters:** `VbmScoreboardTool/Main.lean` (`runProvider`, `stopProvider`, `replaceBoth`).
- **Assumes:** `sh` runs the command it is given and reports its exit code truly; the provider's standard output is its protocol and nothing else (its standard error goes to the caller's); `setsid` makes the provider a process group of its own, which `kill` ends with its children. The command is the caller's own: the tool runs what it is told to run and gives it no authority beyond the caller's. What the provider prints is decoded by `VbmScoreboardWire` (proved): a failing, stopped or malformed provider is a typed refusal, never a guess (`VbmScoreboardProofs/Provider.lean`).
- **Test:** `scripts/test_tool.sh` (a provider that exits nonzero, prints a malformed line, repeats a metric, or never exits, and one whose child outlives it).
- **Owner:** the owner
- **Plan:** accept because the provider is the caller's own command by design, and the one named limit (the timeout) bounds what a provider can hold.
- **Covers:** `io:process`

### T5. The clock
- **What:** `Std.Time.Timestamp.now` (the time written to a history line, unless `--at` gives it) and `IO.monoMsNow` (the provider's deadline).
- **Enters:** `VbmScoreboardTool/Main.lean` (`timeOf`, `runProvider`).
- **Assumes:** the clock reads seconds since the epoch and the monotonic clock does not run backwards: no written contract. A wrong clock writes a wrong `at`, and no decision of the library reads it.
- **Test:** `scripts/test_tool.sh` (every case that writes history gives `--at`; the stop after the timeout is measured).
- **Owner:** the owner
- **Plan:** accept because the time is a label on a history line that nothing decides on.
- **Covers:** `io:clock`

### T6. The standard streams of the tool
- **What:** `IO.println` and `IO.eprintln`, the tool's whole output: the typed results of the libraries written as text, and the exit code.
- **Enters:** `VbmScoreboardTool/Main.lean`, with the words in `VbmScoreboardTool/Cli.lean`.
- **Assumes:** the caller reads the exit code (0 done, 1 the scoreboard says no, 2 usage, 3 provider refused, 4 file error): the list in `VbmScoreboardTool/Cli.lean` and README.md.
- **Test:** `scripts/test_tool.sh` (the exact message of each refusal).
- **Owner:** the owner
- **Plan:** accept because the words are a rendering of values the libraries proved, and a caller that parses them depends on the tool's documented exit codes.
- **Covers:** `io:streams`
