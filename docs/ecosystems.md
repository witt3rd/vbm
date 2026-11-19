# How other ecosystems design and curate libraries, and what a verified-library family should take from them

Status: a study, not a decision. Nothing here changes a rule; section 13 proposes, section 14 asks.

## 0. The question, and how to read this page

The family must be a cohesive set of FEW libraries, not many. The foundation must not become a dumping ground. `code-placement.md` already says where a definition goes (the language's core, then the family, then the product; a general thing defined twice is a defect). This page asks the next question: how do other ecosystems keep a shared core small, move things into it, size their packages, make many versions agree, and what went wrong when they did not?

Honesty convention. The author wrote this from memory, with no network access to check. A name of a document, process or tool that the author is sure exists is given plainly. Anything specific the author cannot check (a version, a date, who did what, a number, whether a thing is still true) carries **[verify]**. No quotation is given as exact; a well-known saying is named as a saying. No date or version is stated without a mark. Treat every unmarked claim as "believed correct, structural, and cheap to check", and every [verify] as "check before relying on it".

The five questions asked of each ecosystem: (a) SCOPE of the standard or core library and how it is defended against growth; (b) the INCUBATION path; (c) GRANULARITY of a package and the cost of too many or too few; (d) CURATION, and how versions of many pieces are made to agree; (e) documented FAILURE MODES; (f) one LESSON.

## 1. Python

Sources by name: PEP 1 (the PEP process); PEP 3108 (the standard library reorganization for Python 3) [verify number]; PEP 594 ("Removing dead batteries from the standard library"); PEP 632 (deprecating distutils) [verify number]; PEP 453 (bundling the package installer, `ensurepip`) [verify number]; PEP 411 (provisional packages) [verify number]; the PyPI index.

(a) Scope. The standard library is large by design ("batteries included"): networking, archives, a database, a GUI toolkit, date handling. Nothing structural limits growth; the limit is the cost of a maintainer, and the core team's willingness to say no. The saying that the standard library is where a module goes to die is a community saying [verify origin]: a module in the standard library is released only with the interpreter, so it changes at the interpreter's pace, and a better external library (for example for HTTP clients or dates) wins in practice while the old module stays.

(b) Incubation. Third parties publish on PyPI; popular ones are sometimes adopted, by a PEP, into the standard library. A package may enter as "provisional" with a weaker compatibility promise (PEP 411) [verify]. The usual advice for a candidate is to prove itself on PyPI first. Adoption freezes the design and the release cadence.

(c) Granularity. The standard library is one distribution, versioned with the interpreter; PyPI is the opposite end, with a very large number of small projects. Mid-size "distributions" are the norm. Python has no concept of a curated set at the PyPI level: any project may depend on any range of any other.

(d) Curation. The standard library is curated by the core team, with one version per interpreter release. Beyond it, curation is by third parties (distributions, data-science bundles) [verify names]. Version agreement is solved by the installer's resolver at install time, which can and does fail or pick surprising versions; lock files are a tool-level convention.

(e) Failure modes. PEP 594 is the documented case of abandoned batteries: it proposes removing a list of modules (old audio, legacy protocols, obsolete Unix interfaces) because they are unmaintained, untested, or have better external replacements; it states the maintenance cost as the reason. PEP 3108 did the same for Python 3 (merging duplicate modules such as the C and pure versions of one module, dropping platform-specific ones) [verify details]. The removal of `distutils` (PEP 632) shows that a build tool inside the standard library cannot evolve. PyPI has had typosquatting and malicious-package incidents [verify specifics]; a flat open namespace has no review.

(f) Lesson. Everything admitted to the standard library is a promise to maintain it, at the interpreter's pace, for decades. The removal PEP is the evidence that the promise was made too freely; it took years to remove what had been added without a retirement path. Admit with a retirement path written down.

## 2. Rust

Sources by name: the RFC process; the `core`, `alloc` and `std` split of the standard library; the Rust API Guidelines (a checklist); The Cargo Book (features, workspaces); crates.io; `cargo-vet` (Mozilla's audit tool), `cargo-crev`, `cargo-audit` and the RustSec database, `cargo-deny`; blessed.rs (a community-maintained list of recommended crates) [verify its status]; the libs team and the libs-api team; the `rust-lang-nursery` organisation [verify its current role].

(a) Scope. `std` is deliberately small. Things many programs want (random numbers, regular expressions, serialization, date and time, async runtimes) live in crates. The language itself ships three layers: `core` (no allocation, no operating system), `alloc` (allocation), `std` (the operating system). That layering is the most relevant structural fact for a bare-metal family: the foundation is itself tiered by what it assumes of the world. Growth is defended by the RFC process and by the stability promise: anything stabilized in `std` stays.

(b) Incubation. A crate proves itself on crates.io, sometimes under an official organisation (the "nursery") [verify], and sometimes under the rust-lang organisation as a team-owned crate that is not part of `std` (for example the `regex` and `log` crates, and `libc`) [verify membership]. Inclusion in `std` happens by an RFC or a library proposal and first lands as an unstable feature behind a flag, stabilized later [verify the exact process names]. Examples of a crate absorbed after years: lazy statics moved from a macro crate through a general crate into `std` types [verify names and versions].

(c) Granularity. Crates are small to mid-size; large projects are workspaces of many crates (the async runtime is a well-known example, split into a facade crate and subcrates) [verify]. Cargo makes a crate cheap to create and to depend on, which encourages many small crates and deep dependency trees. Features (conditional compilation switches) let one crate stay one unit while its parts are optional; the Cargo Book's rule is that features should be additive, because the build unifies them across the whole tree, so two dependents asking different features get the union.

(d) Curation. crates.io is not curated: it is a flat, first-come namespace. Curation is social (blessed.rs, the API Guidelines, the team-owned crates) and tool-based: `Cargo.lock` pins exact versions; `cargo-vet` records, per crate version, who audited it and to what criteria, and lets one organisation import another's audits; `cargo-deny` enforces policy (licenses, banned crates, duplicates). Version agreement within a tree is by semantic versioning plus a resolver that can include more than one version of the same crate (a semver-incompatible pair is allowed to coexist), which is the source of duplicate-implementation bloat.

(e) Failure modes. Dependency explosion: a small program pulling hundreds of crates is a standing concern, and it is the reason supply-chain tooling exists [verify magnitude]. Duplicate versions of the same crate in one binary. Ecosystem fragmentation when the standard library leaves a gap (several async runtimes with incompatible traits) [verify]. Abandoned crates holding a good name, with no way to take the name back except by a human process.

(f) Lesson. A small foundation with a three-layer structure and an additive-only feature rule scales, but only with supply-chain tooling on top, because small packages multiply the number of things trusted. A trusted base is counted per package (see `trusted-base-is-a-budget.md`): many small libraries are many audits.

## 3. Haskell

Sources by name: the `base` package; the Core Libraries Committee (CLC); the Package Versioning Policy (PVP); Hackage (with revisions of dependency bounds after release); the GHC boot libraries (`containers`, `text`, `bytestring` among them) [verify the exact list]; the Haskell Platform (retired in favour of a toolchain installer) [verify when]; Stackage (curated snapshots, "LTS" and "nightly"); the Foldable/Traversable change to the Prelude, the Applicative-Monad change, and the Semigroup-Monoid change (named proposals) [verify]; alternative preludes such as `relude`, `protolude`, `rio` (they exist; their popularity is not checked).

(a) Scope. `base` holds the Prelude and the central classes and types; it is tied to the compiler release, so a change to `base` is a change to the language's world. The CLC reviews changes to it. Growth is defended by the cost of a breaking change: every library in the ecosystem is affected.

(b) Incubation. Hackage is open; a library becomes de-facto standard by use (`containers`, `text`, `bytestring`, `mtl`, `transformers`). Boot libraries ship with the compiler and so are frozen to its cadence, although some can be reinstalled at a newer version [verify]. The Platform used to bless a set; the community moved to snapshots.

(c) Granularity. `base` was once larger and has been split over the years; the compiler-internal parts were being separated from the public `base` [verify what and when]. Libraries are fine-grained by Hackage convention (one package per idea: `text` for Unicode text, `bytestring` for bytes, `containers` for maps, sets and sequences). Those three names are concepts, not roles, and each has stayed cohesive.

(d) Curation. This is the ecosystem's best-known contribution. A solver working over a free-for-all of version bounds fails in what the community called "dependency hell". Stackage answered with a snapshot: a set of package versions, built and tested together, that a project then names as one thing (an LTS snapshot is bound to a compiler version) [verify]. A package enters a snapshot only if it builds with the rest, a maintainer is reachable, and its bounds are compatible; a failing package is dropped from the next snapshot until fixed. The PVP defines what a major version means, so bounds are meaningful; Hackage allows bounds to be corrected after the fact by revision.

(e) Failure modes. The Prelude debates: because every module imports the Prelude, any change (making list functions work on any container, adding a class to the hierarchy) breaks or confuses the whole ecosystem, and the debate over partial functions such as `head` has never been fully resolved [verify current state]. Result: several alternative preludes, which means duplicate foundations and a split ecosystem. Bound churn and revisions as a maintenance burden. Reinstallable boot libraries causing conflicts between versions in one build [verify].

(f) Lesson. A SET with a gate ("this snapshot builds together") beats a solver over free ranges. And the most imported module is the hardest to change; keep what everything imports tiny and closed.

## 4. Go

Sources by name: the Go 1 compatibility document ("Go 1 and the Future of Go Programs"); the proposal process on the issue tracker; the `golang.org/x` repositories (`x/net`, `x/crypto`, `x/text`, `x/tools`, `x/exp`, and others); the module system with minimal version selection (MVS); `go.sum`, the module proxy and the checksum database; the Go proverbs [verify the source of each saying].

(a) Scope. The standard library is large and practical (HTTP, encoding formats, cryptography, templates, testing), with a promise: programs written for Go 1 keep compiling and working. That promise is the defence against growth in one direction (nothing is removed) and it makes the entry decision heavier: admitting a package is a commitment for good. Newer additions have been made by new import paths with a version suffix rather than by changing the old one (a second major version of a random-number package) [verify which and when].

(b) Incubation. The `x` repositories are the official incubator: maintained by the Go team, outside the compatibility promise, with their own versions. A package can wait there, be adopted into the standard library after a proposal (a context package and the generic slice and map helpers followed this path) [verify which packages and in which release], or stay there for good. `x/exp` is explicitly experimental, with no compatibility promise [verify wording].

(c) Granularity. A package is a directory; a module is a versioned tree of packages. Because Go builds from source and prunes what is not imported, a large module costs little to depend on. Go culture prefers a few cohesive packages with short names. The saying "a little copying is better than a little dependency" (a Go proverb) [verify attribution] expresses the cost accounting: a dependency is a coupling and a trust decision; a few lines of copied code is neither. It is exactly the reverse of the rule of two for tiny things, and consistent with it for large things.

(d) Curation. MVS chooses the minimum version that satisfies all requirements, so a build is reproducible without a lock file and does not drift upward unexpectedly; `go.sum` and the checksum database make a fetched module verifiable by hash [verify the details of the checksum database]. There is no curated set outside the standard library.

(e) Failure modes. The promise freezes mistakes: some old packages and APIs are known warts that cannot be removed, and the fix is a new package beside the old one. The standard library carries parts that few people use. Early dependency management (vendoring tools, a flat GOPATH) was a recognised pain before modules [verify].

(f) Lesson. A written compatibility promise plus an official incubator with no promise is a clean two-tier contract. The tier with a weaker promise must be labelled by its path, so no one depends on it by accident.

## 5. JavaScript and Node

Sources by name: the left-pad incident (March 2016): a tiny package was unpublished from the npm registry and builds broke widely; the registry changed its unpublish policy afterwards [verify details]; the compromise of a widely used package through a transferred maintainership (the event-stream case, 2018) [verify]; the deliberate sabotage of two popular packages by their maintainer (colors and faker, 2022) [verify]; the TC39 stage process (stages 0 to 4); Node's built-in modules and the `node:` import prefix [verify]; the Deno standard library, published as separately versioned modules [verify how].

(a) Scope. The language's standard library is tiny (it is the language and a few built-in objects), and the platform APIs are defined elsewhere. Node's core is a runtime API (files, network, streams, now a test runner and `fetch`) [verify]. The browser's platform is a second, much larger standard library. Growth in core is slow and by consensus; the gap is filled by npm.

(b) Incubation. TC39 moves a language proposal through stages; a library idea moves by popularity on npm, sometimes then absorbed into Node core or the web platform. Deno chose to ship a standard library written in TypeScript, reviewed by the Deno team, versioned separately from the runtime, and stabilised module by module [verify how and when].

(c) Granularity. npm culture drifted to tiny single-function packages ("micro-packages") because publishing is cheap and a package name is a unit of reuse. Each carries a version, a maintainer, an install step and a trust decision. The result is deep, wide dependency trees whose total size nobody reviews.

(d) Curation. npm has none: the lock file pins, and audit tooling flags known vulnerabilities after the fact. Deno's standard library is the counter-example inside this ecosystem: one reviewed set, with an owner.

(e) Failure modes. The left-pad incident (the cost of a trivial dependency owned by one person); maintainer takeover; sabotage by an owner; dependency count as an attack surface; the same function in dozens of packages.

(f) Lesson. The unit of reuse must be bigger than a function. A package is a promise of maintenance, and the promise is not worth its cost for a few lines. For a family: a library needs a purpose that justifies a release, a pin and a gate (the same point `code-placement.md` makes about a micro-library over the core).

## 6. C++

Sources by name: Boost (a collection of peer-reviewed libraries); the Boost formal review (a review manager, a review period, a vote-like decision by the manager) [verify mechanics]; the ISO committee's library working groups (an evolution group and a wording group) and their numbered papers [verify names]; Technical Report 1 (TR1) [verify]; the `bcp` tool that extracts a subset of Boost with its dependencies; header-only libraries; Abseil (a library that follows a "live at head" policy) [verify its policy name]; the ABI stability constraint on standard library implementations.

(a) Scope. The standard library is containers, algorithms, strings, I/O, and, since later revisions, many utilities (smart pointers, threads, filesystem, optional values, variants) [verify which revision]. It grows by committee, by a paper with wording and often an existing implementation. Growth is defended by the committee's slow pace, by the requirement of existing practice, and by the ABI problem: an implementation cannot change a type's layout.

(b) Incubation. Boost is the model incubator: a library is submitted, reviewed in public by the community, accepted by a review manager, and then maintained under a common set of conventions. Many standard components began as Boost libraries (smart pointers, regular expressions, filesystem, optional and variant, among others) [verify the list]. TR1 was the earlier bridge.

(c) Granularity. Boost is a single release of many (well over a hundred) libraries, each a separate directory with its own authors, all released together and tested together [verify count]. Header-only libraries avoid a build step and a binary compatibility question, at the price of compile time and of the one-definition rule's sharp edges [verify]. The `bcp` tool exists because the set is big and users want a subset: evidence that the unit of release was larger than the unit of use.

(d) Curation. A Boost release is a set: every library at a version tested against all others, one release number. Review (before admission) and the release (after) are the curation. Version agreement is solved by having no separate versions.

(e) Failure modes. Libraries that the standard adopted in modified form and then could not be fixed (the standard regular-expression library is known as slow, and fixing it would break the ABI) [verify]. Boost libraries that depend on many others (an inclusion graph so entangled that using one pulls many) [verify]. Standard library parts deprecated and later removed (the original owning smart pointer) [verify].

(f) Lesson. Public peer review before admission and a single tested release afterwards works; admission to the standard then freezes the design, so a library should graduate only after its design has stopped moving. That is the family's "extract at the first stable point".

## 7. Java

Sources by name: the JDK and its modules (the module system, JEP 261, from Project Jigsaw) [verify JEP number]; JEP 320, which removed the Java EE and CORBA modules from the JDK [verify]; incubator modules (`jdk.incubator.*`) and preview features [verify]; the date-time API (JSR 310), which grew out of a popular external library (Joda-Time); Apache Commons (Commons Proper, Sandbox, Dormant) [verify the names of the tiers]; Guava and its `@Beta` annotation; the "bill of materials" (BOM) convention in Maven.

(a) Scope. The JDK is large and compatibility-conservative. The module system exists in part to cut it into pieces so that an application can include only some. Removal of modules (JEP 320) was the first big shedding of weight.

(b) Incubation. External libraries (Joda-Time, Guava collections, Commons) prove designs; the JDK adopts some, often redesigned (java.time). The JDK has its own incubator modules and preview features with an explicit label that the API may change. Guava marks unstable APIs `@Beta`, an in-source label for a weaker contract.

(c) Granularity. Apache Commons has many small components (lang, io, collections, codec, and so on), each an independent release, many with a major-version package rename (`lang3`, `collections4`) so two incompatible versions can coexist in one build [verify]. Guava is one big library. "Utils" libraries are an acknowledged anti-pattern in the culture: a class named `Utils` or `Helper` is the symptom the name `util` invites.

(d) Curation. The BOM: a dependency-management artifact that fixes a version for a list of artifacts, so a user states one version for the whole family; a framework's own BOM is the best-known case [verify which]. It is a set by another name. Commons has a lifecycle for components, with a place for sandboxed and for retired ones [verify].

(e) Failure modes. Grab-bag "utils" classes and libraries, with little cohesion and a dumping role. Dependency conflicts in a build ("jar hell") when two versions of one library are required. A transitively included library with a serious flaw reaching thousands of applications (the Log4Shell case in late 2021) [verify specifics]. Old JDK parts kept for compatibility long after better ones existed (the legacy date classes).

(f) Lesson. The sets that work (a BOM; a platform release) are explicit, and the label for a weaker contract (`@Beta`, incubator, preview) is in the artifact itself. The role name `utils` is where cohesion goes to die.

## 8. Clojure

Sources by name: `clojure.core`; the contrib libraries (`core.async`, `core.logic`, `data.json`, `tools.cli`, `tools.namespace`, and others) that came from an earlier single contrib library split into separate ones [verify when]; the contributor agreement required of contributors to the language and contrib; Clojars (the community repository); `deps.edn` with git dependencies pinned by commit [verify].

(a) Scope. The language ships a small core. Large features arrive as libraries that are separately versioned and not bundled into the language jar. Even `core.async`, a significant feature, is a library. The core's maintainers are conservative about adding and about breaking.

(b) Incubation. A library starts outside; the maintainers of the language host an official set of "contrib" libraries with a defined contribution process (an agreement and a review by the core team) and a shared naming scheme [verify].

(c) Granularity. Focused libraries: each contrib library does one named thing, has its own repository and its own release cycle. The earlier single contrib library had been a grab-bag with uneven quality and dependencies, and was split (the reason for the split as stated here is the author's reading [verify]).

(d) Curation. Contrib libraries are curated by the team; releases are independent and versions are exact; the community has no snapshot set. Version agreement is by convention and by an emphasis on accretion (add, do not break) [verify the maintainers' statements on this].

(e) Failure modes. The single contrib library as a grab-bag (see above). Fragmented community libraries around the same job.

(f) Lesson. A namespace of the shape "category.concept" (`data.json`, `tools.cli`) and a rule that each library has one named job give cohesion cheaply. A caution: `tools` is itself close to a role word; the concept after the dot is what carries the meaning.

## 9. OCaml

Sources by name: `Stdlib` (named `Pervasives` before a later release) [verify]; Base and Core, and the family of libraries from one industrial maintainer, released together under one version series [verify]; Batteries Included, Containers, and ExtLib as earlier or alternative extended libraries; opam and the opam repository (submissions reviewed and run through continuous integration); the `Core_kernel` library later merged into `Core` [verify]; dune.

(a) Scope. The `Stdlib` is small and sparse (for years it lacked functions most programs wanted), which pushed users to extended libraries.

(b) Incubation. External libraries; the stdlib adopts selectively and slowly. Some functions long present in extended libraries have been added to `Stdlib` in later releases [verify examples].

(c) Granularity. Base is a minimal, portable, opinionated replacement; Core is the larger layer above (operating-system dependent). The split is by what each layer assumes of the world: like Rust's `core` and `std`, and it is the strongest lesson on tiering. A very large number of small packages sit above.

(d) Curation. The opam repository with CI acts as a rolling curated index: a submitted package version must build with its declared dependency constraints, and a solver picks a coherent set. One maintainer's libraries share a version series and move as a release set. Those versions agree because one organisation releases them together.

(e) Failure modes. A split ecosystem: the stdlib versus Base versus Batteries, and code that picks one cannot easily share types with code that picked another [verify]. Duplicate foundations: three list modules, three string modules. The opinionated library's shadowing of the stdlib confuses new users.

(f) Lesson. When the foundation leaves gaps, someone fills them, and then the ecosystem has two foundations. A closed foundation must be closed in the right place, and where its scope stops the family must say what to use instead, so no second foundation grows.

## 10. Lean, Batteries and Mathlib

This is the closest to our own world: a proof assistant whose libraries are the product, built with Lake.

Sources by name: Lean core (the `Init` and, in recent versions, `Std` parts) [verify what is in which]; the library formerly called `Std4`, renamed Batteries [verify when]; Mathlib; the `lean-toolchain` file that fixes the compiler version of a project; `lake-manifest.json` (the lock of dependencies by commit); Mathlib's deprecation attribute with a date; Mathlib's environment linters, run by a `#lint` command that came from Batteries (including the checks for a missing doc string and for a non-confluent simp lemma) [verify the list]; the import-minimising tool (`lake exe shake`) [verify]; `exact?`.

(a) Scope. Core is the language's own: types, tactics and data structures the compiler and the elaborator need. Core stays small and very conservative; it changes with each compiler release. Batteries is the layer of general programming data structures and tactics not (yet) in core, kept independent of the mathematical content. Mathlib is the mathematics and the tactics for it. A rule of thumb stated in the community: a thing that does not need mathematical content should be in Batteries or core, not Mathlib [verify as stated policy].

(b) Incubation. A definition or tactic starts in Mathlib or in a project, is generalised, is moved down to Batteries, and sometimes on to core: "upstreaming". Parts of what began in `Std4` and Mathlib's tactics have since moved into core [verify examples]. The route is one-directional on purpose: core depends on nothing above it, Batteries only on core, Mathlib on both.

(c) Granularity. The three layers are separate repositories with their own releases; Mathlib itself is one big repository with thousands of modules, organised by mathematical subject (algebra, order, topology, analysis, and so on). Cheap to add a module; expensive to add a repository. Mathlib's own scale (and the unit of one build, one CI and one version) means a refactor of a foundation module is done by the person making the change, across the whole library, in one commit [verify as practice].

(d) Curation. All the layers must be built with the same compiler version; the `lean-toolchain` file pins it. Mathlib pins exact commits of Batteries and the other dependencies; downstream projects pin Mathlib by commit or tag. There is no version solver in the semantic-versioning sense; the set is the pin [verify]. Review is by maintainers by area; a continuous build is the gate, and a failing change is not merged. A bot bumps the dependencies.

(e) Failure modes. Files called `Basic`, `Defs`, `Lemmas` and `Misc` collect whatever does not fit elsewhere: the module-scale grab-bag, and the community splits them over time [verify as practice]. Duplicate definitions: the same concept defined twice, found and merged by human review; the linters in the tool chain catch name-level problems (a namespace repeated, a missing doc string) and the author knows of no linter that detects a semantic duplicate [verify; if one exists the finding changes]. Deprecated names left in place for months, then deleted by date. Churn: a core change needs matching downstream changes in every layer.

(f) Lesson. A strict downward-only layering (core, Batteries, Mathlib), a toolchain pin shared by the set, a defined route down ("upstreaming"), and dated deprecations are enough to keep the layers coherent; the weak spot is generic file names, which are the role names this page recommends banning.

## 11. Linux distributions

Sources by name: Debian (stable, testing, unstable; Debian Policy; source packages and binary packages; the rule that a package moves from unstable to testing after a waiting period if it introduces no new release-critical bug and its dependencies can be met) [verify the mechanics]; the Debian "orphaned package" and package-removal processes; Fedora (the package review a new package must pass; Rawhide as the development branch; the Fedora change process; the retired Modularity experiment) [verify]; Arch Linux (official repositories plus the user-contributed AUR, with promotion by trusted users) [verify]; Nixpkgs (a single repository whose commit is the set; channels).

(a) Scope. A distribution's scope is "everything people want to install", so scope is not the defence; the defence is the maintainer: a package needs a person responsible for it, and one with none is orphaned and eventually removed.

(b) Incubation. A user repository (the AUR), a development branch (Rawhide, unstable), or a new-package review are the entries. The incubator is by definition less trusted: users must opt in.

(c) Granularity. A source package yields several binary packages (a runtime library, its development files, its documentation) so a user installs only the part wanted. Sonames and transitions: a library's incompatible change forces a coordinated rebuild of all its dependents. Many tiny packages are handled well when the tool manages them; the cost is borne by the distribution's team.

(d) Curation. This is the discipline's centre. A release is a set: every package in it was built and tested against every other, with declared relations between them (depends, breaks, conflicts). A package may migrate to the next stage only if the set still satisfies its constraints. Nixpkgs makes the set literal: one commit is the whole set, and a consumer pins the commit.

(e) Failure modes. Orphaned and unmaintained packages that others depend on. Transitions that stall because one dependent does not rebuild. Dependency hell when a user mixes repositories and the set no longer holds. A user repository flooded with duplicates of the same program.

(f) Lesson. The set is the unit that is released; a piece enters only if the set remains consistent; each piece has an owner; a piece with no owner leaves. These are all decidable, which is why distributions can run them at scale.

## 12. What the ecosystems agree on

| Question | Where they agree | Where they differ |
|---|---|---|
| Scope | The more imported a thing is, the smaller and more closed it should be (Haskell's Prelude, Go's promise, Rust's `std`, Lean's core). | Python and Go keep a large standard library; Rust, Clojure, OCaml keep it small. |
| Incubation | There is a named place with a weaker promise, and a named route out (Go `x`, Boost, Java incubator modules, Batteries, Rust nursery). | Who decides: a committee, a review manager, a maintainer by area. |
| Granularity | Cohesion by concept is what lasts (`text`, `bytestring`, `containers`, `data.json`). Micro-packages and `utils` fail. | How many repositories: Mathlib one big, Clojure many small. Lean's per-module import makes a module cheap and a repository dear. |
| Curation | A set that is built and tested together, with one name (Stackage, Boost, a distribution release, a BOM, Nixpkgs, a toolchain pin). | By solver (Cargo, opam, Python's installers) or by snapshot. |
| Failure | Grab-bags, abandoned batteries, dependency explosions, duplicate foundations. | Whether removal is allowed: Python and Java have done it; Go has promised not to. |

## 13. Recommendations for a verified-library family

The family differs from most of the above in three ways that change the answer. It builds from source with no network, so every dependency is a vendored pin of an exact signed release (`vendor-and-pin.md`); old pins stay buildable forever, so removal never breaks an existing consumer (Go's reason for never removing does not apply). Each library is trusted code that costs a proof budget, so a duplicate is a larger cost than in other ecosystems (`trusted-base-is-a-budget.md`). And the authors are agents working in parallel without remembering each other, so everything that a person would "just know" must be a written rule or a gate.

### 13.1 Tiers and the direction of dependencies

Adopt the layering that Rust (`core`, `alloc`, `std`), OCaml (Base, Core) and Lean (core, Batteries, Mathlib) share: tiers by what a layer assumes, and dependencies only downward. For the family, in order: (0) the language's core and standard library (not ours; question 1 of `code-placement.md`); (1) the foundation, with no dependency but tier 0; (2) libraries, which depend on tiers 0 and 1 and on lower-numbered libraries; (3) vocabulary shared between machines; (4) machines (sans-I/O state machines); (5) assemblies and products. The process tool (the lander) sits beside the tiers and is a dependency of none of them at run time. This matches the existing layering in `family-design.md`; the proposal is to make it a written rule with a tier field in each registry entry. Decidable: the declared tier of each dependency is lower or equal by the rule; no cycle; no library imports a product.

### 13.2 Naming: a concept, never a role

Name a library by the concept it defines (`text`, `bytestring`, `containers`, `data.json`), not by the role it plays for others. Banned as the whole or the main word of a library or a module: `util`, `utils`, `common`, `base`, `misc`, `helpers`, `shared`, `lib`, `tools`, `stuff`, `extras`, and `core` unless the purpose sentence defines it (see 13.3). Files named `Basic`, `Defs`, `Lemmas` and `Misc` in Mathlib show the same risk at module scale: allow them only when the directory has a concept name and the file is the unique root of that concept's definitions. The test for a good name: could you write one sentence of what the library IS that does not use "and" and does not mention who uses it?

### 13.3 A closed-scope foundation

The foundation is a small set, defined by a one-sentence purpose and an explicit admission list, not by "things that are used a lot". Admission rules, borrowed from Rust (small std), Go (a promise), and Haskell (the Prelude lesson): (i) the language's core does not already have it; (ii) at least two libraries in the family use it unchanged (the rule of two, here a hard condition rather than a warning); (iii) it is needed by tier 1 or tier 2 code, not by a single machine or product; (iv) it is proved, with its non-vacuity witnesses, before it is admitted; (v) the purpose sentence names the concept, and the commit that admits it changes the sentence or shows that it already covers it. Anything else stays where it is. The foundation's size is a budget with a recorded ceiling (module count, public names, trusted lines) that can only be raised by a change that says so. Because every change to the foundation re-runs the gate of everything above it (`factor-for-disjointness.md`), the foundation should have the slowest-changing, most-reviewed pieces. If the owner wants the family to name this library `core`, the purpose sentence is what makes it a concept and not a role: Rust's `core` is, in substance, the part of the standard library that needs no operating system [verify wording], which is a closed definition. See open question 1.

### 13.4 Extend an existing library or create one

Default: extend. A new module in an existing library is cheap (Lean imports are per module); a new library costs a repository, a release, a pin, and a gate in every consumer (`code-placement.md`). Create a library only when one of these holds: (i) its purpose sentence is different, and adding it to the existing sentence would need "and"; (ii) its import closure would make an existing library's consumers carry a dependency they do not want (the footprint test, decidable: the new imports would grow some consumer's closure); (iii) it has a second consumer already, or a non-trivial adapter. Features and flags are not used to get granularity: Cargo's rule that features must be additive is a warning that each flag multiplies the cases to prove. Use modules that can be imported alone.

### 13.5 An incubator tier with a weaker contract

Take Go's `x`, Boost's review, Java's incubator and `@Beta`: a labelled place, a weaker promise, and a way out. In the registry: `status = incubating`, readable by every gate. The weaker contract is about STABILITY and REVIEW only: no promise that a minor version keeps the interface; it may be depended on only by tier 2 and above, never by the foundation or by a stable library; it is pinned by exact version in every consumer. The truth contract is not weakened (an unproved escape is still marked in the trust ledger and counted; see open question 3). A time limit applies: an incubating library must graduate, merge into another, or retire within a stated number of set releases; that is a date, so decidable. The existing "incubate locally, marked as a candidate library, extract at the first stable point" (`code-placement.md`) is the zero-th step; the incubator tier is the first step where a second repository already uses it.

### 13.6 A versioned set: a manifest of mutually compatible pins, vendored as one

This is the strongest single idea of the study (Stackage, Boost, a distribution release, Nixpkgs, a BOM, Lean's toolchain pin, a series of one maintainer's OCaml libraries). Define a set as one small file (a manifest) listing, for each member library, its tag, commit and tree hash, plus the language toolchain version, with its own version number. The set is released only when every member builds and passes its gate together at exactly those pins (the set's own gate: a build of all libraries at their pinned versions, one version of each, and each library's declared dependencies satisfied by the set's versions). A consumer vendors the set, not N libraries, and `land-pin verify` already refuses two different copies of one library. A library's new release enters the next set only when the set still holds (Debian's migration rule; Stackage dropping a package that fails). Direction: a library lists its dependencies in the registry and the build file; the set checks that these two agree (the drift that `family-design.md` found). Name one place that holds the manifest (this hub is the candidate) and one version scheme (see open question 4).

### 13.7 Retirement

Because pins keep old versions buildable, retirement is cheap and the family should do it early, unlike Go. A library is retired by: a registry status `retired` with a replacement or a reason; a dated deprecation (as Mathlib's deprecation attribute carries a date) kept for a stated number of set releases; then removal from the set. Triggers that a gate can see: no consumer in the set for a stated number of releases; no release in a stated period; a failing set build that nobody fixed; the same purpose sentence as another library (a duplicate). Python's removal PEP and Java's module removal show the cost of waiting: the longer a thing stays, the more depends on it.

### 13.8 Decidable checks versus judgment

Decidable (each can be a gate, with a negative self-test per `gates-need-negative-self-tests.md`):

| Check | What it counts | Limit |
|---|---|---|
| Orphan modules | A module no other module of the library imports and not declared a public entry point | A fresh library's leaf modules need a declared entry list |
| Purpose sentence with a conjunction | The registry's one-sentence purpose contains `and`, `&`, `plus`, `as well as`, or a comma-separated list | Syntactic; a flagged sentence needs a recorded justification, and "and" can be innocent (`encode and decode` as one concept); not a verdict |
| Same name in two libraries | A top-level name defined in more than one library of the set (the sweep in `code-placement.md`) | Misses a renamed or differently typed copy |
| Role name | A library or module name that is on the denylist of 13.2 | A list; a new role word needs adding |
| Dependency direction | Tier of each dependency, cycles, product imports | Needs the tier field |
| Registry versus build file | Declared dependencies equal actual requires | Already shown to drift |
| Footprint | Import closure of each library, and growth caused by a change | Reports size, not whether the growth is warranted |
| Consumer count | Number of set members that depend on a library | A leaf product is allowed zero |
| Ceiling | Foundation module, name and trusted-line counts against their recorded ceiling | A ceiling is chosen by a person |
| Time limits | Incubating or deprecated past its date | The date is chosen by a person |
| Set consistency | One version per library; every pin resolves; the set builds | Costly; run on a set release, not per commit |

Judgment (a person, or a decision model whose typed answer a gate turns into a decision, per `decision-kinds.md`): whether a thing is general; whether it fits this library's purpose; whether two differently named things are the same concept; whether to extend or create; whether a flagged conjunction is really two ideas; whether a name states a concept; whether an incubating library should graduate. A decidable check cuts the judgment's workload (it lists candidates); it does not replace it. This is the same split `code-placement.md` already makes.

## 14. Open questions for the owner

1. Is `core` a library the family will own, or only the name of the language's core? If owned: its one-sentence purpose, and whether the word is accepted despite the role-name rule (it is the same word as Rust's `core` and Lean's core, but only a closed definition makes it a concept).
2. How few is "few"? A target number of libraries, or a rule such as "a new library needs a second consumer and a different purpose sentence" (13.4) with no number? Does the family prefer one repository with many libraries (Mathlib's way: one version, one gate, cheap modules) or many repositories (Clojure's way)? The existing plan is one repository per library.
3. May an incubating library carry unproved escapes that are marked and counted, or must the truth contract stay whole at every tier? This page assumes the latter.
4. The set: where does the manifest live (this hub), what version scheme does it use (a counter, a date, or semantic), how often is a set released, and does the lander itself belong in it?
5. Existing names that look like roles: is `rt` (the runtime foundation) a concept or a role, and are `work` and `host` concepts? Rename now, or keep and let the purpose sentences decide?
6. Does the language's Batteries layer count as "the language's core" for question 1 of `code-placement.md` (so the family depends on it freely), or is it a dependency to be pinned like any library?
7. Who judges generality: the owner, or a decision model with a rubric and measured agreement? And which of the checks in 13.8 are hard gates from day one and which are reports first, since a gate that has never run cannot be trusted either way?
8. Retirement thresholds: how many set releases without a consumer, and how long a dated deprecation lasts?
9. May an existing product-resident vocabulary be extracted in one step, or only on the second consumer, as `family-design.md` says?

## 15. What this study does not claim

It does not claim that any ecosystem's choice was right; it records what each documented and what went wrong. It was written from memory without a way to check sources, so every unmarked claim is a belief to confirm and every [verify] a known gap. It does not decide the questions of section 14, and it changes no existing rule, gate or layout.
