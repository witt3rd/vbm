# Code placement: core first, then the family, then the product

Independent agents working in parallel reinvent the same small things, because nothing tells them not to and no gate can see it. One sweep, after a single afternoon of parallel work on a few repositories, found 71 names defined in more than one of them, a rational-number type in three places, and ten hand-written sorts in one repository, while the proof assistant's own core already ships exact rationals and a verified merge sort with its lemmas, and the standard library ships calendar dates. Every copy is trusted code, a surface to prove or to attack, and a place for behaviour to drift. Before writing a definition, ask three questions, in this order.

| # | Question | If yes | Example |
|---|----------|--------|---------|
| 1 | Does the language's core or standard library already provide it? | USE it and prove only what is missing on top. Never reimplement. | Exact rationals, a verified sort, calendar dates: import them and prove only the extra property you need. |
| 2 | Is it GENERAL, useful unchanged to another product? | It belongs to the family. Look in the registry first and DEPEND on what exists (vendored and pinned, see `vendor-and-pin.md`). If nothing exists, incubate it locally, marked in its docstring as a candidate library, until its first stable point, then extract it. | A parser for a wire format, a bounded queue, a time-window type. |
| 3 | Otherwise it is SPECIFIC. | It stays in the product, factored into specification and theory. | The rule that decides when this product retries a job. |

A production library that imports only the core has the core as its whole world. Its proofs, and a product's specifications, may import the standard library.

## The rule of two

A general thing defined in a SECOND repository is a defect on arrival. That is the moment to extract it into a library, or to use the core if question 1 now answers yes. Do not wait for a third copy: the second one is the cheapest to remove and the first time anyone can see the duplication.

## Who decides generality

Generality is a judgment (see `decision-kinds.md`): a person makes it, or a decision model whose typed answer a gate turns into a decision. Part of it is decidable, and that part is a gate:
- no private name in a library (the public lint);
- no import of a product module by a library;
- the sweep: the same top-level name defined in two repositories.

## What a gate can and cannot check

A duplicated-definitions sweep counts top-level names defined in more than one repository of the family, and reports the number and the names. It is a candidate card metric (not built). It sees a copy that kept its name; it cannot see one that was renamed, written differently, or written for a different type, and it cannot say whether a shared name is general or a coincidence. A name flagged twice is a question for the judgment above, not a verdict. Nothing a gate sees tells you that the core already had it: question 1 is a habit of looking, and the rule is written down so that the agent looks.

## Failure modes

- **A micro-library for three theorems over the core.** A repository costs a release, a pin and a gate. It is worth it when there is a second consumer, or a non-trivial adapter (code that bridges the core's form to the one the family needs). Without either, the theorems stay incubated in their first consumer.
- **Extracting too early.** A thing still changing is incubated, not extracted; extract at its first stable point.
- **Calling everything general.** A product that pushes its specific rules into the family makes every library depend on one product's decisions. A library never imports a product.
- **Reimplementing for a small gap.** If the core is almost right, use it and prove the missing part on top; a copy that differs in one case is a worse trusted base than a lemma.

## What this does not claim

It does not say that duplicates are always wrong: a deliberate second implementation, such as a reference for differential testing, is a decision to record, not a defect. It does not say where the line between general and specific falls; that is a judgment, and the sweep only finds candidates. It does not say that a library is better than a local copy before there is a second user.
