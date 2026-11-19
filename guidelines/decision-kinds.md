# Every decision point has a kind, and the kind fixes its evidence

**Every decision point in a system is decidable, judgmental or probabilistic. The specification says which, and the kind fixes the evidence the decision must meet.** Code decides and a model judges; nothing is decided by a heuristic over free text (`no-decisions-from-text.md`). This guideline makes the sorting explicit.

## Why

A judgment dressed as a computation looks exact and is not: a keyword rule that "classifies" a request is a guess with no error bar, and it fails silently in the case nobody tried. A probability dressed as a fact is worse: "the job will finish in an hour" is a claim about the world that nothing in the code can prove. In both cases the gate checks the wrong thing (a proof of a function that was never the right answer) and the reader trusts it. Name the kind and the right evidence follows.

## The rule

| Kind | What it requires | How it is checked | What it may never do |
|---|---|---|---|
| **Decidable**: a function of its inputs; the same inputs always give the same answer | Deterministic code: exact arithmetic; for numerics a stated epsilon with a proved error bound, or interval arithmetic | Proofs, and properties generated from the specification (the family's standard) | Use an unstated tolerance, a clock, a random source or text it must interpret |
| **Judgmental**: no function defines the right answer; a judge must decide | A decision model (it returns typed answers with probabilities: a choice among options, the probability that a condition holds, a position on an ordered scale) or a language model that gives a typed answer. The answer is data; code turns it into the decision with a threshold truth table in the specification that fails closed. Each threshold is chosen from a labelled sample for that model | Measured agreement with a written rubric and with human labels; the audit trail records the judge (model and version), the question, the probabilities and the decision | Default on a missing, malformed or below-threshold answer (that is a refusal); reuse a threshold for another model (probabilities do not transfer); let code read the judge's prose |
| **Probabilistic**: the outcome is uncertain; the answer is a distribution | Informed priors or Bayesian updating, with the prior and its source recorded | Calibration and proper scoring rules against what happened, and a track record; not proof | Report a point value as a fact, or hide the prior |

## Subtleties

- A probabilistic answer computed by deterministic code is still computed by decidable code. What is probabilistic is its input (the prior) and the claim it makes about the world. Prove the update; score the forecast.
- One component can hold several kinds: a number is decidable, the words around it are judgmental. Label each decision point, not each component.
- A judgment's typed probability is itself a probabilistic output, so its calibration is checked like any other: of the answers given at 0.8, about eight in ten should be right.

## How the specification marks the kind

Each decision point carries a label in the specification, next to its definition: `DECISION(kind: decidable)`, `DECISION(kind: judgmental, judge: NAME, sample: ID)` or `DECISION(kind: probabilistic, prior: SOURCE)`. A gate would derive the decision points from the tree (every definition that returns a choice, a refusal or a branch of the step function) and count those with no label, or with a label missing the field its kind needs (a judgmental point with no threshold table or no sample, a probabilistic one with no prior). The count may only fall. This guideline does not build that gate.

## How it fits the others

- `no-decisions-from-text.md`: the judgmental kind is how text-shaped questions get decided; the model reads the prose, code reads only the typed answer.
- `logic-lives-in-the-spec.md`: the truth table, the thresholds and the label are in the specification, never in a script.
- `boundary-never-decides.md`: the boundary carries the question to the judge and the answer back; it never applies a threshold.
- `mark-what-is-trusted.md`: a judge is a trusted component. It is named in the ledger with its agreement and calibration numbers, and a prior is a named assumption.
- `spec-first.md`: the label, the truth table and the evidence plan land before the code that asks the judge.

## Examples

- **Judgmental.** Route a request to one of three queues. A decision model returns a probability for each queue. The specification's truth table sends it to a queue only if that queue's probability is at least its threshold and the runner-up is below a second one; anything else, and any missing or malformed answer, is a refusal that goes to a person. The thresholds come from a labelled sample for that model; changing the model means measuring again.
- **Decidable.** Settle an account between parties: sum integer amounts in the smallest unit, split a remainder by a stated rule, and prove that the parts add up to the total and that the same ledger gives the same split. No model, no tolerance.
- **Probabilistic.** Forecast next week's load. Start from a stated prior (last quarter's weekly counts, recorded as the source), update it with each week's count, and report an interval. The update is proved; the forecast is scored against what happened, and the interval's coverage is tracked.

## What this does not claim

It does not say judgments are reliable or forecasts are right. It says what evidence makes each usable: a proof for a function, measured agreement and a fail-closed table for a judge, calibration and a track record for a forecast. Without that evidence the decision point is unmarked, and an unmarked one is a defect.
