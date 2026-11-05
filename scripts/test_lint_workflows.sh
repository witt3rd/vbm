#!/usr/bin/env bash
# Tier 1: scripts/lint-workflows.py passes the repo's workflows and FAILS on: `with:` under a `run:` step, a step with both/neither of uses/run, no jobs, a job with no steps, broken YAML, no trigger.
set -euo pipefail
export LC_ALL=C
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
python3 scripts/lint-workflows.py >/dev/null && ran_case || { echo "test_lint_workflows: the repo's workflows are invalid" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
neg() { # neg <name> <yaml>
  printf '%s\n' "$2" > "$T/$1.yml"
  if python3 scripts/lint-workflows.py "$T/$1.yml" >/dev/null 2>&1; then echo "test_lint_workflows: '$1' was accepted" >&2; exit 1; fi
}
head='name: x
on: push'
ok="$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0
      - run: true"
printf '%s\n' "$ok" > "$T/ok.yml"; python3 scripts/lint-workflows.py "$T/ok.yml" >/dev/null && ran_case || { echo "test_lint_workflows: a valid workflow was rejected" >&2; exit 1; }
neg with-under-run "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: true
        with:
          fetch-depth: 0"
neg inserted-step "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - name: free disk
        run: true
        with:
          fetch-depth: 0"
neg both "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - uses: x/y@v1
        run: true"
neg neither "$head
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - name: nothing"
neg no-jobs "$head
jobs: {}"
neg no-jobs-key "$head"
neg no-steps "$head
jobs:
  a:
    runs-on: ubuntu-latest"
neg no-trigger "name: x
jobs:
  a:
    runs-on: ubuntu-latest
    steps:
      - run: true"
neg broken-yaml "$head
jobs:
  a: [unclosed"
ran_done test_lint_workflows
echo "test_lint_workflows: ok (valid accepted; 9 invalid shapes each rejected)"
