# Security policy

## Reporting a vulnerability

Please report a vulnerability **privately**: on the repository page open **Security**, then **Report a vulnerability** (GitHub private vulnerability reporting). Do not open a public issue or pull request for it.

Include what you found, the commit, and a way to reproduce it. You will get an acknowledgement within a few days.

## What counts

In scope: a way for a submitted (untrusted) repository to make the scorecard run its code outside the sandbox contract, read a file the adapter did not declare, or write outside the scratch output; a way to make the scorecard print a score that its inputs do not support (a gate that is not shown to fail, a bypass of the protected set); a leak of a secret through a log.

Out of scope: running the scorecard with `--sandbox` omitted on a repository you do not trust (then nothing of the subject executes by design, and metrics that need it say `not-measurable`), and scores of repositories you control.

## Supported versions

The latest commit on `main` only.
