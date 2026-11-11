# Logic lives in the specification

Every decision the system makes is in a Lean specification with a pure core: a step function from a state and an event to a new state and a list of effects. Shell, Python and glue code may only be a binding of a port: they move data and perform effects, and decide nothing. If a script branches on what a result means, the branch belongs in the spec.
A new file in `scripts/` requires deleting one. A change that adds behaviour lands its specification first. A temporary patch is allowed only when something is losing money or doing damage now; label it `TEMPORARY(until: what replaces it)` and list it.
Logic added in shell is a `fix`-level finding for a reviewer.
