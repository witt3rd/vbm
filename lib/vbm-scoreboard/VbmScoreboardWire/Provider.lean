import VbmScoreboardWire.Format
/-! # The provider's outcome

A provider is a command; what the tool saw of it is an `Outcome`: it ended with an exit code and printed a text, or it was stopped after a limit of seconds. `readProvider` is the whole rule: the text is read as the provider protocol ONLY when the exit code is 0; a nonzero exit or a stop is refused whatever was printed (a failed provider's partial output is never a reading); a text that does not decode is the wire's own typed refusal. Proved in `VbmScoreboardProofs.Provider`. -/
namespace VbmScoreboardWire

open VbmScoreboard (Reading)

/-- What the tool saw of a provider. -/
inductive Outcome where
  | exited (code : Nat) (out : String)
  | timedOut (seconds : Nat)
  deriving DecidableEq, Repr

/-- Why a provider's outcome was refused. -/
inductive ProviderRefusal where
  | failed (code : Nat)
  | timedOut (seconds : Nat)
  | malformed (r : Refusal)
  deriving DecidableEq, Repr

/-- The readings of a provider's outcome. -/
def readProvider : Outcome → Except ProviderRefusal (List Reading)
  | .timedOut s => .error (.timedOut s)
  | .exited 0 out =>
    match decodeReadings out with
    | .ok rs => .ok rs
    | .error r => .error (.malformed r)
  | .exited (c + 1) _ => .error (.failed (c + 1))

end VbmScoreboardWire
