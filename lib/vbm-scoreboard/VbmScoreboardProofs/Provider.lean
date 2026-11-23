import VbmScoreboardWire.Provider
import VbmScoreboardProofs.Wire
/-! # The provider's outcome, proved

* `readProvider_failed`, `readProvider_timedOut`: a provider that exits nonzero or is stopped is refused, whatever it printed (its partial output is never a reading).
* `readProvider_ok`, `readProvider_malformed`: a provider that exits 0 is read as the provider protocol, no other way; a text that does not decode is the wire's own typed refusal. -/
namespace VbmScoreboardWire

theorem readProvider_failed (c : Nat) (out : String) :
    readProvider (.exited (c + 1) out) = .error (.failed (c + 1)) := rfl

theorem readProvider_timedOut (s : Nat) : readProvider (.timedOut s) = .error (.timedOut s) := rfl

theorem readProvider_ok (out : String) (rs : List VbmScoreboard.Reading)
    (h : readProvider (.exited 0 out) = .ok rs) : decodeReadings out = .ok rs := by
  unfold readProvider at h
  cases hd : decodeReadings out <;> simp [hd] at h
  simp [h]

theorem readProvider_malformed (out : String) (r : Refusal) (h : decodeReadings out = .error r) :
    readProvider (.exited 0 out) = .error (.malformed r) := by
  simp [readProvider, h]

example : readProvider (.exited 0 "") = .ok [] := rfl
example : readProvider (.exited 3 "") = .error (.failed 3) := readProvider_failed 2 ""
example : readProvider (.timedOut 5) = .error (.timedOut 5) := readProvider_timedOut 5

end VbmScoreboardWire
