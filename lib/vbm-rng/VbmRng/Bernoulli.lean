import VbmRng.Below
/-! # Bernoulli (S8)

`bernoulli num den st` is `true` with the exact probability `num / den`: it draws `u` uniformly below `den` with `uniformBelow` and answers `u < num`. The checks run in order, the first refusal wins: `den = 0`, then `num` outside `[0, den]`, then `den > 2^64`. A draw always consumes one accepted word, also for `num = 0` and `num = den`. The properties B1-B4 are proved in `VbmRngProofs/Bernoulli.lean`. -/
namespace VbmRng

/-- A Boolean that is `true` with probability exactly `num / den`, or a typed refusal. -/
def bernoulli (num : Int) (den : Nat) (st : Stream) : DrawWith Stream Bool :=
  if den = 0 then .error .probabilityDenominatorZero
  else if num < 0 ∨ (den : Int) < num then .error .probabilityOutOfRange
  else if maxBound < den then .error .boundTooLarge
  else
    match uniformBelow den st with
    | .error e => .error e
    | .ok (u, st') => .ok (decide ((u : Int) < num), st')

end VbmRng
