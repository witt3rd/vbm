import VbmProbProofs.Prob.Bayes
import VbmProbProofs.Scaled
import VbmProbProofs.Apportion
import VbmProbProofs.Dist.Quantile
import VbmProbProofs.Dist.Mixture
import VbmProbProofs.Dist.Map
import VbmProbProofs.Dist.Condition
import VbmProbProofs.Dist.Scaled
/-! # The known-answer vectors of `docs/spec.md`, each a proved `example`

Every vector of the specification states its exact result and is checked by the kernel (`decide +kernel`), or, where a sort or the largest-remainder order is
involved, by `simp` through `List.mergeSort` (which is irreducible: the kernel is never asked to run it by `decide`). `A` is the distribution 100 ↦ 1/4, 200 ↦ 1/2, 300 ↦ 1/4
and `B` is 200 ↦ 1/2, 300 ↦ 1/2 (keys `Int`, `Limits.default`). Results that carry a `Prob` or a `Dist` are compared through their exact values (`pv`, `dv`),
because a proof field has no equality to decide. -/
namespace VbmProb
namespace Vectors

open Dist

/-- A refusal or a value, as a `Sum` (which has a decidable equality): the form a vector is stated in. -/
def res {ε α : Type} (e : Except ε α) : Sum ε α :=
  match e with
  | .error x => .inl x
  | .ok a => .inr a

/-- A probability result by its exact value. -/
def pv (e : Except Refusal Prob) : Sum Refusal Rat := res (e.map (·.val))

/-- A distribution result by its atoms with exact values. -/
def dv {α : Type} [Key α] (e : Except Refusal (Dist α)) : Sum Refusal (List (α × Rat)) :=
  res (e.map (fun d => d.atoms.map (fun a => (a.1, a.2.val))))

/-- A successful distribution result is its atoms with exact values. -/
theorem dv_ok {α : Type} [Key α] (d : Dist α) : dv (.ok d) = .inr (d.atoms.map (fun a => (a.1, a.2.val))) := rfl

/-- A scale result by its unit count. -/
def sv (e : Except Refusal Scale) : Sum Refusal Nat := res (e.map (·.n))

/-- A literal scale (the positivity is decided). -/
def sc (n : Nat) (h : 0 < n := by decide) : Scale := ⟨n, h⟩

local macro "vec" : tactic => `(tactic| decide +kernel)

/-- Evaluate a vector that goes through `List.mergeSort` (irreducible): `simp` unfolds the sort on a small literal, the kernel decides the rest. -/
local macro "vsort" : tactic =>
  `(tactic| (simp [VbmProb.apportion, VbmProb.Apportion.units, VbmProb.Apportion.floorAt, VbmProb.Apportion.chosen, VbmProb.Apportion.order,
    VbmProb.Apportion.extra, VbmProb.Apportion.before, VbmProb.Apportion.remAt, List.mergeSort, List.range_succ, res]))

/-! ## Probability -/

theorem prob_01 : pv (Prob.make (1/2)) = .inr (1/2) := by vec
theorem prob_02 : pv (Prob.make 0) = .inr 0 := by vec
theorem prob_03 : pv (Prob.make 1) = .inr 1 := by vec
theorem prob_04 : pv (Prob.make (-1/2)) = .inl (.belowZero (-1/2)) := by vec
theorem prob_05 : pv (Prob.make (3/2)) = .inl (.aboveOne (3/2)) := by vec
theorem prob_06 : pv (Prob.ofFrac 1 0) = .inl .denominatorZero := by vec
theorem prob_07 : pv (Prob.ofFrac 5 4) = .inl (.aboveOne (5/4)) := by vec
theorem prob_08 : pv (Prob.ofFrac 1 4) = .inr (1/4) := by vec
theorem prob_09 : (Prob.complement (pr (1/4))).val = 3/4 := by vec
theorem prob_10 : (Prob.mul (pr (1/2)) (pr (1/3))).val = 1/6 := by vec
theorem prob_11 : pv (Prob.add (pr (1/2)) (pr (1/2))) = .inr 1 := by vec
theorem prob_12 : pv (Prob.add (pr (2/3)) (pr (2/3))) = .inl (.sumExceedsOne (4/3)) := by vec
theorem prob_13 : pv (Prob.bayes (pr (1/100)) (pr (99/100)) (pr (5/100))) = .inr (1/6) := by vec
theorem prob_14 : pv (Prob.bayes (pr (1/2)) (pr 0) (pr 0)) = .inl .zeroEvidence := by vec
theorem prob_15 : pv (Prob.bayes (pr (1/2)) (pr 1) (pr 0)) = .inr 1 := by vec
theorem prob_16 : pv (Prob.bayes (pr (1/3)) (pr (1/2)) (pr (1/2))) = .inr (1/3) := by vec
theorem prob_17 : pv (Prob.conditional (pr (1/4)) (pr (1/2))) = .inr (1/2) := by vec
theorem prob_18 : pv (Prob.conditional (pr (3/4)) (pr (1/2))) = .inl .jointExceedsMarginal := by vec
theorem prob_19 : pv (Prob.conditional (pr 0) (pr 0)) = .inl .zeroMarginal := by vec

/-! ## Fixed point -/

theorem fixed_01 : toScaled (sc 1000000) (pr (1/3)) = 333333 := by vec
theorem fixed_02 : toScaled (sc 1000000) (pr (2/3)) = 666667 := by vec
theorem fixed_03 : toScaled (sc 1000000) (pr 0) = 0 := by vec
theorem fixed_04 : toScaled (sc 1000000) (pr 1) = 1000000 := by vec
theorem fixed_05 : toScaled (sc 1000000) (pr (1/2000000)) = 1 := by vec
theorem fixed_06 : toScaled (sc 10) (pr (1/3)) = 3 := by vec
theorem fixed_07 : toScaled (sc 1) (pr (1/2)) = 1 := by vec
theorem fixed_08 : toScaled (sc 1) (pr (1/4)) = 0 := by vec
theorem fixed_09 : pv (ofScaled (sc 1000000) 250000) = .inr (1/4) := by vec
theorem fixed_10 : pv (ofScaled (sc 1000000) 1000001) = .inl (.scaledAboveScale 1000001 1000000) := by vec
theorem fixed_11 : pv (ofScaledInt (sc 10) (-1)) = .inl (.belowZero (-1/10)) := by vec
theorem fixed_12 : pv (ofScaledInt (sc 10) 11) = .inl (.aboveOne (11/10)) := by vec
theorem fixed_13 : sv (Scale.make 0 Limits.default) = .inl .zeroScale := by vec
theorem fixed_14 : sv (Scale.make (10 ^ 18 + 1) Limits.default) = .inl (.scaleTooLarge (10 ^ 18 + 1) (10 ^ 18)) := by vec

/-! ## Largest remainder -/



theorem apportion_01 : res (apportion 10 [1, 1, 1]) = .inr [4, 3, 3] := by vsort
theorem apportion_02 : res (apportion 10 [1, 2, 4]) = .inr [1, 3, 6] := by vsort
theorem apportion_03 : res (apportion 10 [1, 2, 1]) = .inr [3, 5, 2] := by vsort
theorem apportion_04 : res (apportion 1000 [3, 8, 5]) = .inr [188, 500, 312] := by vsort
theorem apportion_05 : res (apportion 1000000 [1, 1, 1]) = .inr [333334, 333333, 333333] := by vsort
theorem apportion_06 : res (apportion 5 [0, 1]) = .inr [0, 5] := by vsort
theorem apportion_07 : res (apportion 2 [1, 1, 1]) = .inr [1, 1, 0] := by vsort
theorem apportion_08 : res (apportion 4 [1, 2, 1]) = .inr [1, 2, 1] := by vsort
theorem apportion_09 : res (apportion 10 [0, 0]) = .inl .zeroTotalWeight := by vsort
theorem apportion_10 : res (apportion 10 []) = .inl .zeroTotalWeight := by vsort

/-! ## Distributions -/

theorem dist_01 : dv (Dist.make Limits.default [((1 : Int), pr (1/2)), (1, pr (1/2))]) = .inl (.keysNotIncreasing 1) := by vec
theorem dist_02 : dv (Dist.make Limits.default [((2 : Int), pr (1/2)), (1, pr (1/2))]) = .inl (.keysNotIncreasing 1) := by vec
theorem dist_03 : dv (Dist.make Limits.default [((1 : Int), pr (1/2))]) = .inl (.atomSumNotOne (1/2)) := by vec
theorem dist_04 : dv (Dist.make Limits.default ([] : List (Int × Prob))) = .inl .emptyDist := by vec
theorem dist_05 : dv (Dist.make Limits.default [((1 : Int), pr 0), (2, pr 1)]) = .inl (.zeroAtom 0) := by vec
theorem dist_06 : dv (Dist.make Limits.default [((100 : Int), pr (1/4)), (200, pr (1/2)), (300, pr (1/4))]) =
    .inr [(100, 1/4), (200, 1/2), (300, 1/4)] := by vec
theorem dist_07 : dv (Dist.make Limits.default [((100 : Int), pr (1/4)), (200, pr (1/2)), (300, pr (1/4))]) =
    dv (.ok distA) := by vec

theorem dist_08 : (distA.cdf 99).val = 0 := by vec
theorem dist_09 : (distA.cdf 100).val = 1/4 := by vec
theorem dist_10 : (distA.cdf 150).val = 1/4 := by vec
theorem dist_11 : (distA.cdf 200).val = 3/4 := by vec
theorem dist_12 : (distA.cdf 300).val = 1 := by vec
theorem dist_13 : (distA.cdf 1000).val = 1 := by vec

theorem dist_14 : res (distA.quantile (1/1000)) = .inr 100 := by vec
theorem dist_15 : res (distA.quantile (1/4)) = .inr 100 := by vec
theorem dist_16 : res (distA.quantile (1/3)) = .inr 200 := by vec
theorem dist_17 : res (distA.quantile (3/4)) = .inr 200 := by vec
theorem dist_18 : res (distA.quantile (4/5)) = .inr 300 := by vec
theorem dist_19 : res (distA.quantile 1) = .inr 300 := by vec
theorem dist_20 : res (distA.quantile 0) = .inl (.levelNotPositive 0) := by vec
theorem dist_21 : res (distA.quantile (-1/2)) = .inl (.levelNotPositive (-1/2)) := by vec
theorem dist_22 : res (distA.quantile (11/10)) = .inl (.levelAboveOne (11/10)) := by vec

theorem dist_23 : ratA.mean = 200 := by vec
theorem dist_24 : ratB.mean = 250 := by vec

theorem dist_25 : dv (mixture Limits.default (pr (1/2)) distA distB) = .inr [(100, 1/8), (200, 1/2), (300, 3/8)] := by vec
theorem dist_26 : dv (mixture Limits.default (pr (1/4)) distA distB) = .inr [(100, 3/16), (200, 1/2), (300, 5/16)] := by vec
theorem dist_27 : dv (mixture Limits.default (pr (1/2)) ratA ratB) = .inr [(100, 1/8), (200, 1/2), (300, 3/8)] := by vec
theorem dist_28 : ∀ d : Dist Rat, mixture Limits.default (pr (1/2)) ratA ratB = .ok d → d.mean = 225 := by
  intro d hd; rw [mixture_mean hd]; vec
theorem dist_29 : ∀ d : Dist Rat, mixture Limits.default (pr (1/4)) ratA ratB = .ok d → d.mean = 425/2 := by
  intro d hd; rw [mixture_mean hd]; vec
theorem dist_30 : dv (mixture Limits.default Prob.zero distA distB) = dv (.ok distA) := by vec
theorem dist_31 : dv (mixture Limits.default Prob.one distA distB) = dv (.ok distB) := by vec
theorem dist_32 : res (mixture { Limits.default with maxAtoms := 3 } (pr (1/2)) distA distB4) = .inl (.tooManyAtoms 4 3) := by
  have h : mixture { Limits.default with maxAtoms := 3 } (pr (1/2)) distA distB4 = .error (.tooManyAtoms 4 3) :=
    (mixture_tooManyAtoms_iff (by decide +kernel)).mpr (by decide +kernel)
  rw [h]; rfl

theorem dist_33 : dv (.ok (shift (5 : Int) distA)) = .inr [(105, 1/4), (205, 1/2), (305, 1/4)] := by vec


theorem dist_34 : dv (normalize Limits.default [((1 : Int), (1 : Rat)), (2, -1)]) = .inl (.negativeWeight 1) := by vec
theorem dist_35 : dv (normalize Limits.default [((1 : Int), (0 : Rat)), (2, 0)]) = .inl .zeroTotalWeight := by
  rw [(normalize_zeroTotalWeight_iff (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)]; rfl

/-- `normalize` on weights already in key order, through `canon_of_increasing` (no sort is evaluated). -/
private theorem norm_sorted {α : Type} [Key α] {ws : List (α × Rat)} (hk : (ws.map (·.1)).Pairwise (· < ·))
    (hn : ¬ Limits.default.maxAtoms < ws.length) (hb : ∀ a ∈ ws, a.2.bits ≤ Limits.default.maxBits)
    (hnn : ∀ a ∈ ws, 0 ≤ a.2) (hpos : ∃ a ∈ ws, 0 < a.2) :
    dv (normalize Limits.default ws) = .inr ((ws.filter (fun a => decide (0 < a.2))).map
      (fun a => (a.1, a.2 / ((ws.filter (fun a => decide (0 < a.2))).map (·.2)).sum))) := by
  obtain ⟨d, hd, hv⟩ := normalize_vals hn hb hnn hpos
  rw [hd, dv_ok, hv]
  unfold normWeights
  rw [canon_of_increasing _ hk]

theorem dist_36 : dv (normalize Limits.default [((100 : Int), (1 : Rat)), (200, 2), (300, 1)]) =
    .inr [(100, 1/4), (200, 1/2), (300, 1/4)] := by
  rw [norm_sorted (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem dist_37 : dv (normalize Limits.default [((1 : Int), (1 : Rat)), (2, 1), (3, 1)]) =
    .inr [(1, 1/3), (2, 1/3), (3, 1/3)] := by
  rw [norm_sorted (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem dist_38 : dv (normalize Limits.default [((1 : Int), (0 : Rat)), (2, 3)]) = .inr [(2, 1)] := by
  rw [norm_sorted (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- The unsorted vector with a repeated key: sorted and merged (`simp` through `mergeSort`). -/
theorem dist_39 : dv (normalize Limits.default [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)]) =
    .inr [(1, 1/4), (2, 1/4), (3, 1/2)] := by
  obtain ⟨d, hd, hv⟩ := normalize_vals (lim := Limits.default) (ws := [((3 : Nat), (1 : Rat)), (1, 1), (3, 1), (2, 1)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [hd, dv_ok, hv]
  unfold normWeights canon
  rw [sort_example]
  decide +kernel

/-! ## Map, condition -/

theorem dist_40 : dv (.ok (map (fun k : Int => k / 200) distA)) = .inr [(0, 1/4), (1, 3/4)] := by
  rw [dv_ok]
  have h : (map (fun k : Int => k / 200) distA).atoms.map vals = [(0, 1/4), (1, 3/4)] := by
    rw [map_vals]
    have e : (pushW (fun k : Int => k / 200) distA).mergeSort (fun a b => keyLe a.1 b.1) =
        pushW (fun k : Int => k / 200) distA :=
      List.mergeSort_of_pairwise (by decide +kernel)
    unfold canon
    rw [e]
    decide +kernel
  exact congrArg Sum.inr h

theorem dist_41 : dv (condition distA (fun k => decide (200 ≤ k))) = .inr [(200, 2/3), (300, 1/3)] := by
  obtain ⟨d', hd, -⟩ := condition_core (d := distA) (e := fun k => decide (200 ≤ k)) (by decide +kernel)
  rw [hd, dv_ok]
  have h2 : d'.atoms.map (fun a => (a.1, a.2.val)) = _ := condition_vals hd
  rw [h2]
  decide +kernel

theorem dist_42 : dv (condition distA (fun k => decide (300 < k))) = .inl .nullEvent := by
  rw [condition_nullEvent (by decide +kernel)]; rfl

/-! ## Distributions at a scale -/

private theorem weightsA : scaledWeights distA = [1, 2, 1] := by
  unfold scaledWeights commonDen distA pr
  decide +kernel

local macro "units_eval" : tactic =>
  `(tactic| simp [VbmProb.Apportion.units, VbmProb.Apportion.floorAt, VbmProb.Apportion.chosen, VbmProb.Apportion.order,
    VbmProb.Apportion.extra, VbmProb.Apportion.before, VbmProb.Apportion.remAt, List.mergeSort, List.range_succ])

theorem scaled_01 : Dist.toScaled (sc 1000000) distA = [(100, 250000), (200, 500000), (300, 250000)] := by
  unfold Dist.toScaled
  rw [weightsA]
  show List.zip [100, 200, 300] (Apportion.units 1000000 [1, 2, 1]) = _
  units_eval

private theorem weightsThirds : scaledWeights distThirds = [1, 1, 1] := by
  unfold scaledWeights commonDen distThirds pr
  decide +kernel

theorem scaled_02 : Dist.toScaled (sc 1000000) distThirds = [(1, 333334), (2, 333333), (3, 333333)] := by
  unfold Dist.toScaled
  rw [weightsThirds]
  show List.zip [1, 2, 3] (Apportion.units 1000000 [1, 1, 1]) = _
  units_eval

private theorem ofScaled_ten_ok : ∃ d : Dist Nat, Dist.ofScaled Limits.default (sc 10) [(1, 4), (2, 3), (3, 3)] = .ok d :=
  (Dist.ofScaled_ok_iff _ _ _).mpr ⟨by decide, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem scaled_03 : dv (Dist.ofScaled Limits.default (sc 10) [((1 : Nat), 4), (2, 3), (3, 3)]) =
    .inr [(1, 2/5), (2, 3/10), (3, 3/10)] := by
  obtain ⟨d, hd⟩ := ofScaled_ten_ok
  rw [hd, dv_ok, Dist.ofScaled_vals hd]
  decide +kernel

theorem scaled_04 : dv (Dist.ofScaled Limits.default (sc 10) [((1 : Nat), 4), (2, 3)]) = .inl (.scaledSumNotScale 7 10) := by
  rw [Dist.ofScaled_sumNotScale (by decide)]; rfl

end Vectors
end VbmProb
