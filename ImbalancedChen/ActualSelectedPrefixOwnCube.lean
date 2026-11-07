import ImbalancedChen.ActualSelectedPrefixCapSelector
import ImbalancedChen.FirstExitFrontierAdmission
import ImbalancedChen.ActualFrozenOwnCubeDensity

/-!
# Actual selected-box updates of ordinary upper and lower densities

The parent is the actual ordinary parity-safe policy at the old constant
level. Its complete prefix admissibility is proved from its recursion.
The replacement level is the concrete finite box selector on the prime
history. Thus neither inherited validity nor level monotonicity is an
external hypothesis in these two density-difference identities.

All next candidates of the common parent frontier remain in the sum,
with both strict own-cube gates. The identities do not assert positivity
of the difference or evaluate its limiting prefix integral.
-/

namespace ImbalancedChen

noncomputable section

/-- Change the level at the selected rank's own admission test, retaining
the ordinary parent through the preceding rank. -/
def actualSelectedPrefixSplicePolicy {d : ℕ} (lower : Bool) (N : ℝ)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy (d - 1)
    (ordinaryParityRosserPolicy lower (N ^ (old : ℝ)))
    (frozenParityRosserPolicy lower d (actualSelectedPrefixLevel N I old nu a b m J))

/-- The exact actual-prime double sum, before any limiting estimate.
The old gate is retained even for candidates rejected by that gate. -/
def actualSelectedPrefixOwnCubeSum {d : ℕ} (lower : Bool) (N cap : ℕ)
    (z : ℝ) (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) : ℝ :=
  ((firstExitDepthFrontier (d - 1)
    (ordinaryParityRosserPolicy lower ((N : ℝ) ^ (old : ℝ)))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap 0 z)).map (fun frontier =>
      ((firstExitNextSelectionCandidates (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining).map
        (fun candidate =>
          (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
            (actualOwnCubeGatedMinusDensity N cap
                (actualSelectedPrefixLevel (N : ℝ) I old nu a b m J)
                candidate.selectedPrefix -
              actualOwnCubeGatedMinusDensity N cap
                (fun _ => (N : ℝ) ^ (old : ℝ)) candidate.selectedPrefix))).sum)).sum

private theorem actual_constantFrozen_parent_density
    (lower : Bool) (k N cap : ℕ) (z Q : ℝ) (hQ : 1 < Q)
    (hzQ : lower = true → z ≤ Q) :
    firstExitRetainedPolynomial
      (firstExitDepthSplicePolicy k (ordinaryParityRosserPolicy lower Q)
        (frozenParityRosserPolicy lower k (fun _ => Q)))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z) =
        if lower then actualSmallRosserMinusDensity N cap z Q
        else actualSmallRosserPlusDensity N cap z Q := by
  change firstExitRetainedPolynomial
    (firstExitDepthSplicePolicy k (ordinaryParityRosserPolicy lower Q)
      (ordinaryParityRosserPolicy lower Q)) _ _ _ _ _ = _
  rw [firstExitDepthSplicePolicy_self]
  exact firstExitRetainedPolynomial_ordinaryParityRosser_eq_actualDensity lower N cap z Q hQ hzQ

/-- Upper fifth-own-cube saving from the actual ordinary upper density.
Only the stored box checks and the positive old exponent are inputs;
the parent prefix tests and the comparison of actual levels are proved. -/
theorem actualSelectedPrefix_upper_five_saving
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) (I : Finset (Fin 5))
    (old nu a b : ℚ) (hold : 0 < old) (m : ℕ)
    (J : Finset (Fin 5 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    actualSmallRosserPlusDensity N cap z ((N : ℝ) ^ (old : ℝ)) -
      firstExitRetainedPolynomial
        (actualSelectedPrefixSplicePolicy false (N : ℝ) I old nu a b m J)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z) =
      actualSelectedPrefixOwnCubeSum false N cap z I old nu a b m J := by
  have ho : (0 : ℝ) < old := by exact_mod_cast hold
  have hQ : 1 < (N : ℝ) ^ (old : ℝ) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hN ho
  have heq := actual_frozen_upper_five_ownCube_saving
    (ordinaryParityRosserPolicy false ((N : ℝ) ^ (old : ℝ)))
    (fun _ => (N : ℝ) ^ (old : ℝ))
    (actualSelectedPrefixLevel (N : ℝ) I old nu a b m J) N cap z
    (fun frontier hf => actualPrimeFrontier_ordinaryParityRosser_admissible
      false _ hQ 4 N cap z (by simp) _ frontier hf)
    (fun _ _ candidate _ => actualSelectedPrefixLevel_ge_old
      (N : ℝ) hN I old nu a b m J hchecks candidate.selectedPrefix)
  rw [actual_constantFrozen_parent_density false 4 N cap z _ hQ (by simp)] at heq
  simpa only [Bool.false_eq_true, if_false, actualSelectedPrefixSplicePolicy,
    actualSelectedPrefixOwnCubeSum] using heq

/-- Lower fourth-own-cube restoration from the actual ordinary lower
density. The lower first-prime range is the explicit cutoff `z<=N^old`. -/
theorem actualSelectedPrefix_lower_four_restoration
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) (I : Finset (Fin 4))
    (old nu a b : ℚ) (hold : 0 < old) (hz : z ≤ (N : ℝ) ^ (old : ℝ))
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    firstExitRetainedPolynomial
        (actualSelectedPrefixSplicePolicy true (N : ℝ) I old nu a b m J)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z) -
      actualSmallRosserMinusDensity N cap z ((N : ℝ) ^ (old : ℝ)) =
      actualSelectedPrefixOwnCubeSum true N cap z I old nu a b m J := by
  have ho : (0 : ℝ) < old := by exact_mod_cast hold
  have hQ : 1 < (N : ℝ) ^ (old : ℝ) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hN ho
  have heq := actual_frozen_lower_four_ownCube_restoration
    (ordinaryParityRosserPolicy true ((N : ℝ) ^ (old : ℝ)))
    (fun _ => (N : ℝ) ^ (old : ℝ))
    (actualSelectedPrefixLevel (N : ℝ) I old nu a b m J) N cap z
    (fun frontier hf => actualPrimeFrontier_ordinaryParityRosser_admissible
      true _ hQ 3 N cap z (fun _ => hz) _ frontier hf)
    (fun _ _ candidate _ => actualSelectedPrefixLevel_ge_old
      (N : ℝ) hN I old nu a b m J hchecks candidate.selectedPrefix)
  rw [actual_constantFrozen_parent_density true 3 N cap z _ hQ (fun _ => hz)] at heq
  simpa only [if_true, actualSelectedPrefixSplicePolicy,
    actualSelectedPrefixOwnCubeSum] using heq

end

end ImbalancedChen
