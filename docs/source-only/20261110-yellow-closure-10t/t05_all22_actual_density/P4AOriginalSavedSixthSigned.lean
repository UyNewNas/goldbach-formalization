import ImbalancedChen.P4AOriginalSavedSixthFrontier
import ImbalancedChen.P4AOriginalFull87OrdinarySignedGain

/-! Exact G4 ordinary raw difference at the frontier of the actual fifth
policy. In every state both caps are compared at its own last prime
and product, with the signed polynomial on the same target-deleted carrier. -/
namespace ImbalancedChen.P4AOriginalSavedSixthSigned
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87DataPolicy (fifthPolicy fifth_even level5Exponent)
open P4AOriginalSavedSixthStage (level fifth_le_level)
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87OrdinarySignedGain (weight)

def pre (p : Fin 6 → ℕ) := (List.ofFn p).reverse
def admitted (n : ℕ) (d : OriginalData) (N cap : ℕ) (z : ℝ) :=
  firstExitAdmittedTuples 6 (fifthPolicy n d (N:ℝ)) (roughPrimeUniverse N cap 0 z)
def old (n : ℕ) (d : OriginalData) (N : ℝ) (p : List ℕ) :=
  level5Exponent n d N (rosserAncestor 5 p)
def tupleResidual (n : ℕ) (d : OriginalData) (N cap : ℕ) (p : Fin 6 → ℕ) :=
  actualPrimeTupleInitialSaving N cap (old n d (N:ℝ) (pre p)) (level n d (N:ℝ) (pre p)) p

theorem parent_refreeze (n : ℕ) (d : OriginalData) (N : ℝ) :
    firstExitDepthSplicePolicy 6 (fifthPolicy n d N)
      (frozenParityRosserPolicy false 6 (fun h => N^old n d N h)) = fifthPolicy n d N := by
  unfold old fifthPolicy
  rw [frozenParityRosserPolicy_nested false 5 6 (by decide)
    (fun h => N^level5Exponent n d N h)]
  exact firstExitDepthSplicePolicy_absorb_later 4 6 (by decide) _ _

theorem rank_six_density (N cap : ℕ) (Q : List ℕ → ℝ) (h : List ℕ) (hl : h.length=6) :
    actualFrozenFrontierDensityTerm false N cap Q h =
      (h.map weight).prod*actualSmallRosserPlusDensity N cap (h.headD 0:ℝ) (Q h/(h.prod:ℝ)) := by
  unfold actualFrozenFrontierDensityTerm
  rw [signedTreeCoefficient_evenListLength_eq_negOnePow,hl]
  norm_num [ordinaryRosserResidualLower,weight]

theorem original_raw_difference_eq_admitted (n : ℕ) (d : OriginalData) (N cap : ℕ) (z : ℝ)
    (hN : 1 ≤ (N:ℝ)) :
    normalize N (raw (fifthPolicy n d (N:ℝ)) N cap 0 z -
      raw (P4AOriginalSavedSixthStage.policy n d (N:ℝ)) N cap 0 z) =
      ∑ p ∈ admitted n d N cap z, (∏ i,weight (p i))*tupleResidual n d N cap p := by
  let S := fifthPolicy n d (N:ℝ)
  let Q := fun h => (N:ℝ)^old n d (N:ℝ) h
  let M := fun h => (N:ℝ)^level n d (N:ℝ) h
  let carrier := roughPrimeUniverse N cap 0 z
  have hold (s) (hs : s∈firstExitDepthFrontier 6 S weight [] true 1 carrier) :
      ordinaryRosserPrefixAdmissible false (Q s.selectedPrefix) s.selectedPrefix :=
    P4AOriginalSavedSixthFrontier.actual_fifth_at_six n d N cap 0 z weight s hs
  have hnew (s) (hs : s∈firstExitDepthFrontier 6 S weight [] true 1 carrier) :
      ordinaryRosserPrefixAdmissible false (M s.selectedPrefix) s.selectedPrefix :=
    ordinaryRosserPrefixAdmissible_mono false _
      (Real.rpow_le_rpow_of_exponent_le hN (fifth_le_level n d (N:ℝ) _)) (hold s hs)
  have hx := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 6 (by decide) S M Q N cap z hnew hold
  change firstExitRetainedPolynomial
      (firstExitDepthSplicePolicy 6 S (frozenParityRosserPolicy false 6 Q)) _ _ _ _ _ -
      firstExitRetainedPolynomial
      (firstExitDepthSplicePolicy 6 S (frozenParityRosserPolicy false 6 M)) _ _ _ _ _ = _ at hx
  dsimp only [S,Q,M] at hx
  rw [parent_refreeze,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
      (fifth_even n d (N:ℝ)) N cap 0 z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
      (P4AOriginalSavedSixthStage.even n d (N:ℝ)) N cap 0 z] at hx
  unfold normalize
  change (raw _ N cap 0 z - raw _ N cap 0 z) * _ / _ = _
  change raw _ N cap 0 z - raw _ N cap 0 z = _ at hx
  rw [hx]
  let states := firstExitDepthFrontier 6 S weight [] true 1 carrier
  let term := fun s : FirstExitDepthState ℕ =>
    actualFrozenFrontierDensityTerm false N cap Q s.selectedPrefix -
      actualFrozenFrontierDensityTerm false N cap M s.selectedPrefix
  have hscale (l : List (FirstExitDepthState ℕ)) :
      (l.map term).sum * Real.log (N : ℝ) / singularSeries N =
        (l.map (fun s => term s * Real.log (N : ℝ) / singularSeries N)).sum := by
    induction l with
    | nil => simp
    | cons s l ih => simp only [List.map_cons, List.sum_cons, add_mul, add_div, ih]
  change (states.map term).sum * _ / _ = _
  rw [hscale]
  rw [← firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 6 S weight carrier
    (roughPrimeUniverse_nodup N cap 0 z) (tupleResidual n d N cap)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hl := firstExitDepthFrontier_selected_length 6 S weight [] carrier true 1 (by simp) s hs
  have hpre : pre (primeHistoryTuple 6 s.selectedPrefix) = s.selectedPrefix :=
    primeHistoryTuple_reverse_ofFn hl
  dsimp only [term]
  rw [rank_six_density N cap Q _ hl,rank_six_density N cap M _ hl]
  simp only [tupleResidual,actualPrimeTupleInitialSaving,hpre,primeHistoryTuple_last (k := 5) hl,
    primeHistoryTuple_prod hl,Q,M,weight]
  ring


end
end ImbalancedChen.P4AOriginalSavedSixthSigned
