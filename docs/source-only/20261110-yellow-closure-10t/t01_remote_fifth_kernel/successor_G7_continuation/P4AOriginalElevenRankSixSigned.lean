import ImbalancedChen.P4AOriginalElevenAcceptedCaps
import ImbalancedChen.P4AOriginalSavedSixthSigned

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Actual G4→G7 normalized signed difference on the SAME fifth frontier.
Both caps inherit genuine rank-six ordinary admissibility from that
frontier's actual fifth parent. The original last prime and full product
remain in every quotient. This is an exact finite identity, before the
separate normalized prime-limit/payment theorem.
-/
namespace ImbalancedChen.P4AOriginalElevenRankSixSigned
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87DataPolicy (fifthPolicy level5Exponent)
open P4AOriginalFull87OrdinarySignedGain (weight)
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalSavedSixthSigned (pre admitted rank_six_density)

theorem actual_G4_at_six (n : ℕ) (d : OriginalData) (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ)
    (hN : 1≤(N:ℝ)) (s : FirstExitDepthState ℕ)
    (hs : s∈firstExitDepthFrontier 6 (fifthPolicy n d (N:ℝ)) h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^P4AOriginalSavedSixthStage.level n d (N:ℝ) s.selectedPrefix) s.selectedPrefix :=
  ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le hN (P4AOriginalSavedSixthStage.fifth_le_level n d (N:ℝ) _))
    (P4AOriginalSavedSixthFrontier.actual_fifth_at_six n d N cap w z h s hs)

theorem actual_G7_at_six (n : ℕ) (d : OriginalData) (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ)
    (hN : 1≤(N:ℝ)) (s : FirstExitDepthState ℕ)
    (hs : s∈firstExitDepthFrontier 6 (fifthPolicy n d (N:ℝ)) h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^P4AOriginalElevenSixthStage.level n d (N:ℝ) s.selectedPrefix) s.selectedPrefix :=
  ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le hN (P4AOriginalElevenSixthStage.saved_le_level n d (N:ℝ) _))
    (actual_G4_at_six n d N cap w z h hN s hs)

def tupleResidual (n : ℕ) (d : OriginalData) (N cap : ℕ) (p : Fin 6 → ℕ) : ℝ :=
  actualPrimeTupleInitialSaving N cap
    (P4AOriginalSavedSixthStage.level n d (N:ℝ) (pre p))
    (P4AOriginalElevenSixthStage.level n d (N:ℝ) (pre p)) p

/-- No source-licence or frontier-admissibility premise remains: both
are inherited at every actual state from the actual fifth policy. -/
theorem original_G7_raw_difference_eq_admitted (n : ℕ) (d : OriginalData)
    (N cap : ℕ) (z : ℝ) (hN : 1≤(N:ℝ)) :
    normalize N (raw (P4AOriginalSavedSixthStage.policy n d (N:ℝ)) N cap 0 z-
      raw (P4AOriginalElevenSixthStage.policy n d (N:ℝ)) N cap 0 z)=
      ∑ p∈admitted n d N cap z, (∏ j,weight (p j))*tupleResidual n d N cap p := by
  let S := fifthPolicy n d (N:ℝ)
  let Q := fun h => (N:ℝ)^P4AOriginalSavedSixthStage.level n d (N:ℝ) h
  let M := fun h => (N:ℝ)^P4AOriginalElevenSixthStage.level n d (N:ℝ) h
  let carrier := roughPrimeUniverse N cap 0 z
  have hold (s) (hs : s∈firstExitDepthFrontier 6 S weight [] true 1 carrier) :
      ordinaryRosserPrefixAdmissible false (Q s.selectedPrefix) s.selectedPrefix :=
    actual_G4_at_six n d N cap 0 z weight hN s hs
  have hnew (s) (hs : s∈firstExitDepthFrontier 6 S weight [] true 1 carrier) :
      ordinaryRosserPrefixAdmissible false (M s.selectedPrefix) s.selectedPrefix :=
    actual_G7_at_six n d N cap 0 z weight hN s hs
  have hx := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 6 (by decide) S M Q N cap z hnew hold
  change firstExitRetainedPolynomial
      (firstExitDepthSplicePolicy 6 S (frozenParityRosserPolicy false 6 Q)) _ _ _ _ _-
      firstExitRetainedPolynomial
      (firstExitDepthSplicePolicy 6 S (frozenParityRosserPolicy false 6 M)) _ _ _ _ _=_ at hx
  dsimp only [S,Q,M] at hx
  change firstExitRetainedPolynomial (P4AOriginalSavedSixthStage.policy n d (N:ℝ)) _ _ _ _ _-
    firstExitRetainedPolynomial (P4AOriginalElevenSixthStage.policy n d (N:ℝ)) _ _ _ _ _=_ at hx
  rw [UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
      (P4AOriginalSavedSixthStage.even n d (N:ℝ)) N cap 0 z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
      (P4AOriginalElevenSixthStage.even n d (N:ℝ)) N cap 0 z] at hx
  unfold normalize
  change (raw _ N cap 0 z-raw _ N cap 0 z)*_/_=_
  change raw _ N cap 0 z-raw _ N cap 0 z=_ at hx
  rw [hx]
  let states := firstExitDepthFrontier 6 S weight [] true 1 carrier
  let term := fun s : FirstExitDepthState ℕ =>
    actualFrozenFrontierDensityTerm false N cap Q s.selectedPrefix-
      actualFrozenFrontierDensityTerm false N cap M s.selectedPrefix
  have hscale (l : List (FirstExitDepthState ℕ)) :
      (l.map term).sum*Real.log (N:ℝ)/singularSeries N=
        (l.map (fun s => term s*Real.log (N:ℝ)/singularSeries N)).sum := by
    induction l with
    | nil => simp
    | cons s l ih => simp only [List.map_cons,List.sum_cons,add_mul,add_div,ih]
  change (states.map term).sum*_/_=_
  rw [hscale]
  rw [← firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 6 S weight carrier
    (roughPrimeUniverse_nodup N cap 0 z) (tupleResidual n d N cap)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hl := firstExitDepthFrontier_selected_length 6 S weight [] carrier true 1 (by simp) s hs
  have hpre : pre (primeHistoryTuple 6 s.selectedPrefix)=s.selectedPrefix := primeHistoryTuple_reverse_ofFn hl
  dsimp only [term]
  rw [rank_six_density N cap Q _ hl,rank_six_density N cap M _ hl]
  simp only [tupleResidual,actualPrimeTupleInitialSaving,hpre,primeHistoryTuple_last (k:=5) hl,
    primeHistoryTuple_prod hl,Q,M,weight]
  ring

end
end ImbalancedChen.P4AOriginalElevenRankSixSigned
