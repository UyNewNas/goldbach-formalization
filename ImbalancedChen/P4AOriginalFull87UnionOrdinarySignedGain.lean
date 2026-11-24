import ImbalancedChen.P4AOriginalFull87UnionHistory

/-! Exact signed rank-eight splice on the enlarged fifth bank.
Both ordinary tails use the same sixth frontier of this bank. -/
namespace ImbalancedChen.P4AOriginalFull87UnionOrdinarySignedGain
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SevenCubeAdmission (pre pre_ofFn)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_append point8_at_eight)
open P4AOriginalFull87UnionHistory
open P4AOriginalFull87OrdinarySignedGain (weight HistoryOnTrim)
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize)

def nextExponent (r n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (h : List ℕ) : ℝ :=
  match selectedCap (width r) n N h with
  | none => actualParent n e q om N h
  | some a => (a : ℝ)

private theorem selected_ancestor (r n : ℕ) (N : ℝ) (h : List ℕ) (hl : 8 ≤ h.length) :
    selectedCap (width r) n N (rosserAncestor 8 h) = selectedCap (width r) n N h := by
  have h8 : 8 ≤ (rosserAncestor 8 h).length := by simp [min_eq_left hl]
  simp only [selectedCap,P4AOriginalFull87SourceDispatch.ownerAtPrefix,if_pos h8,if_pos hl,
    P4AOriginalFull87SourceDispatch.point8,rosserAncestor_nested 8 8 le_rfl]

theorem next_refreeze_eq_policy (r n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) :
    firstExitDepthSplicePolicy 8 (sixthPolicy n e q om N)
      (frozenParityRosserPolicy false 8 (fun h => N ^ nextExponent r n e q om N h)) =
        policy (width r) n e q om N := by
  funext b h
  by_cases h8 : h.length ≤ 8
  · simp only [policy,P4AOriginalFull87DataPolicy.policy,firstExitDepthSplicePolicy,if_pos h8]
  · have h6 : ¬h.length ≤ 6 := by omega
    simp only [policy,P4AOriginalFull87DataPolicy.policy,firstExitDepthSplicePolicy,if_neg h8,
      frozenParityRosserPolicy,ancestorFrozenPolicy,nextExponent,selected_ancestor r n N h (by omega),
      P4AOriginalFull87DataPolicy.eighthContinuation]
    cases selectedCap (width r) n N h with
    | some a => rfl
    | none =>
      simp only [actualParent,P4AOriginalFull87DataPolicy.actualParent,rosserAncestor_nested 6 8 (by decide),
        sixthPolicy,P4AOriginalFull87DataPolicy.sixthPolicy,firstExitDepthSplicePolicy,if_neg h6,
        frozenParityRosserPolicy,ancestorFrozenPolicy]

theorem parent_refreeze_eq_sixth (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) :
    firstExitDepthSplicePolicy 8 (sixthPolicy n e q om N)
      (frozenParityRosserPolicy false 8 (fun h => N ^ actualParent n e q om N h)) =
        sixthPolicy n e q om N := by
  unfold actualParent P4AOriginalFull87DataPolicy.actualParent sixthPolicy P4AOriginalFull87DataPolicy.sixthPolicy
  rw [frozenParityRosserPolicy_nested false 6 8 (by decide)
    (fun h => N ^ P4AOriginalFull87DataPolicy.level6Exponent n (bank e q om) N h)]
  exact firstExitDepthSplicePolicy_absorb_later 6 8 (by decide) _ _

def admitted (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (z : ℝ) :=
  firstExitAdmittedTuples 8 (sixthPolicy n e q om (N : ℝ)) (roughPrimeUniverse N cap 0 z)

def tupleResidual (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (p : Fin 8 → ℕ) : ℝ :=
  actualPrimeTupleInitialSaving N cap (actualParent n e q om (N : ℝ) (pre p))
    (nextExponent r n e q om (N : ℝ) (pre p)) p

theorem original_raw_difference_eq_admitted
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (z : ℝ)
    (hn : 4 * width n < width r) (he : 0 ≤ e) (hN : 1 < (N : ℝ)) (hh : HistoryOnTrim r e q om) :
    normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z -
      raw (policy (width r) n e q om (N : ℝ)) N cap 0 z) =
      ∑ p ∈ admitted n e q om N cap z, (∏ i, weight (p i)) * tupleResidual r n e q om N cap p := by
  let S := sixthPolicy n e q om (N : ℝ)
  let Q := fun h => (N : ℝ) ^ actualParent n e q om (N : ℝ) h
  let M := fun h => (N : ℝ) ^ nextExponent r n e q om (N : ℝ) h
  let carrier := roughPrimeUniverse N cap 0 z
  have hold (s) (hs : s ∈ firstExitDepthFrontier 8 S weight [] true 1 carrier) :
      ordinaryRosserPrefixAdmissible false (Q s.selectedPrefix) s.selectedPrefix :=
    P4AActualSixthFrozenEighthAdmission.actual_rank_eight_admissible
      (fifthPolicy n e q om (N : ℝ))
      (fun h => (N : ℝ) ^ level6Exponent n e q om (N : ℝ) h)
      N cap 0 z weight s hs
  have hnew (s) (hs : s ∈ firstExitDepthFrontier 8 S weight [] true 1 carrier) :
      ordinaryRosserPrefixAdmissible false (M s.selectedPrefix) s.selectedPrefix := by
    apply ordinaryRosserPrefixAdmissible_mono false _ _ (hold s hs)
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    change actualParent n e q om (N : ℝ) s.selectedPrefix ≤ nextExponent r n e q om (N : ℝ) s.selectedPrefix
    cases ha : selectedCap (width r) n (N : ℝ) s.selectedPrefix with
    | none => simp [nextExponent, ha]
    | some a =>
      obtain ⟨c, _, htrim, hval⟩ :=
        P4AOriginalFull87FiniteEighthPolicy.selectedCap_some_spec _ _ _ _ _ ha
      have hl := firstExitDepthFrontier_selected_length 8 S weight [] carrier true 1 (by simp) s hs
      rw [point8_at_eight _ _ hl] at htrim hval
      have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 S weight carrier s hs
      have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := fun p hp =>
        (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
      have h := actual_eighth_kernel_transport r n hn e q om (N : ℝ) he _ hl c htrim
        (hh N hN _ hl hpos c htrim)
      simpa only [nextExponent, ha, hval] using h.2.2.1.trans h.2.2.2.1.le
  have hx := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 8 (by decide) S M Q N cap z hnew hold
  change firstExitRetainedPolynomial
      (firstExitDepthSplicePolicy 8 S (frozenParityRosserPolicy false 8 Q)) _ _ _ _ _ -
      firstExitRetainedPolynomial
      (firstExitDepthSplicePolicy 8 S (frozenParityRosserPolicy false 8 M)) _ _ _ _ _ = _ at hx
  dsimp only [S, Q, M] at hx
  rw [parent_refreeze_eq_sixth, next_refreeze_eq_policy,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
      (P4AOriginalFull87DataPolicy.sixth_even n (bank e q om) (N : ℝ)) N cap 0 z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
      (P4AOriginalFull87DataPolicy.policy_even (width r) n (bank e q om) (N : ℝ)) N cap 0 z] at hx
  unfold normalize
  change (raw _ N cap 0 z - raw _ N cap 0 z) * _ / _ = _
  change raw _ N cap 0 z - raw _ N cap 0 z = _ at hx
  rw [hx]
  let states := firstExitDepthFrontier 8 S weight [] true 1 carrier
  let d := fun s : FirstExitDepthState ℕ =>
    actualFrozenFrontierDensityTerm false N cap Q s.selectedPrefix -
      actualFrozenFrontierDensityTerm false N cap M s.selectedPrefix
  have hscale (l : List (FirstExitDepthState ℕ)) :
      (l.map d).sum * Real.log (N : ℝ) / singularSeries N =
        (l.map (fun s => d s * Real.log (N : ℝ) / singularSeries N)).sum := by
    induction l with
    | nil => simp
    | cons s l ih => simp only [List.map_cons, List.sum_cons, add_mul, add_div, ih]
  change (states.map d).sum * _ / _ = _
  rw [hscale]
  rw [← firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 8 S weight carrier
    (roughPrimeUniverse_nodup N cap 0 z) (tupleResidual r n e q om N cap)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hl := firstExitDepthFrontier_selected_length 8 S weight [] carrier true 1 (by simp) s hs
  have hpre : pre (primeHistoryTuple 8 s.selectedPrefix) = s.selectedPrefix :=
    (pre_ofFn _).trans (primeHistoryTuple_reverse_ofFn hl)
  dsimp only [d]
  rw [P2OriginalAscendingEighthCapDictionary.actual_rank_eight_difference N cap Q M _ hl]
  simp only [P2OriginalAscendingEighthCapDictionary.actualEighthResidualDifference, tupleResidual,
    actualPrimeTupleInitialSaving, hpre, primeHistoryTuple_last (k := 7) hl,
    primeHistoryTuple_prod hl, Q, M, weight]
  ring


end
end ImbalancedChen.P4AOriginalFull87UnionOrdinarySignedGain
