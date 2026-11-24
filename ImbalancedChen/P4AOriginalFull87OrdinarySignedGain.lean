import ImbalancedChen.P4AOriginalFull87EighthKernelIntegration
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger
import ImbalancedChen.FirstExitAdmittedFrontierTuples
import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral
import ImbalancedChen.P5OriginalCommonPositivePresieve

/-!
Ordinary density of the actual licensed eighth splice. Section 4 first
takes the difference with the same sixth parent at zero presieve. Both
ordinary tails have the original last-prime cutoff and prefix quotient.
The later physical beta projection applies to one complete tree.
-/
namespace ImbalancedChen.P4AOriginalFull87OrdinarySignedGain
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87HistoryCore (core width width_pos)
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87SevenCubeAdmission (pre point pre_length pre_ofFn tuple_pre source_strictAnti)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap point8_at_eight selectedCap_of_trim)
open P4AOriginalFull87LicensedSixthPolicy (level6Exponent sixthPolicy policy)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent actual_eighth_kernel_transport)
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize)

/-- The existing common history restricted to the eight-prime words
where it is used. Supplied uniformly by the original common mesh. -/
def HistoryOnTrim (r : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℕ, 1 < (N : ℝ) → ∀ h : List ℕ, h.length = 8 →
    (∀ p ∈ h, 0 < p) → ∀ c : Cell,
    primeHistoryLogCoordinates (N : ℝ) 8 h ∈ trim c (width r) →
      RealizedHistory e q om (N : ℝ) h c

theorem common_history_on_trim (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
        ∀ om : ℝ, om ≤ 1 / 100 → HistoryOnTrim r e q om := by
  obtain ⟨e0, he0, h⟩ := P4AOriginalFull87ActualCommonHistory.exists_original_common_history
    (width r) (width_pos r)
  refine ⟨e0, he0, ?_⟩
  intro e he he'
  obtain ⟨q0, hq0, hh⟩ := h e he he'
  refine ⟨q0, hq0, ?_⟩
  intro q hq om hom N hN word hlen hpos c ht
  exact hh q hq om hom (N : ℝ) hN word hlen hpos c
    (trim_subset_source c (width_pos r) ht) (trim_subset_core c (width r) ht)

def nextExponent (r n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (h : List ℕ) : ℝ :=
  match selectedCap (width r) n N h with
  | none => actualParent n e q om N h
  | some a => (a : ℝ)

theorem point_eq_tuple_log (N : ℕ) (p : Fin 8 → ℕ) :
    point (N : ℝ) p = actualPrimeTupleLog N p := by
  simp only [point, primeHistoryLogCoordinates, actualPrimeTupleLog, tuple_pre]

private theorem selected_ancestor (r n : ℕ) (N : ℝ) (h : List ℕ) (hl : 8 ≤ h.length) :
    selectedCap (width r) n N (rosserAncestor 8 h) = selectedCap (width r) n N h := by
  have h8 : 8 ≤ (rosserAncestor 8 h).length := by simp [min_eq_left hl]
  simp only [selectedCap, ownerAtPrefix, if_pos h8, if_pos hl, point8,
    rosserAncestor_nested 8 8 le_rfl]

/-- This is an equality of the original licensed policy functions. In
the inherited branch the sixth ancestor of the eighth is the own sixth. -/
theorem next_refreeze_eq_policy (r n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) :
    firstExitDepthSplicePolicy 8 (sixthPolicy n e q om N)
      (frozenParityRosserPolicy false 8 (fun h => N ^ nextExponent r n e q om N h)) =
        policy (width r) n e q om N := by
  funext b h
  by_cases h8 : h.length ≤ 8
  · simp only [policy, firstExitDepthSplicePolicy, if_pos h8]
  · have h6 : ¬h.length ≤ 6 := by omega
    simp only [policy, firstExitDepthSplicePolicy, if_neg h8, frozenParityRosserPolicy,
      ancestorFrozenPolicy, nextExponent, selected_ancestor r n N h (by omega),
      P4AOriginalFull87LicensedSixthPolicy.eighthContinuation]
    cases selectedCap (width r) n N h with
    | some a => rfl
    | none =>
      simp only [actualParent, rosserAncestor_nested 6 8 (by decide),
        sixthPolicy, firstExitDepthSplicePolicy, if_neg h6,
        frozenParityRosserPolicy, ancestorFrozenPolicy]

theorem parent_refreeze_eq_sixth (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) :
    firstExitDepthSplicePolicy 8 (sixthPolicy n e q om N)
      (frozenParityRosserPolicy false 8 (fun h => N ^ actualParent n e q om N h)) =
        sixthPolicy n e q om N := by
  unfold actualParent sixthPolicy
  rw [frozenParityRosserPolicy_nested false 6 8 (by decide)
    (fun h => N ^ level6Exponent n e q om N h)]
  exact firstExitDepthSplicePolicy_absorb_later 6 8 (by decide) _ _

abbrev weight (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

def admitted (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (z : ℝ) :=
  firstExitAdmittedTuples 8 (sixthPolicy n e q om (N : ℝ)) (roughPrimeUniverse N cap 0 z)

def tupleResidual (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (p : Fin 8 → ℕ) : ℝ :=
  actualPrimeTupleInitialSaving N cap (actualParent n e q om (N : ℝ) (pre p))
    (nextExponent r n e q om (N : ℝ) (pre p)) p

theorem original_raw_difference_eq_admitted
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (z : ℝ)
    (hn : 4 * width n < width r) (hN : 1 < (N : ℝ)) (hh : HistoryOnTrim r e q om) :
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
      (P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q om (N : ℝ))
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
      have h := actual_eighth_kernel_transport r n hn e q om (N : ℝ) _ hl c htrim
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
      (P4AOriginalFull87LicensedSixthPolicy.sixth_even n e q om (N : ℝ)) N cap 0 z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
      (P4AOriginalFull87LicensedSixthPolicy.policy_even (width r) n e q om (N : ℝ)) N cap 0 z] at hx
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
end ImbalancedChen.P4AOriginalFull87OrdinarySignedGain

