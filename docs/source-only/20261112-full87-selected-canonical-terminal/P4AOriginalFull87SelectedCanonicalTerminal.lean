import ImbalancedChen.P4AOriginalFull87InheritedTerminalLevel
import ImbalancedChen.P4AOriginalFull87LicensedSixthRealization
import ImbalancedChen.P4AOriginalFull87FiniteEighthCap
import ImbalancedChen.P4AActualSixthFrozenEighthAdmission
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The selected eighth action on the ACTUAL licensed-sixth full87 tree:
for the original canonical eight-prime source histories supplied by the
previously proved FilteredSourceSupply, ALL literal post-eight retained
terminal leaves satisfy the fixed rough product bound.

Unlike the inherited branch, the selected continuation uses the actual
finite eighth cap. Incoming full Rosser admission is transported from
the true sixth level to that eighth cap using the source-supplied
licensed sixth < finite eighth comparison. SourceSupply is a pre-existing
manuscript-internal theorem output, NOT an assumed distribution theorem.
No new parent, mask, leaf cover, source field, PP or reserve is introduced.

This theorem covers canonical realised source states, not arbitrary rank-eight
states with selectedCap=some; that remaining exhaustiveness step is explicit.
-/

namespace ImbalancedChen.P4AOriginalFull87SelectedCanonicalTerminal
noncomputable section
open scoped Classical
open VariableEnvelope
open P4AOriginalFull87SevenCubeAdmission (pre pre_length point)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_of_trim selectedCap_append)
open P4AOriginalFull87FiniteEighthCap (finiteCap finiteCap_upper)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)

/-- The same canonical source history, the original selected eighth cap,
the same sixth ancestor, the same retained terminal leaves. -/
theorem actual_selected_canonical_terminal_product_lt_fixed_power
    (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (hsupply : FilteredSourceSupply s r n e q om)
    (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ) ^ mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (p : Fin 8 → ℕ) (hp : ∀ i, (p i).Prime)
    (hdelete : ∀ i, ¬p i ∣ N)
    (c : P4AOriginalFull87SourceDictionary.Cell)
    (ht : point (N : ℝ) p ∈ trim c (width r))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight
      (canonicalState N cap w weight p).selectedPrefix
      (canonicalState N cap w weight p).positive
      (canonicalState N cap w weight p).mass
      (canonicalState N cap w weight p).remaining) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  let state := canonicalState N cap w weight p
  have hsrc : P4AOriginalFull87SourceDictionary.Source c (point (N : ℝ) p) :=
    trim_subset_source c (width_pos r) ht
  obtain ⟨hhistory, _h5, _h6, _halphabet, hcapGap, _hsafe, hmember⟩ :=
    hsupply N hN p hp hdelete c ht
  have hstate : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
    -- The existing supplier returns membership in its *filtered owned list*.
    -- Recover the actual original frontier membership without changing it.
    have hm : canonicalState N cap w weight p ∈
        P4AOriginalFull87LicensedSixthRealization.states
          (width r) n e q om N cap w z weight c :=
      hmember cap w z hw hz hzcap weight
    exact (List.mem_filter.mp hm).1
  have hpre : state.selectedPrefix = pre p := rfl
  have hlen : 8 ≤ state.selectedPrefix.length := by
    rw [hpre, pre_length]
  have hactive :
      P4AOriginalFull87FiniteParentPolicy.active e q om (N : ℝ)
        (rosserAncestor 6 (pre p)) := by
    apply (P4AOriginalFull87FiniteParentPolicy.active_ancestor
      e q om (N : ℝ) 6 (by decide) (pre p)).mpr
    exact P4AOriginalFull87FiniteParentPolicy.source_active
      e q om (N : ℝ) (pre p) (pre_length p) c hsrc hhistory
  have h6le :
      P4AOriginalFull87LicensedSixthPolicy.level6Exponent
        n e q om (N : ℝ) (rosserAncestor 6 state.selectedPrefix) ≤
        (finiteCap n c (point (N : ℝ) p) : ℝ) := by
    rw [hpre]
    unfold P4AOriginalFull87LicensedSixthPolicy.level6Exponent
    rw [if_pos hactive]
    have hwidth := width_pos r
    linarith
  have hSix : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.sixthPolicy
        n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only [P4AOriginalFull87LicensedSixthPolicy.frontier_eq_new_sixth] using hstate
  have hActual : state ∈ firstExitDepthFrontier 8
      (P4AActualSixthFrozenEighthAdmission.sixthPolicy
        (P4AOriginalFull87FiniteParentPolicy.fifthPolicy
          n e q om (N : ℝ))
        (fun history => (N : ℝ) ^
          P4AOriginalFull87LicensedSixthPolicy.level6Exponent
            n e q om (N : ℝ) history))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only [P4AActualSixthFrozenEighthAdmission.sixthPolicy,
      P4AOriginalFull87LicensedSixthPolicy.sixthPolicy] using hSix
  have hSixAdmissible :=
    P4AActualSixthFrozenEighthAdmission.actual_rank_eight_admissible
      (P4AOriginalFull87FiniteParentPolicy.fifthPolicy
        n e q om (N : ℝ))
      (fun history => (N : ℝ) ^
        P4AOriginalFull87LicensedSixthPolicy.level6Exponent
          n e q om (N : ℝ) history)
      N cap w z weight state hActual
  have hEightAdmissible : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ (finiteCap n c (point (N : ℝ) p) : ℝ))
      state.selectedPrefix :=
    ordinaryRosserPrefixAdmissible_mono false _
      (Real.rpow_le_rpow_of_exponent_le hN.le h6le) hSixAdmissible
  have hselected :
      selectedCap (width r) n (N : ℝ) state.selectedPrefix =
        some (finiteCap n c (point (N : ℝ) p)) := by
    rw [hpre]
    exact selectedCap_of_trim (width r) (width_pos r) n
      (N : ℝ) (pre p) (pre_length p) c ht
  have hext : ∀ later : List ℕ, later ≠ [] →
      ∀ b : Bool,
        P4AOriginalFull87LicensedSixthPolicy.policy
          (width r) n e q om (N : ℝ) b
          (later ++ state.selectedPrefix) =
        ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c (point (N : ℝ) p) : ℝ))
          b (later ++ state.selectedPrefix) := by
    intro later hne b
    have hlater : 0 < later.length := by
      cases later with
      | nil => exact (hne rfl).elim
      | cons _ _ => simp
    have hdeep : ¬(later ++ state.selectedPrefix).length ≤ 8 := by
      simp only [List.length_append]
      omega
    simp only [P4AOriginalFull87LicensedSixthPolicy.policy,
      firstExitDepthSplicePolicy, if_neg hdeep,
      P4AOriginalFull87LicensedSixthPolicy.eighthContinuation,
      selectedCap_append (width r) n (N : ℝ) later state.selectedPrefix hlen,
      hselected]
  have hmatch :=
    P4AOriginalFull87InheritedTerminalLevel.retained_leaves_congr_nonempty
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^ (finiteCap n c (point (N : ℝ) p) : ℝ)))
      weight state.selectedPrefix state.remaining state.positive state.mass hext
  change leaf ∈ firstExitRetainedLeaves
    (P4AOriginalFull87LicensedSixthPolicy.policy
      (width r) n e q om (N : ℝ))
    weight state.selectedPrefix state.positive state.mass state.remaining at hleaf
  rw [hmatch] at hleaf
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength
    8 (P4AOriginalFull87LicensedSixthPolicy.policy
      (width r) n e q om (N : ℝ))
    weight (roughPrimeUniverse N cap w z) state hstate
  have hsub : state.selectedPrefix.reverse ++ state.remaining <+
      roughPrimeUniverse N cap w z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist
      8 (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight [] (roughPrimeUniverse N cap w z) true 1 state hstate
  have hprime : ∀ v ∈ state.remaining, v.Prime := by
    intro v hv
    exact mem_roughPrimeUniverse_prime
      (hsub.subset (List.mem_append_right _ hv))
  have horder : (state.selectedPrefix.reverse ++ state.remaining).Pairwise
      (· > ·) :=
    (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hsort : (state.remaining.reverse ++ state.selectedPrefix).Pairwise
      (· < ·) := by
    simpa only [List.reverse_append, List.reverse_reverse,
      List.pairwise_reverse] using horder
  have hterminal : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ (finiteCap n c (point (N : ℝ) p) : ℝ))
      leaf.selected :=
    P4AOriginalFull87InheritedTerminalLevel.ordinary_terminal_admissible
      _ weight state.selectedPrefix state.remaining state.positive state.mass
      hEightAdmissible hsign hprime hsort leaf hleaf
  have hUpper : (finiteCap n c (point (N : ℝ) p) : ℝ) ≤
      (299 / 500 : ℝ) :=
    (finiteCap_upper n hsrc).1.le.trans (by norm_num)
  exact hterminal.1.trans_le
    (Real.rpow_le_rpow_of_exponent_le hN.le hUpper)

end
end ImbalancedChen.P4AOriginalFull87SelectedCanonicalTerminal
