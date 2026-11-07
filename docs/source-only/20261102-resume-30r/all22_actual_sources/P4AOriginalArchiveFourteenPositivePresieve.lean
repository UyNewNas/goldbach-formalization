import ImbalancedChen.P5OriginalFourthFifthSourceInputs
import ImbalancedChen.P2OriginalFourteenCommonScheduleEndpoint
import ImbalancedChen.P5OriginalCommonPositivePresieve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original fourth byte bank and its actual integer-geometry admission
instantiate the previously primitive common archive schedule. The original
fifth archive, fourteen pattern and actual sixth parent are unchanged.

The positive-presieve estimate projects ONE COMPLETE fourteen-policy tree.
It never projects an old-minus-new signed difference. The actual beta
supplier pays eta/2, and Q's existing ordinary endpoint uses eta/2.
This is a local actual-policy envelope, not the all87 policy or All22.
The geometry filter is retained; no assertion that all 3,699,127 wire rows
pass it or supply analytic licences is made. All finite bodies UNEVALUATED.
-/

namespace ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSource
open P5OriginalFourthFifthSourceInputs
open P4AOriginalCausalHistory P4AOriginalCommonArchiveSchedule
open P5OriginalCommonFourthFallbackExcision P5OriginalCommonFourthSourceNavigation
open P5OriginalCommonFourthSourceLedger P1Pair12RetainedSignedSource
open P4AOriginalVariableFifthPhysicalLedger P5OriginalCommonPositivePresieve
open P2OriginalSaving16TrimmedHistory P2OriginalFourteenWeightedTrim

/-- The same pre-N archive schedule with the actual fourth bank. -/
def schedule (e : ℚ) (q : ℕ) (omega : ℝ) : ArchiveSchedule :=
  fixedSchedule originalRows4 originalAdmission4 e q omega

def data (e : ℚ) (q : ℕ) (omega : ℝ) : OriginalData :=
  (schedule e q omega).data

theorem data_eq_original_heldData (e : ℚ) (q : ℕ) (omega : ℝ) :
    data e q omega = heldData e q ((e : ℝ) / 20) omega := rfl

/-- Geometry follows from the actual admission test. -/
theorem actual_fourth_geometry (e : ℚ) (q : ℕ) (omega : ℝ) :
    FourthGeometry (data e q omega) := by
  intro r _hr hlicense
  exact originalAdmission4_geometry r hlicense

/-- Literal fourteen-family tree on this same actual policy6 parent.
It is not identified with the full87 tree. -/
def fourteenPolicy (e : ℚ) (q : ℕ) (omega N : ℝ) : Bool → List ℕ → Bool :=
  P2OriginalFourteenSignedParentLedger.policy N (lambda6 (data e q omega) N)
    P4AOriginalAscending14Literal42.literalPattern (policy5 (data e q omega) N)

theorem fourteenPolicy_even (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    fourteenPolicy e q omega N true pre = true :=
  P2OriginalFourteenSignedParentLedger.policy_even N (lambda6 (data e q omega) N)
    P4AOriginalAscending14Literal42.literalPattern (policy5 (data e q omega) N)
    (policy5_even (data e q omega) N) pre

/-- Independent occurrence-list source with actual full-q beta attachment.
The sign is NEW minus CURRENT policy6. -/
def fourteenSourceChange (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier 8 (policy6 (data e q omega) (N : ℝ))
    (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z)).map (fun state =>
      signedTest
        (frozenParityRosserPolicy false 8
          (P2OriginalAscendingEighthCapDictionary.familyNextLevel (N : ℝ)
            (lambda6 (data e q omega) (N : ℝ))
            P4AOriginalAscending14Literal42.literalPattern))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining -
      signedTest (policy6 (data e q omega) (N : ℝ))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining)).sum

/-- Exact source at any presieve, with the same target-deleted carrier,
full modulus, incoming sign/mass and remaining carrier. -/
theorem physical_fourteen_sub_current_eq_source
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ actualSmallRoughModuli (fourteenPolicy e q omega (N : ℝ) false) N cap w z,
      actualSmallRoughRho (fourteenPolicy e q omega (N : ℝ) false) N cap w z L d * G d) -
      source (data e q omega) .sixth N cap w z L G =
        fourteenSourceChange e q omega N cap w z L G := by
  have hphysical := physical_test_eq_signedTest (fourteenPolicy e q omega (N : ℝ))
    (fourteenPolicy_even e q omega (N : ℝ)) N cap 1 w z L G
  simp only [one_mul] at hphysical
  rw [hphysical, source_eq_actual_root]
  change signedTest (firstExitDepthSplicePolicy 8 (policy6 (data e q omega) (N : ℝ))
      (frozenParityRosserPolicy false 8
        (P2OriginalAscendingEighthCapDictionary.familyNextLevel (N : ℝ)
          (lambda6 (data e q omega) (N : ℝ))
          P4AOriginalAscending14Literal42.literalPattern)))
      (fun _ => 1) (attachedLeafTest N cap 1 w L G) [] true 1
      (roughPrimeUniverse N cap w z) -
    signedTest (policy6 (data e q omega) (N : ℝ))
      (fun _ => 1) (attachedLeafTest N cap 1 w L G) [] true 1
      (roughPrimeUniverse N cap w z) = _
  exact signedTest_splice_sub_eq_frontier 8 _ _ (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] (roughPrimeUniverse N cap w z) true 1

/-- Concrete fourth/fifth increments retain the original signed gains,
including positive-presieve attachment. No primitive Geometry premise. -/
theorem original_fourth_fifth_attached_sources
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 ≤ (N : ℝ))
    (w z L : ℝ) (G : ℕ → ℝ) :
    let d := data e q omega
    let T := attachedLeafTest N cap 1 w L G
    let carrier := roughPrimeUniverse N cap w z
    sourceChange d .fourth N cap w z L G =
      signedTest (original4 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
        signedTest (old3 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier ∧
    sourceChange d .fifth N cap w z L G =
      signedTest (original5 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier -
        signedTest (original4 d (N : ℝ)) (fun _ => 1) T [] true 1 carrier := by
  dsimp only
  have h4 := source_next_sub_current (data e q omega) .fourth N cap w z L G
  have h5 := source_next_sub_current (data e q omega) .fifth N cap w z L G
  simp only [nextStage, parentStage, source_eq_actual_root, stagePolicy, terminal] at h4 h5
  have hp4 := fourth_signed_gain_preserved (data e q omega)
    (actual_fourth_geometry e q omega) (N : ℝ) hN (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) (roughPrimeUniverse N cap w z)
  have hp5 := archive_fifth_signed_gain_preserved (schedule e q omega)
    (actual_fourth_geometry e q omega) (N : ℝ) hN (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) (roughPrimeUniverse N cap w z)
  change signedTest (policy4 (data e q omega) (N : ℝ)) _ _ [] true 1 _ -
    signedTest (policy5 (data e q omega) (N : ℝ)) _ _ [] true 1 _ = _ at hp5
  constructor <;> linarith only [h4, h5, hp4, hp5]

/-- Raw density uses the same concrete sixth parent as Q. -/
theorem raw_current_sub_fourteen_eq_original_charge
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ) :
    raw (policy6 (data e q omega) (N : ℝ)) N cap w z -
      raw (fourteenPolicy e q omega (N : ℝ)) N cap w z =
        P2OriginalFourteenSignedParentLedger.charge N cap w z
          (lambda6 (data e q omega) (N : ℝ))
          P4AOriginalAscending14Literal42.literalPattern (policy5 (data e q omega) (N : ℝ)) := by
  have hh := P2OriginalFourteenSignedParentLedger.parent_sub_policy_eq_charge N cap w z
    (lambda6 (data e q omega) (N : ℝ))
    P4AOriginalAscending14Literal42.literalPattern (policy5 (data e q omega) (N : ℝ))
  change firstExitRetainedPolynomial (policy6 (data e q omega) (N : ℝ)) _ _ _ _ _ -
    firstExitRetainedPolynomial (fourteenPolicy e q omega (N : ℝ)) _ _ _ _ _ = _ at hh
  rw [UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (policy6_even (data e q omega) (N : ℝ)) N cap w z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (fourteenPolicy_even e q omega (N : ℝ)) N cap w z] at hh
  exact hh

/-- Actual positive-w envelope for the literal fourteen policy.
Beta is fixed before the archive/history choices, and one grid400 schedule
precedes N. Q's ordinary endpoint and the beta supplier each use eta/2.
This does not identify the resulting policy with all87 or pay a compiler
loss. The original fourth geometry admission remains a concrete filter. -/
theorem exists_original_bank_positive_fourteen_schedule
    (nu eta betaMax : ℝ) (hnu : 0 < nu) (heta : 0 < eta) (hbetaMax : 0 < betaMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧
      beta ^ 2 ≤ (19 / 96 : ℝ) / nu ∧
      ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
        ∀ e : ℚ, 0 < e → (e : ℝ) < e0 → ∀ omega : ℝ, omega ≤ 1 / 100 →
          ∃ q N0 : ℕ, 0 < q ∧ 2 ≤ N0 ∧
            FourteenHistory (schedule e q omega) (width n) ∧
            ∀ N cap : ℕ, N0 ≤ N → Even N →
              (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
              let w := (N : ℝ) ^ (nu * beta ^ 2)
              let z := (N : ℝ) ^ (19 / 96 : ℝ)
              let L := (N : ℝ) ^ (nu * beta)
              1 < w ∧ w ≤ z ∧
                normalize N (physical (fourteenPolicy e q omega (N : ℝ)) N cap w z L) <
                  normalize N (raw (policy6 (data e q omega) (N : ℝ)) N cap 0 z) -
                    (1222997719565324892497827 : ℝ) / (2 : ℝ)^96 + eta := by
  have hr : 0 < (19 / 96 : ℝ) / nu := div_pos (by norm_num) hnu
  have hnr : nu * ((19 / 96 : ℝ) / nu) = (19 / 96 : ℝ) := by
    field_simp [hnu.ne'] <;> ring
  obtain ⟨beta, hb, hb8, hbMax, hbr, Nb, _hNb, hbeta⟩ :=
    exists_actualSmallRoughRho_density_le_full_reserve
      nu ((19 / 96 : ℝ) / nu) (eta / 2) betaMax hnu hr (half_pos heta) hbetaMax
  obtain ⟨n, e0, he0, he0bound, hschedule⟩ :=
    P2OriginalFourteenCommonScheduleEndpoint.exists_fixed_archive_and_whole_fourteen_q96_schedule
      originalRows4 originalAdmission4 (fun r _hr hr => originalAdmission4_geometry r hr)
      (eta / 2) (half_pos heta)
  refine ⟨beta, hb, hb8, hbMax, hbr, n, e0, he0, he0bound, ?_⟩
  intro e he hee omega homega
  obtain ⟨q, Ns, hq, hNs, hs⟩ := hschedule e he hee omega homega
  dsimp only at hs
  obtain ⟨hhistory, hordinary, _hfourth, _hfifth⟩ := hs
  refine ⟨q, max Ns Nb, hq, hNs.trans (le_max_left _ _), hhistory, ?_⟩
  intro N cap hN hEven hcap
  have hN2 : 2 ≤ N := hNs.trans ((le_max_left _ _).trans hN)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hz : (N : ℝ) ^ mu ≤ (N : ℝ) ^ (19 / 96 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num [mu])
  have hbs := hbeta N ((le_max_right _ _).trans hN) hEven cap
    (by simpa only [hnr] using hcap) (fourteenPolicy e q omega (N : ℝ) false)
  dsimp only at hbs
  simp only [hnr] at hbs
  change physical (fourteenPolicy e q omega (N : ℝ)) N cap
      ((N : ℝ) ^ (nu * beta ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ)) ((N : ℝ) ^ (nu * beta)) ≤
    raw (fourteenPolicy e q omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) +
      (eta / 2) * singularSeries N / Real.log (N : ℝ) at hbs
  have hnorm := normalize_mono N hN2 hbs
  rw [normalize_add, normalize_reserve N hN2] at hnorm
  have hq96 := (hordinary N cap ((le_max_left _ _).trans hN) hEven
    ((N : ℝ) ^ (19 / 96 : ℝ)) hz hcap).2
  change (1222997719565324892497827 : ℝ) / (2 : ℝ)^96 - eta / 2 <
    normalize N (P2OriginalFourteenSignedParentLedger.charge N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))
      (lambda6 (data e q omega) (N : ℝ))
      P4AOriginalAscending14Literal42.literalPattern (policy5 (data e q omega) (N : ℝ))) at hq96
  rw [← raw_current_sub_fourteen_eq_original_charge, normalize_sub] at hq96
  dsimp only
  refine ⟨Real.one_lt_rpow hN1 (mul_pos hnu (sq_pos_of_pos hb)), ?_, ?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hN1.le
    simpa only [hnr] using mul_le_mul_of_nonneg_left hbr hnu.le
  · linarith only [hnorm, hq96]

end
end ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
