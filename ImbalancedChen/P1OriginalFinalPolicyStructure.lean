import ImbalancedChen.P4AOriginalFiniteAll22PhysicalLedger
import ImbalancedChen.P4AOriginalFiniteFallbackJointGain
import ImbalancedChen.P4AOriginalFiniteFallbackPhysicalRange
import ImbalancedChen.P4AOriginalFull87CompiledCounting
import ImbalancedChen.P4AUpperTaggedContinuationAccounting
import ImbalancedChen.ActualUpperPolicyFiniteBridge
import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.PhysicalUpperWeightBridge

/-!
Static structural exports for the actual modern final policy.
UNCOMPILED: no kernel or publication status is asserted.

The retained tree is the finite fallback dispatcher on NewFifthUnion.data.
Its physical coefficient is the existing empty-tag beta compiler rho.
The raw and compiled coefficients are kept distinct.  Their exact density
identity retains the beta, changed-cell and presieve-correction terms.
-/
namespace ImbalancedChen.P1OriginalFinalPolicyStructure

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P4AOriginalFiniteFallbackPolicy (F rho)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87CompiledCounting (moduli)

/-- Both branches of the actual final dispatcher retain positive states. -/
theorem finalPolicy_even (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (pre : List ℕ) :
    finalPolicy m r n e q a omega N true pre = true := by
  classical
  unfold finalPolicy P4AOriginalFiniteFallbackPolicy.policy
    P4AOriginalFiniteFallbackPolicy.dispatch
  split_ifs
  · exact P4AOriginalFiniteFallbackOccurrence.positive
      (bank m) (data e q a) omega (N : ℝ) pre
  · exact P4AOriginalFiniteFallbackJointGain.lower_even
      (width r) n (data e q a) omega (N : ℝ) pre

/-- No fourth, fifth, sixth or eighth action replaces the initial rule
through rank two, including the original first-label stop. -/
theorem finalPolicy_through_two (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 2) :
    finalPolicy m r n e q a omega N positive pre =
      HistoricalThirdCoarse.initialPolicy (e : ℝ) (data e q a).m (N : ℝ) positive pre := by
  classical
  have h3 : pre.length ≤ 3 := by omega
  have h4 : pre.length ≤ 4 := by omega
  have h6 : pre.length ≤ 6 := by omega
  have h8 : pre.length ≤ 8 := by omega
  unfold finalPolicy P4AOriginalFiniteFallbackPolicy.policy
    P4AOriginalFiniteFallbackPolicy.dispatch
  split_ifs
  · simp [P4AOriginalFiniteFallbackPolicy.upper, hlen]
  · simp [P4AOriginalOrderedThirdFullPolicy.policy,
      P4AOriginalOrderedThirdFullPolicy.eight,
      P4AOriginalOrderedThirdFullPolicy.six,
      P4AOriginalOrderedThirdFullPolicy.five,
      firstExitDepthSplicePolicy,
      P4AOriginalOrderedThirdFullPolicy.common,
      P4AOriginalOrderedThirdFullPolicy.base, hlen, h3, h4, h6, h8]

/-- The first-stop conclusion concerns an accepted rank-one odd test;
acceptance of an arbitrary later word alone is not its premise. -/
theorem finalPolicy_firstStop (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (pre : List ℕ) (hlen : pre.length = 1)
    (haccept : finalPolicy m r n e q a omega N false pre = true) :
    HistoricalThirdCoarse.firstStop (e : ℝ) (data e q a).m (N : ℝ) pre := by
  have hi :
      HistoricalThirdCoarse.initialPolicy (e : ℝ) (data e q a).m
        (N : ℝ) false pre = true :=
    (finalPolicy_through_two m r n e q a omega N false pre (by omega)).symm.trans haccept
  have h :
      ordinaryRosserPrefixAdmissible false
          ((N : ℝ) ^ HistoricalThirdCoarse.initial (e : ℝ)) pre ∧
        (pre.length = 1 →
          HistoricalThirdCoarse.firstStop (e : ℝ) (data e q a).m (N : ℝ) pre) := by
    simpa [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy] using hi
  exact h.2 hlen

/-- The odd-retention interface reconstructs this very final tree. -/
theorem finalPolicy_eq_oddFirstExitPolicy (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) :
    oddFirstExitPolicy (F (bank m) (width r) n (data e q a) omega N) =
      finalPolicy m r n e q a omega N := by
  simpa only [finalPolicy, F] using
    UpperPolicyFiniteBridge.oddFirstExitPolicy_eq_of_even_retained
      (finalPolicy m r n e q a omega N) (finalPolicy_even m r n e q a omega N)

theorem final_raw_coefficient_identity (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient (F (bank m) (width r) n (data e q a) omega N) N N w z d =
      (firstExitRetainedCoefficient (finalPolicy m r n e q a omega N)
        (roughPrimeUniverse N N w z) d : ℝ) := by
  simpa only [finalPolicy, F] using
    UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
      (finalPolicy m r n e q a omega N)
      (finalPolicy_even m r n e q a omega N) N N w z d

/-- The actual final retained polynomial and its raw reciprocal-totient
density use the same retained coefficient. -/
theorem final_raw_density_identity (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial (finalPolicy m r n e q a omega N)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N N w z) =
      reciprocalTotientDensity
        (fixedRoughSupport (F (bank m) (width r) n (data e q a) omega N) N N w z)
        (fixedRoughCoefficient (F (bank m) (width r) n (data e q a) omega N) N N w z) := by
  simpa only [finalPolicy, F] using
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      (finalPolicy m r n e q a omega N)
      (finalPolicy_even m r n e q a omega N) N N w z

/-- The genuine upper projection is an inequality for the same raw policy. -/
theorem final_raw_presieve_projection (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    actualSmallEulerProduct N N w *
        reciprocalTotientDensity
          (fixedRoughSupport (F (bank m) (width r) n (data e q a) omega N) N N w z)
          (fixedRoughCoefficient (F (bank m) (width r) n (data e q a) omega N) N N w z) ≤
      reciprocalTotientDensity
        (fixedRoughSupport (F (bank m) (width r) n (data e q a) omega N) N N 0 z)
        (fixedRoughCoefficient (F (bank m) (width r) n (data e q a) omega N) N N 0 z) :=
  fixedRoughDensity_presieveProjection
    (F (bank m) (width r) n (data e q a) omega N) N N w z hwz

/-- One literal final rho majorizes the rough indicator for every integer,
including zero and negative integers. -/
theorem final_rho_majorant (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau L : ℝ) (hL : 1 < L) (hwL : (N : ℝ) ^ omega ≤ L)
    (hwz : (N : ℝ) ^ omega ≤ cutoff N) (hzN : cutoff N ≤ (N : ℝ)) (x : ℤ) :
    actualSmallRoughIndicator N (cutoff N) x ≤
      physicalDivisorSum (moduli N ((N : ℝ) ^ omega))
        (rho (bank m) r n e q a omega N tau L) x.natAbs := by
  simpa only [rho, moduli] using
    P4AUpperTaggedBetaAttachment.rho_majorant
      (F (bank m) (width r) n (data e q a) omega N) (fun _ => [])
      N N ((N : ℝ) ^ omega) (cutoff N) tau L hL hwL hwz hzN x

theorem final_rho_divisorSum_nonneg (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau L : ℝ) (hL : 1 < L) (hwL : (N : ℝ) ^ omega ≤ L)
    (hwz : (N : ℝ) ^ omega ≤ cutoff N) (hzN : cutoff N ≤ (N : ℝ)) (x : ℤ) :
    0 ≤ physicalDivisorSum (moduli N ((N : ℝ) ^ omega))
      (rho (bank m) r n e q a omega N tau L) x.natAbs := by
  simpa only [rho, moduli] using
    P4AUpperTaggedBetaAttachment.rho_divisorSum_nonneg
      (F (bank m) (width r) n (data e q a) omega N) (fun _ => [])
      N N ((N : ℝ) ^ omega) (cutoff N) tau L hL hwL hwz hzN x

theorem final_rho_abs_le_one (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau L : ℝ) (d : ℕ) :
    |rho (bank m) r n e q a omega N tau L d| ≤ 1 := by
  simpa only [rho] using
    P4AUpperTaggedBetaAttachment.rho_abs_le_one
      (F (bank m) (width r) n (data e q a) omega N) (fun _ => [])
      N N ((N : ℝ) ^ omega) (cutoff N) tau L d

theorem final_rho_support_arithmetic (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau L : ℝ) (d : ℕ)
    (hd : rho (bank m) r n e q a omega N tau L d ≠ 0) :
    Squarefree d ∧ d.Coprime N := by
  classical
  have hm : d ∈ P4AUpperTaggedBetaAttachment.support N N ((N : ℝ) ^ omega) (cutoff N) := by
    by_contra hnot
    apply hd
    change smallRoughRho _ _ _ _ _ d = 0
    exact smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot
  exact ⟨P4AUpperTaggedBetaAttachment.support_squarefree N N _ _ hm,
    P4AUpperTaggedBetaAttachment.support_coprime_target N N _ _ hm⟩

/-- Exact compiled density, before estimates.  The compiler rho is not
identified with the uncompiled raw beta attachment. -/
theorem final_rho_density_identity (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau L : ℝ) (hwz : (N : ℝ) ^ omega ≤ cutoff N) :
    let f := F (bank m) (width r) n (data e q a) omega N
    physicalDensitySum (moduli N ((N : ℝ) ^ omega))
        (rho (bank m) r n e q a omega N tau L) =
      rawRoot (finalPolicy m r n e q a omega N) N +
        (p4aReservePhysicalDensity f N N ((N : ℝ) ^ omega) (cutoff N) L -
          actualSmallEulerProduct N N ((N : ℝ) ^ omega) *
            p4aReserveRawDensity f N N ((N : ℝ) ^ omega) (cutoff N)) +
        reciprocalTotientDensity (actualSmallRosserSupport N N ((N : ℝ) ^ omega))
            (actualSmallRosserPlus N N ((N : ℝ) ^ omega) L) *
          P4AUpperTaggedContinuationAccounting.positiveChangedMass f (fun _ => [])
            N N ((N : ℝ) ^ omega) (cutoff N) tau +
        reciprocalTotientDensity (actualSmallRosserSupport N N ((N : ℝ) ^ omega))
            (actualSmallRosserMinus N N ((N : ℝ) ^ omega) L) *
          P4AUpperTaggedContinuationAccounting.negativeChangedMass f (fun _ => [])
            N N ((N : ℝ) ^ omega) (cutoff N) tau -
        p4aActualPresieveCorrection f N N ((N : ℝ) ^ omega) (cutoff N) := by
  simpa only [rho, moduli,
    P4AOriginalFiniteAll22PhysicalLedger.reserve_raw_is_actual_final] using
    P4AUpperTaggedContinuationAccounting.compiled_density_eq_full_plus_beta_and_changed_minus_correction
      (F (bank m) (width r) n (data e q a) omega N) (fun _ => [])
      N N ((N : ℝ) ^ omega) (cutoff N) tau L hwz

/-- Finite source evaluation and reciprocal-totient density use this same
Q and rho.  The signed distribution and coprime correction remain visible. -/
theorem final_same_rho_source_identity (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N num den : ℕ) (tau L T : ℝ) :
    (∑ d ∈ moduli N ((N : ℝ) ^ omega),
        rho (bank m) r n e q a omega N tau L d * halfProductCongruenceMass num den N T d) =
      ((halfProductSource num den N T).card : ℝ) *
          physicalDensitySum (moduli N ((N : ℝ) ^ omega))
            (rho (bank m) r n e q a omega N tau L) +
        physicalCoprimeCorrection num den N T (moduli N ((N : ℝ) ^ omega))
          (rho (bank m) r n e q a omega N tau L) +
        physicalDistributionError num den N T (moduli N ((N : ℝ) ^ omega))
          (rho (bank m) r n e q a omega N tau L) :=
  sum_rho_mul_halfProductCongruenceMass_eq num den N T
    (moduli N ((N : ℝ) ^ omega)) (rho (bank m) r n e q a omega N tau L)

/-- The actual raw final policy has the existing strict 299/500 carrier. -/
theorem final_raw_support (m r n : ℕ) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (a omega : ℝ)
    (homega : 0 < omega) (N : ℕ) (hN : 2 ≤ N) (d : ℕ)
    (hd : d ∈ P4AUpperTaggedParityCompiler.rawSupport
      (F (bank m) (width r) n (data e q a) omega N) N N ((N : ℝ) ^ omega) (cutoff N)) :
    d.primeFactorsList.length < P4AHeldTaggedCompilerSupport.J0 omega ∧
      (d : ℝ) < (N : ℝ) ^ P4AFull87UnionCompilerPayment.top := by
  exact P4AOriginalFiniteFallbackRange.raw_range
    (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m) (width r) (width_pos r)
    n (data e q a) (show 0 ≤ (data e q a).e from he) omega N N hN omega (cutoff N) homega hd

/-- The physical support width is chosen before N.  Its ell and tau
conditions are not conclusions of the raw bound alone. -/
theorem exists_final_rho_support_width (m r n : ℕ) (e : ℚ) (he : 0 ≤ e) (q : ℕ)
    (a omega ell : ℝ) (homega : 0 < omega) (hell : ell < 1 / 1000) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
      ell + tau * (P4AHeldTaggedCompilerSupport.J0 omega : ℝ) < 1 / 1000 ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ d : ℕ,
        rho (bank m) r n e q a omega N tau ((N : ℝ) ^ ell) d ≠ 0 →
          (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  obtain ⟨tau0, htau0, h⟩ :=
    P4AOriginalFiniteFallbackPhysicalRange.data_physical_range
      (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m) (width r) (width_pos r)
      n (data e q a) (show 0 ≤ (data e q a).e from he) omega ell homega hell
  refine ⟨tau0, htau0, ?_⟩
  intro tau htau hsmall
  obtain ⟨hbudget, hactive⟩ := h tau htau hsmall
  refine ⟨hbudget, ?_⟩
  intro N hN d hd
  exact hactive N N hN (cutoff N) (fun _ => []) d hd

end
end ImbalancedChen.P1OriginalFinalPolicyStructure
