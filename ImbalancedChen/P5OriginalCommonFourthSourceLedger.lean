import ImbalancedChen.P5OriginalCommonFourthSourceNavigation
import ImbalancedChen.P1OriginalVariableFourthFullSourceMean
import ImbalancedChen.P5OriginalArchivePositivePresieveGain

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The common-fourth baseline is attached to the independently defined
original fourth source and its proved full active integral. The genuine
above-mu source correction remains, with no sign or endpoint assumed.
-/
namespace ImbalancedChen.P5OriginalCommonFourthSourceLedger
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSource
open P5OriginalCommonFourthSourceNavigation
open P1Pair12RetainedSignedSource
open P4AOriginalVariableFifthPhysicalLedger
open P5OriginalCommonPositivePresieve P5OriginalArchivePositivePresieveGain
open P1HistoricalFifthCommonPolicyInputs P2OriginalFourthCapProducerInterface
open P5OriginalFifthArchiveActualMean

theorem original4_even (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    original4 d N true pre = true :=
  fourth_even d.e d.chi d.m d.omega d.rows4 d.licensed4 N pre

theorem signedTest_one_eq_polynomial (R : Bool → List ℕ → Bool)
    (h : ℕ → ℝ) (pre : List ℕ) (positive : Bool) (mass : ℝ) (carrier : List ℕ) :
    signedTest R h (fun _ _ => 1) pre positive mass carrier =
      firstExitRetainedPolynomial R h pre positive mass carrier := by
  induction carrier generalizing pre positive mass with
  | nil => simp [signedTest, firstExitRetainedPolynomial]
  | cons p ps ih => simp only [signedTest, firstExitRetainedPolynomial, ih]

def rawCorrection (d : OriginalData) (N cap : ℕ) (w z : ℝ) : ℝ :=
  correctionTest d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (fun _ _ => 1) (roughPrimeUniverse N cap w z)

def physicalCorrection (d : OriginalData) (N cap : ℕ) (w z L : ℝ)
    (G : ℕ → ℝ) : ℝ :=
  correctionTest d (N : ℝ) (fun _ => 1) (attachedLeafTest N cap 1 w L G)
    (roughPrimeUniverse N cap w z)

/-- Arithmetic/AP/mean identity on complete physical moduli. The actual
small beta is kept inside the terminal test with its true incoming sign. -/
theorem common4_physical_source_sub_original (d : OriginalData) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    source d .fourth N cap w z L G -
      (∑ q ∈ actualSmallRoughModuli ((original4 d (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((original4 d (N : ℝ)) false) N cap w z L q * G q) =
      physicalCorrection d N cap w z L G := by
  rw [source_eq_actual_root]
  have ho := physical_test_eq_signedTest (original4 d (N : ℝ))
    (original4_even d (N : ℝ)) N cap 1 w z L G
  simp only [one_mul] at ho
  rw [ho]
  exact common4_sub_original_eq_correction d (N : ℝ) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) (roughPrimeUniverse N cap w z)

/-- Exact density correction is derived from the same localized source,
not defined as the difference of two densities. -/
theorem common4_raw_sub_original (d : OriginalData) (N cap : ℕ) (w z : ℝ) :
    raw (policy4 d (N : ℝ)) N cap w z -
      raw (original4 d (N : ℝ)) N cap w z = rawCorrection d N cap w z := by
  have h := common4_sub_original_eq_correction d (N : ℝ)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun _ _ => 1) (roughPrimeUniverse N cap w z)
  rw [signedTest_one_eq_polynomial, signedTest_one_eq_polynomial,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (policy4_even d (N : ℝ)) N cap w z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (original4_even d (N : ℝ)) N cap w z] at h
  exact h

def originalFourthSaving (d : OriginalData) (N cap : ℕ) (z : ℝ) : ℝ :=
  actualHistoricalFourthSaving
    (HistoricalThirdCoarse.initialPolicy (d.e : ℝ) d.m (N : ℝ))
    (HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ))
    (P1OriginalVariableFourthContinuation.producerLevel4
      (d.e : ℝ) d.chi d.m d.omega (N : ℝ) d.rows4 d.licensed4) N cap z

def originalFourthIntegral (d : OriginalData) : ℝ :=
  P1OriginalVariableFourthFullActiveIntegral.fullActiveIntegral
    d.e d.chi d.m d.omega d.rows4 d.licensed4

/-- Original firstStop/rawQ3 baseline minus the original full fourth
charge, plus the only genuine common-parent correction. -/
theorem common4_raw_original_ledger (d : OriginalData) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (z : ℝ) :
    raw (policy4 d (N : ℝ)) N cap 0 z =
      raw (old3 d (N : ℝ)) N cap 0 z - originalFourthSaving d N cap z +
        rawCorrection d N cap 0 z := by
  have ho := P1OriginalVariableFourthSourceCoefficient.original_policy_difference_eq_fourth_saving
    (d.e : ℝ) d.chi d.m d.omega N cap z d.rows4 d.licensed4 hN
  rw [UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (HistoricalThirdCoarse.policy_even (d.e : ℝ) d.chi d.m d.omega (N : ℝ)) N cap 0 z,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      _ (original4_even d (N : ℝ)) N cap 0 z] at ho
  change raw (old3 d (N : ℝ)) N cap 0 z - raw (original4 d (N : ℝ)) N cap 0 z =
    originalFourthSaving d N cap z at ho
  linarith [common4_raw_sub_original d N cap 0 z]

/-- Count/mean source telescope reaches the SAME final rho. The original
fourth source appears once; the common-parent correction appears once. -/
theorem final_rho_source_original_fourth (d : OriginalData) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ moduli d N cap w z, rho d N cap w z L q * G q) =
      (∑ q ∈ actualSmallRoughModuli ((original4 d (N : ℝ)) false) N cap w z,
        actualSmallRoughRho ((original4 d (N : ℝ)) false) N cap w z L q * G q) +
      physicalCorrection d N cap w z L G + sourceChange d .fifth N cap w z L G +
        sourceChange d .sixth N cap w z L G + sourceChange d .eighth N cap w z L G := by
  have h4 := source_next_sub_current d .fourth N cap w z L G
  have hc := common4_physical_source_sub_original d N cap w z L G
  have ht := actual_source_telescope d N cap w z L G
  simp only [nextStage, parentStage] at h4
  linarith

/-- This is the actual original fourth integral theorem, with its original
fine-mesh condition and fixed source. No common-fourth endpoint is assumed. -/
theorem eventually_original_fourth_error (d : OriginalData) (he : 0 ≤ d.e)
    (homega : 0 < d.omega) (homegaRho : d.omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) d.m ≤ d.omega / 2)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      |normalize N (originalFourthSaving d N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))) -
        originalFourthIntegral d| < eta := by
  simpa only [Real.dist_eq, normalize, originalFourthSaving, originalFourthIntegral] using
    Metric.tendsto_nhds.1
      (P1OriginalVariableFourthFullSourceMean.tendsto_normalizedActualSaving_fullActiveIntegral
        d.e he d.chi d.m d.omega homega homegaRho hmesh d.rows4 d.licensed4 cap hcap) eta heta

/-- H's actual positive-presieve fifth consumer with its unresolved common4
scalar replaced by an original source/integral ledger. A single epsilon
and N0 work for fifth and final rho; the above-mu correction and sixth/
eighth changes remain genuine signed source terms. -/
theorem exists_original_fourth_fifth_positive_ledger
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96)
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) ≤ omega / 2)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ))
    (nu eta epsilonMax : ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 ≤ (19 / 96 : ℝ) / nu ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let d := sourceData rows4 licensed4 e q chi omega
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (19 / 96 : ℝ)
        let L := (N : ℝ) ^ (nu * epsilon)
        let baseline := normalize N (raw (old3 d (N : ℝ)) N (cap N) 0 z) -
          originalFourthIntegral d - archiveFifthIntegral rows4 licensed4 e q chi omega +
          normalize N (rawCorrection d N (cap N) 0 z)
        1 < w ∧
          normalize N (physical (policy5 d (N : ℝ)) N (cap N) w z L) ≤ baseline + eta ∧
          normalize N (physicalDensitySum (moduli d N (cap N) w z)
            (rho d N (cap N) w z L)) ≤ baseline + laterRawLedger d N (cap N) z + eta := by
  let d := sourceData rows4 licensed4 e q chi omega
  obtain ⟨epsilon, heps, heps8, hepsMax, hepsr, NH, hNH, hH⟩ :=
    exists_archive_positive_presieve_integral_ledger rows4 licensed4 e he q chi omega
      homega homegaRho cap hcap nu (eta / 2) epsilonMax hnu (half_pos heta) hepsilonMax
  have hfour := eventually_original_fourth_error d he homega homegaRho hmesh
    cap hcap (eta / 2) (half_pos heta)
  rw [Filter.eventually_inf_principal] at hfour
  obtain ⟨N4, hN4⟩ := eventually_atTop.mp hfour
  refine ⟨epsilon, heps, heps8, hepsMax, hepsr,
    max NH N4, hNH.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNHN : NH ≤ N := (le_max_left _ _).trans hN
  have hN4N : N4 ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNH.trans hNHN
  have hF := (abs_lt.mp (hN4 N hN4N ⟨by omega, hEven⟩)).1
  have hB := hH N hNHN hEven
  dsimp only at hB ⊢
  have hB5 := hB.2.1
  have hB8 := hB.2.2
  have hraw := common4_raw_original_ledger d N (cap N)
    (by exact_mod_cast (show 1 ≤ N by omega)) ((N : ℝ) ^ (19 / 96 : ℝ))
  have hnorm := congrArg (normalize N) hraw
  rw [normalize_add, normalize_sub] at hnorm
  change normalize N (raw (policy4 d (N : ℝ)) N (cap N) 0 _) = _ at hnorm
  refine ⟨hB.1, ?_, ?_⟩
  · change normalize N (physical (policy5 d (N : ℝ)) N (cap N) _ _ _) ≤ _
    change normalize N (physical (policy5 d (N : ℝ)) N (cap N) _ _ _) ≤ _ at hB5
    linarith
  · change normalize N (physicalDensitySum (moduli d N (cap N) _ _)
      (rho d N (cap N) _ _ _)) ≤ _
    change normalize N (physicalDensitySum (moduli d N (cap N) _ _)
      (rho d N (cap N) _ _ _)) ≤ _ at hB8
    linarith

end
end ImbalancedChen.P5OriginalCommonFourthSourceLedger
