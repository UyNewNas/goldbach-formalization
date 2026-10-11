import ImbalancedChen.RosserEndpointBridge
import ImbalancedChen.RoughPowerParameters
import MathlibNt.SieveTheory.LiLiuGoldbachB8RosserFactor
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147JurkatRichertInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenAdaptiveDepthAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDensityBoundingSieveBridge

/-!
# Lower thresholds for the same actual Rosser coefficients

The uniform-in-sieve literal all-depth lower estimate is applied at
`ceil (N^(s*u))`.  The actual prime carrier consists of the primes below
`N^u` not dividing the target.  Its dimension-one bound and the adaptive-depth
error estimate are supplied by proved provider theorems.  Every constant and
threshold is chosen before the target and the covering enumeration cap.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- At any fixed legal lower-sieve parameter, the literal actual minus density
is eventually at least the continuous lower factor minus any positive error.
The same threshold works for every cap covering the strict prime cutoff. -/
theorem exists_actualSmallRosserMinusDensity_lower_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        suzukiContinuousLowerFactor s - eta ≤
          actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hspos : 0 < s := by linarith
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, _hC1min, hall⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_C145, _Clow, C, _hC145, _hClow, hC, hnat⟩ := hall C1min le_rfl
  obtain ⟨K, _hK, hlocal⟩ :=
    exists_goldbachB8PlusBoundingSieve_dimensionOneLocalProductBound
  let K' : ℝ := max 2 K
  have hK' : 2 ≤ K' := le_max_left _ _
  have hKK' : K ≤ K' := le_max_right _ _
  obtain ⟨Dσ, _hDσ1, hDσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) s (by norm_num)
  have herrEv := eventually_all_depth_suzuki_error_half
    jr1965Section13HatLayers jr1965Section13HatSourceContract.toSection13HatContract
    (C := C) (K := K') (s := s) (by linarith) hspos eta heta
  obtain ⟨DE, hDE⟩ := eventually_atTop.mp herrEv
  let Y : ℝ := max 2 (max Dσ DE)
  have hlarge : ∀ᶠ N : ℕ in atTop, Y ≤ (N : ℝ) ^ u :=
    ((tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop Y)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hlarge
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap hcap
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hY : Y ≤ (N : ℝ) ^ u := hN1 N ((le_max_left _ _).trans hN)
  have hy2 : (2 : ℝ) ≤ (N : ℝ) ^ u := (le_max_left _ _).trans hY
  have hyσ : Dσ ≤ (N : ℝ) ^ u :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hyE : DE ≤ (N : ℝ) ^ u :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  let D : ℕ := Nat.ceil ((N : ℝ) ^ (s * u))
  let S := goldbachB8PlusBoundingSieve N hEven ((N : ℝ) ^ u)
  have hyR : (N : ℝ) ^ u ≤ (N : ℝ) ^ (s * u) :=
    Real.rpow_le_rpow_of_exponent_le hNreal.le (by nlinarith)
  have hRD : (N : ℝ) ^ (s * u) ≤ (D : ℝ) := Nat.le_ceil _
  have hyD : (N : ℝ) ^ u ≤ (D : ℝ) := hyR.trans hRD
  have hD2 : 2 ≤ D := by exact_mod_cast hy2.trans hyD
  have hroot : ((N : ℝ) ^ (s * u)) ^ (1 / s) = (N : ℝ) ^ u := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    field_simp
  have hyroot : (N : ℝ) ^ u ≤ (D : ℝ) ^ (1 / s) := by
    rw [← hroot]
    exact Real.rpow_le_rpow (by positivity) hRD (by positivity)
  let z : ℕ := Nat.ceil ((D : ℝ) ^ (1 / s))
  have hz2 : 2 ≤ z := by
    have h : (1 : ℕ) < Nat.ceil ((D : ℝ) ^ (1 / s)) := by
      apply Nat.lt_ceil.mpr
      simpa only [Nat.cast_one] using
        ((by linarith : (1 : ℝ) < (N : ℝ) ^ u).trans_le hyroot)
    omega
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors, p < z := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N ((N : ℝ) ^ u) :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    have hpy := prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd
    exact Nat.lt_ceil.mpr (hpy.trans_le hyroot)
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono (hlocal N hEven ((N : ℝ) ^ u)) hKK'
  have hsSigma : s ≤ sourceSigma (D : ℝ) 16 := hDσ _ (hyσ.trans hyD)
  have hmain := hnat S K' hK' hlocal' D hD2 s hs hsSigma hz2
  change suzukiVProduct S (z : ℝ) *
      (suzukiContinuousLowerFactor s -
        C * Real.exp (Real.sqrt K') *
          errorEnvelope jr1965Section13HatLayers
            (2 * ((suzukiSupportedBelow S z).card + 1)) (D : ℝ) 16 s *
              (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) at hmain
  have herr := hDE (D : ℝ) (hyE.trans hyD)
    (2 * ((suzukiSupportedBelow S z).card + 1))
  have hdict : actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) =
      S.mainSum (LinearSieve.lowerRosserWeight S.prodPrimes D) := by
    exact actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil N cap hEven
      ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) hcap
  have hVdict : actualSmallEulerProduct N cap ((N : ℝ) ^ u) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
    actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors N cap hEven ((N : ℝ) ^ u) hcap
  have hVsuzuki : suzukiVProduct S (z : ℝ) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    apply suzukiVProduct_eq_sieveProductPrimeFactors_of_all_lt
    intro p hp
    exact_mod_cast hcut p hp
  rw [← mainSum_lowerRosserWeight_eq_suzukiLowerDensity_of_all_lt S D hcut,
    ← hdict, hVsuzuki, ← hVdict] at hmain
  have hVpos := actualSmallEulerProduct_pos N cap ((N : ℝ) ^ u) hEven
  apply (le_div_iff₀ hVpos).mpr
  have hfinal := (mul_le_mul_of_nonneg_left
    (sub_le_sub_left herr.2.le (suzukiContinuousLowerFactor s)) hVpos.le).trans hmain
  simpa only [mul_comm] using hfinal

/-- The first-interval version uses the exact source normalization, including
both endpoints `s=2` and `s=4`. -/
theorem exists_actualSmallRosserMinusDensity_firstInterval_sharp_lower_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s - eta ≤
          actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hfactor : suzukiContinuousLowerFactor s =
      2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
    rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
      one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
        jr1965Section13HatSourceContract hs hs4,
      suzukiLowerSieveFactorFirstInterval_eq_log hs hs4,
      suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
        jr1965Section13HatSourceContract]
  simpa only [hfactor] using
    exists_actualSmallRosserMinusDensity_lower_threshold u hu s hs eta heta

end

end ImbalancedChen
