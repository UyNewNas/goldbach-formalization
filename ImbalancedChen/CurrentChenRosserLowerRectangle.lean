import ImbalancedChen.CurrentChenRosserEndpointDictionary
import ImbalancedChen.RosserCompactErrorAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147JurkatRichertInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenAdaptiveDepthAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDensityBoundingSieveBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaElementaryHead
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
# Uniform lower Rosser rectangle on the actual initial Chen sieve

The same real prime cutoff, product, reciprocal-totient density and exact
natural ceiling level are retained. The proved canonical all-depth theorem
and Mertens local-product theorem supply the bound on the actual initial
prime-receiver sieve, with one threshold for the whole parameter rectangle.
Executed verification status is recorded in the continuation progress report.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
/-- The actual minus density estimate has one threshold on the whole rectangle. -/
theorem exists_currentChen_model_minusDensity_rectangle_lower_threshold
    (a : ℝ) (ha : 0 < a) (sigma : ℝ) (hsigma : 2 ≤ sigma)
    (B : ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ u : ℝ, a ≤ u → ∀ s : ℝ, sigma ≤ s → s ≤ B →
        ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
          suzukiContinuousLowerFactor s - eta ≤
            actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
              actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  by_cases hab : sigma ≤ B
  · have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
      constructor <;> norm_num
    obtain ⟨C1min, _hC1min, hall⟩ :=
      exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
        jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
    obtain ⟨_C145, _Clow, C, _hC145, _hClow, hC, hnat⟩ := hall C1min le_rfl
    obtain ⟨K, _hK, hlocal⟩ :=
      exists_currentChen_model_dimensionOneLocalProductBound
    let K' : ℝ := max 2 K
    have hK' : 2 ≤ K' := le_max_left _ _
    have hKK' : K ≤ K' := le_max_right _ _
    obtain ⟨Dσ, _hDσ1, hDσ⟩ :=
      exists_sourceSigma_fixed_lower_threshold (16 : ℝ) B (by norm_num)
    have herrEv := eventually_all_depth_suzuki_error_compact
      jr1965Section13HatLayers jr1965Section13HatSourceContract.toSection13HatContract
      (C := C) (K := K') (a := sigma) (b := B) (d := 16) (Δ := (1 / 2 : ℝ))
      (ρ := eta) (by linarith) (by linarith) hab (by norm_num) (by norm_num) heta
    obtain ⟨DE, hDE⟩ := eventually_atTop.mp herrEv
    let Y : ℝ := max 2 (max Dσ DE)
    have hlarge : ∀ᶠ N : ℕ in atTop, Y ≤ (N : ℝ) ^ a :=
      ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop Y)
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp hlarge
    refine ⟨max N1 2, le_max_right _ _, ?_⟩
    intro N hN hEven u hau s hslo hshi cap hcap
    have hu : 0 < u := ha.trans_le hau
    have hs : 2 ≤ s := hsigma.trans hslo
    have hspos : 0 < s := by linarith
    have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
    have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hY : Y ≤ (N : ℝ) ^ u :=
      (hN1 N ((le_max_left _ _).trans hN)).trans
        (Real.rpow_le_rpow_of_exponent_le hNreal.le hau)
    have hy2 : (2 : ℝ) ≤ (N : ℝ) ^ u := (le_max_left _ _).trans hY
    have hyσ : Dσ ≤ (N : ℝ) ^ u :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hY)
    have hyE : DE ≤ (N : ℝ) ^ u :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hY)
    let D : ℕ := Nat.ceil ((N : ℝ) ^ (s * u))
    let S := chenInitialBoundingSieve N ((N : ℝ) ^ u) hEven
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
      have hpS : p ∈ sievePrimes N (Nat.ceil ((N : ℝ) ^ u)) := by
        change p ∈ (chenInitialBoundingSieve N ((N : ℝ) ^ u) hEven).prodPrimes.primeFactors at hp
        rwa [currentChen_model_primeFactors N ((N : ℝ) ^ u) hEven] at hp
      have hpy := (mem_sievePrimes_chen_real_cap.mp hpS).1
      exact Nat.lt_ceil.mpr (hpy.trans_le hyroot)
    have hlocal' : HasDimensionOneLocalProductBound S K' :=
      MathlibNt.SieveTheory.hasDimensionOneLocalProductBound_mono_K (hlocal N hEven ((N : ℝ) ^ u)) hKK'
    have hsSigma : s ≤ sourceSigma (D : ℝ) 16 := hshi.trans (hDσ _ (hyσ.trans hyD))
    have hmain := hnat S K' hK' hlocal' D hD2 s hs hsSigma hz2
    change suzukiVProduct S (z : ℝ) *
        (suzukiContinuousLowerFactor s -
          C * Real.exp (Real.sqrt K') *
            errorEnvelope jr1965Section13HatLayers
              (2 * ((suzukiSupportedBelow S z).card + 1)) (D : ℝ) 16 s *
                (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
        lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) at hmain
    have herr := hDE (D : ℝ) (hyE.trans hyD)
      (2 * ((suzukiSupportedBelow S z).card + 1)) s ⟨hslo, hshi⟩
    have hdict : actualSmallRosserMinusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) =
        S.mainSum (LinearSieve.lowerRosserWeight S.prodPrimes D) := by
      exact currentChen_model_minusDensity_eq_mainSum N cap
        ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) hEven hcap
    have hVdict : actualSmallEulerProduct N cap ((N : ℝ) ^ u) =
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
      currentChen_model_actualEuler_eq_sieveEuler N cap ((N : ℝ) ^ u) hEven hcap
    have hVsuzuki : suzukiVProduct S (z : ℝ) =
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
      apply suzukiVProduct_eq_sieveProductPrimeFactors_of_all_lt
      intro p hp
      exact_mod_cast hcut p hp
    rw [← mainSum_lowerRosserWeight_eq_suzukiLowerDensity_of_all_lt S D hcut,
      ← hdict, hVsuzuki, ← hVdict] at hmain
    have hVpos := currentChen_model_actualEuler_pos N cap ((N : ℝ) ^ u) hEven
    apply (le_div_iff₀ hVpos).mpr
    have hfinal := (mul_le_mul_of_nonneg_left
      (sub_le_sub_left herr.2.le (suzukiContinuousLowerFactor s)) hVpos.le).trans hmain
    simpa only [mul_comm] using hfinal
  · refine ⟨2, le_rfl, ?_⟩
    intro N _hN _hEven u _hu s hslo hshi cap _hcap
    exact (hab (hslo.trans hshi)).elim

end

end ImbalancedChen
