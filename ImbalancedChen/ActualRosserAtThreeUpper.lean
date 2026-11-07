import ImbalancedChen.RosserEndpointBridge
import ImbalancedChen.RoughPowerParameters
import MathlibNt.SieveTheory.LiLiuGoldbachB8RosserFactor

/-!
# Sharp upper threshold for the same actual Rosser coefficients at three

The proved all-depth Suzuki estimate is applied at the literal level
`ceil (N^(3*u))`. The actual primes satisfy `p < N^u`, hence are strictly
below `ceil ((ceil (N^(3*u)))^(1/3))`, including integer endpoints.
The target-prime-deleted local product bound and the error bound uniform
in every odd depth are both supplied by proved provider theorems.
Constants and thresholds are selected before the target and covering cap.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- The actual coefficient at its strict natural ceiling has sharp upper
factor at three, for every later even target and every complete cap. -/
theorem exists_actualSmallRosserPlusDensity_at_three_sharp_upper_threshold
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
          2 * Real.exp Real.eulerMascheroniConstant / 3 + eta := by
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, _hC1min, hall⟩ :=
    exists_upperRosserDensity_at_natCeil_of_suzuki_allDepth
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_C145, _Clow, C, _hC145, _hClow, hC, hnat⟩ := hall C1min le_rfl
  obtain ⟨K, _hK, hlocal⟩ :=
    exists_goldbachB8PlusBoundingSieve_dimensionOneLocalProductBound
  let K' : ℝ := max 2 K
  have hK' : 2 ≤ K' := le_max_left _ _
  have hKK' : K ≤ K' := le_max_right _ _
  obtain ⟨Dσ, _hDσ1, hDσ⟩ :=
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) 4 (by norm_num)
  have herrEv := eventually_all_odd_depth_suzuki_error_upper_window
    jr1965Section13HatLayers jr1965Section13HatSourceContract.toSection13HatContract
    (C := C) (K := K') (d := 16) (Δ := (1 / 2 : ℝ)) (ρ := eta)
      (by linarith) (by norm_num) (by norm_num) heta
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
  let D : ℕ := Nat.ceil ((N : ℝ) ^ (3 * u))
  let S := goldbachB8PlusBoundingSieve N hEven ((N : ℝ) ^ u)
  have hyR : (N : ℝ) ^ u ≤ (N : ℝ) ^ (3 * u) :=
    Real.rpow_le_rpow_of_exponent_le hNreal.le (by linarith)
  have hRD : (N : ℝ) ^ (3 * u) ≤ (D : ℝ) := Nat.le_ceil _
  have hyD : (N : ℝ) ^ u ≤ (D : ℝ) := hyR.trans hRD
  have hD2 : 2 ≤ D := by exact_mod_cast hy2.trans hyD
  have hroot : ((N : ℝ) ^ (3 * u)) ^ (1 / 3 : ℝ) = (N : ℝ) ^ u := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  have hyroot : (N : ℝ) ^ u ≤ (D : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← hroot]
    exact Real.rpow_le_rpow (by positivity) hRD (by norm_num)
  have hz2 : 2 ≤ Nat.ceil ((D : ℝ) ^ (1 / 3 : ℝ)) := by
    have h : (1 : ℕ) < Nat.ceil ((D : ℝ) ^ (1 / 3 : ℝ)) := by
      apply Nat.lt_ceil.mpr
      simpa only [Nat.cast_one] using
        ((by linarith : (1 : ℝ) < (N : ℝ) ^ u).trans_le hyroot)
    omega
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < Nat.ceil ((D : ℝ) ^ (1 / 3 : ℝ)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N ((N : ℝ) ^ u) :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    have hpy := prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd
    exact Nat.lt_ceil.mpr (hpy.trans_le hyroot)
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono (hlocal N hEven ((N : ℝ) ^ u)) hKK'
  have hsSigma : (3 : ℝ) ≤ sourceSigma (D : ℝ) 16 :=
    (by norm_num : (3 : ℝ) ≤ 4).trans (hDσ _ (hyσ.trans hyD))
  have hmain := hnat S K' hK' hlocal' D hD2 3
    (by norm_num) (by norm_num) hsSigma hz2 hcut
  have hodd : Odd (2 * S.prodPrimes.primeFactors.card + 1) :=
    ⟨S.prodPrimes.primeFactors.card, by omega⟩
  have herr := hDE (D : ℝ) (hyE.trans hyD)
    (2 * S.prodPrimes.primeFactors.card + 1) hodd 3 (by norm_num) (by norm_num)
  have hfactor : suzukiContinuousUpperFactor 3 =
      2 * Real.exp Real.eulerMascheroniConstant / 3 := by
    rw [suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
      jr1965Section13HatLayers jr1965Section13HatSourceContract (by norm_num) (by norm_num)]
    norm_num [jurkatRichertUpperLinearSieveFactor]
  have hdict : actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) =
      S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) := by
    exact actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N cap hEven
      ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) hcap
  have hVdict : actualSmallEulerProduct N cap ((N : ℝ) ^ u) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
    actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors N cap hEven ((N : ℝ) ^ u) hcap
  rw [← hdict, ← hVdict, hfactor] at hmain
  have hVpos := actualSmallEulerProduct_pos N cap ((N : ℝ) ^ u) hEven
  apply (div_le_iff₀ hVpos).mpr
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (2 * Real.exp Real.eulerMascheroniConstant / 3)) herr.2.le) hVpos.le)
  simpa only [mul_comm] using hfinal

/-- Original level `R=N` and complete strict cutoff `N^(1/3)`. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_sharp_upper_threshold
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) ≤
          2 * Real.exp Real.eulerMascheroniConstant / 3 + eta := by
  simpa only [show (3 * (1 / 3 : ℝ)) = 1 by norm_num, Real.rpow_one] using
    exists_actualSmallRosserPlusDensity_at_three_sharp_upper_threshold
      (1 / 3) (by norm_num) eta heta

end

end ImbalancedChen
