import ImbalancedChen.ActualRosserLowerThreshold
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserAllDepth
import ImbalancedChen.RosserEndpointBridge
import ImbalancedChen.RoughPowerParameters
import MathlibNt.SieveTheory.LiLiuGoldbachB8RosserFactor
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147JurkatRichertInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenAdaptiveDepthAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDensityBoundingSieveBridge

/-!
# Actual upper Rosser density at every fixed legal parameter

The moving-range all-depth estimate is used at the literal natural ceiling.
The finite odd source sum is bounded by its genuine convergent full series;
no restriction to an initial interval or piecewise factor is imposed.
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

/-- The all-depth natural-ceiling consumer on its full legal odd parity domain. -/
theorem upperRosserDensity_at_natCeil_of_allDepth_of_one_lt
    (H : Section13HatLayers) (hH : Section13HatSourceContract H)
    (S : BoundingSieve)
    {C K d Δ : ℝ} (hall : ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2)
    (D : ℕ) (s : ℝ)
    (hD : 2 ≤ D) (hs : 1 < s)
    (hsSigma : s ≤ sourceSigma (D : ℝ) d)
    (hz2 : 2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let m : ℕ := S.prodPrimes.primeFactors.card
  let N : ℕ := 2 * m + 1
  have hNodd : Odd N := by dsimp [N]; exact ⟨m, by omega⟩
  have hN1 : 1 ≤ N := by dsimp [N]; omega
  have hsdom : s ∈ KappaOneModel.parityDomain 2 N := by
    simp [KappaOneModel.parityDomain, Nat.odd_iff.mp hNodd]
    linarith
  have hSuzuki := hall N hN1 D (by omega) hD s hsdom hsSigma hz2
  have hfinite := finiteSourceLayer_odd_le_suzukiContinuousUpperFactor_sub_one
    H hH m (by linarith : 1 < s)
  have hVeq : suzukiVProduct S (z : ℝ) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    unfold suzukiVProduct
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · intro hp
      exact ⟨hp, by simpa [z] using hcut p hp⟩
  have hzD : z ≤ D := by
    apply Nat.ceil_le.mpr
    have hbase : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hexp : 1 / s ≤ (1 : ℝ) := by
      rw [div_le_one (by linarith : 0 < s)]
      linarith
    simpa [z] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact lt_of_lt_of_le (hcut p hp) hzD
  have hexact := upperRosserSuzukiExactBridge S D z (by omega) hlevel
    (by simpa [z] using hcut)
  dsimp only [N, m, z] at hSuzuki hexact ⊢
  rw [hVeq] at hSuzuki
  have hprod : 0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    rw [← hVeq]
    exact (suzukiVProduct_pos S (z : ℝ)).le
  calc
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          suzukiActualT S
            (2 * S.prodPrimes.primeFactors.card + 1) D z := by
              simpa [z] using hexact
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (finiteSourceLayer 1 2
              (2 * S.prodPrimes.primeFactors.card + 1) s +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H
                (2 * S.prodPrimes.primeFactors.card + 1)
                (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          gcongr
    _ ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (suzukiContinuousUpperFactor s +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H
              (2 * S.prodPrimes.primeFactors.card + 1)
              (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
          have hf := hfinite
          dsimp [m] at hf
          nlinarith


/-- A fixed-parameter threshold for the actual coefficient, uniform over covering caps. -/
theorem exists_actualSmallRosserPlusDensity_general_upper_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 1 < s) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
          suzukiContinuousUpperFactor s + eta := by
  have hspos : 0 < s := by linarith
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  obtain ⟨C1min, _hC1min, hall⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
  obtain ⟨_C145, _Clow, C, _hC145, _hClow, hC, hdepth⟩ := hall C1min le_rfl
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
  have hmain := upperRosserDensity_at_natCeil_of_allDepth_of_one_lt
    jr1965Section13HatLayers jr1965Section13HatSourceContract S
    (hdepth S K' hK' hlocal') D s hD2 hs hsSigma hz2 hcut
  have herr := hDE (D : ℝ) (hyE.trans hyD)
    (2 * S.prodPrimes.primeFactors.card + 1)
  have hdict : actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) =
      S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) := by
    exact actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N cap hEven
      ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) hcap
  have hVdict : actualSmallEulerProduct N cap ((N : ℝ) ^ u) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
    actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors N cap hEven ((N : ℝ) ^ u) hcap
  rw [← hdict, ← hVdict] at hmain
  have hVpos := actualSmallEulerProduct_pos N cap ((N : ℝ) ^ u) hEven
  apply (div_le_iff₀ hVpos).mpr
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (suzukiContinuousUpperFactor s)) herr.2.le) hVpos.le)
  simpa only [mul_comm] using hfinal

end

end ImbalancedChen
