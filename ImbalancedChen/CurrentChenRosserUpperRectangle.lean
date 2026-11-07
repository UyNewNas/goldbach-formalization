import ImbalancedChen.CurrentChenRosserUpperEndpointDictionary
import ImbalancedChen.RosserCompactErrorAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserAllDepth
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
# Uniform upper Rosser rectangle on the actual initial Chen sieve

This is the genuine canonical all-depth upper theorem on the literal
initial prime receiver, transported using the exact actual coefficient,
prime product and Euler dictionaries. The Mertens dimension-one bound
and every adaptive depth are paid before selecting a point of the compact
parameter rectangle. No upper-density or distribution premise is added.
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

/-- The all-depth natural-ceiling consumer on its full legal odd parity domain. -/
private theorem currentChen_model_upper_at_natCeil_allDepth_one_lt
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


/-- The actual plus density estimate has one threshold on the whole rectangle. -/
theorem exists_currentChen_model_plusDensity_rectangle_upper_threshold
    (a : ℝ) (ha : 0 < a) (sigma : ℝ) (hsigma : 1 < sigma)
    (B : ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ u : ℝ, a ≤ u → ∀ s : ℝ, sigma ≤ s → s ≤ B →
        ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
              actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
            suzukiContinuousUpperFactor s + eta := by
  by_cases hab : sigma ≤ B
  · have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
      constructor <;> norm_num
    obtain ⟨C1min, _hC1min, hall⟩ :=
      exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source
        jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc
    obtain ⟨_C145, _Clow, C, _hC145, _hClow, hC, hdepth⟩ := hall C1min le_rfl
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
    have hs : 1 < s := hsigma.trans_le hslo
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
    have hmain := currentChen_model_upper_at_natCeil_allDepth_one_lt
      jr1965Section13HatLayers jr1965Section13HatSourceContract S
      (hdepth S K' hK' hlocal') D s hD2 hs hsSigma hz2 hcut
    have herr := hDE (D : ℝ) (hyE.trans hyD)
      (2 * S.prodPrimes.primeFactors.card + 1) s ⟨hslo, hshi⟩
    have hdict : actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) =
        S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) := by
      exact currentChen_model_plusDensity_eq_mainSum N cap
        ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) hEven hcap
    have hVdict : actualSmallEulerProduct N cap ((N : ℝ) ^ u) =
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
      currentChen_model_actualEuler_eq_sieveEuler N cap ((N : ℝ) ^ u) hEven hcap
    rw [← hdict, ← hVdict] at hmain
    have hVpos := currentChen_model_actualEuler_pos N cap ((N : ℝ) ^ u) hEven
    apply (div_le_iff₀ hVpos).mpr
    have hfinal := hmain.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (suzukiContinuousUpperFactor s)) herr.2.le) hVpos.le)
    simpa only [mul_comm] using hfinal
  · refine ⟨2, le_rfl, ?_⟩
    intro N _hN _hEven u _hu s hslo hshi cap _hcap
    exact (hab (hslo.trans hshi)).elim


end

end ImbalancedChen
