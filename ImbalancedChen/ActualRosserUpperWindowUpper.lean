import ImbalancedChen.ActualRosserAtThreeUpper

/-!
# An actual upper-density threshold uniform in a residual window

The all-depth supplier constants and errors precede the sieve carrier.
Consequently one target threshold works simultaneously for all exponents
bounded below by a fixed positive exponent, all residuals in `[3/2,4]`,
and every covering enumeration cap. The level remains the literal ceiling.
This is a uniform one-sided bound, not a uniform two-sided limit.
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

/-- One threshold works for all `u>=a`, all `s` in `[3/2,4]`, and all caps
covering `N^u`. No upper bound on the exponent is required. -/
theorem exists_actualSmallRosserPlusDensity_upperWindow_uniform_upper_threshold
    (a : ℝ) (ha : 0 < a) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ u : ℝ, a ≤ u → ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        ∀ s : ℝ, 3 / 2 ≤ s → s ≤ 4 →
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
              actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
            jurkatRichertUpperLinearSieveFactor s + eta := by
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
  have hlarge : ∀ᶠ N : ℕ in atTop, Y ≤ (N : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop Y)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hlarge
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN hEven u hau cap hcap s hslo hshi
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hu : 0 < u := ha.trans_le hau
  have hspos : 0 < s := by linarith
  have hY : Y ≤ (N : ℝ) ^ u :=
    (hN1 N ((le_max_left _ _).trans hN)).trans
      (Real.rpow_le_rpow_of_exponent_le hNreal.le hau)
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
  have hz2 : 2 ≤ Nat.ceil ((D : ℝ) ^ (1 / s)) := by
    have h : (1 : ℕ) < Nat.ceil ((D : ℝ) ^ (1 / s)) := by
      apply Nat.lt_ceil.mpr
      simpa only [Nat.cast_one] using
        ((by linarith : (1 : ℝ) < (N : ℝ) ^ u).trans_le hyroot)
    omega
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < Nat.ceil ((D : ℝ) ^ (1 / s)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N ((N : ℝ) ^ u) :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact Nat.lt_ceil.mpr ((prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd).trans_le hyroot)
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono (hlocal N hEven ((N : ℝ) ^ u)) hKK'
  have hsSigma : s ≤ sourceSigma (D : ℝ) 16 := hshi.trans (hDσ _ (hyσ.trans hyD))
  have hmain := hnat S K' hK' hlocal' D hD2 s hslo hshi hsSigma hz2 hcut
  have hodd : Odd (2 * S.prodPrimes.primeFactors.card + 1) :=
    ⟨S.prodPrimes.primeFactors.card, by omega⟩
  have herr := hDE (D : ℝ) (hyE.trans hyD)
    (2 * S.prodPrimes.primeFactors.card + 1) hodd s hslo hshi
  have hfactor : suzukiContinuousUpperFactor s = jurkatRichertUpperLinearSieveFactor s :=
    suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
      jr1965Section13HatLayers jr1965Section13HatSourceContract hslo hshi
  have hdict : actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) =
      S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) :=
    actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N cap hEven
      ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) hcap
  have hVdict : actualSmallEulerProduct N cap ((N : ℝ) ^ u) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
    actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors N cap hEven ((N : ℝ) ^ u) hcap
  rw [← hdict, ← hVdict, hfactor] at hmain
  have hVpos := actualSmallEulerProduct_pos N cap ((N : ℝ) ^ u) hEven
  apply (div_le_iff₀ hVpos).mpr
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (jurkatRichertUpperLinearSieveFactor s)) herr.2.le) hVpos.le)
  simpa only [mul_comm] using hfinal

/-- Fixed-parameter specialization of the uniform upper threshold. -/
theorem exists_actualSmallRosserPlusDensity_upperWindow_upper_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hslo : 3 / 2 ≤ s) (hshi : s ≤ 4)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) ≤
          jurkatRichertUpperLinearSieveFactor s + eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_upperWindow_uniform_upper_threshold u hu eta heta
  exact ⟨N0, hN0, fun N hN hEven cap hcap => hbound N hN hEven u le_rfl cap hcap s hslo hshi⟩

end

end ImbalancedChen
