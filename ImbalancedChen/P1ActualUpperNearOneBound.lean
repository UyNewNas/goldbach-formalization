import ImbalancedChen.ActualRosserInitialResidualSaving
import ImbalancedChen.RosserCompactErrorAbsorption
import ImbalancedChen.ActualRosserBoundaryExpansion
import ImbalancedChen.ActualSmallEulerNormalization

/-!
# A genuine upper bound for the actual upper residual at the wall `s = 1`

This file keeps the literal actual coefficient, its strict level `ceil R`,
its prime carrier, and its singular-series normalization.  It does not use a
mean-value premise or a density-limit premise.

The arithmetic endpoint is handled by a finite-carrier observation.  For a
fixed natural level `D`, choose an auxiliary Suzuki parameter `t > 1` close
enough to one that every natural `p < D` still lies below
`ceil (D ^ (1/t))`.  The actual level and coefficient do not change.  The
source constants precede this auxiliary choice, and the existing scalar error
absorption is uniform for `t` in the closed interval `[1,2]`.  The canonical
upper factor on `1 < t <= 2` is bounded by `2 exp(gamma)`.

The resulting bound holds for every real `R >= y`, so it covers the complete
near-one interval and its endpoint.  The final tuple corollary is stated at
the literal natural four-prime product, ready for the rank-four dictionary.

Status: source_written / uncompiled.  No Lean, lake, or numerical replay was
run while preparing this candidate.
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

/-- Perturb only the analytic coordinate.  The natural Rosser level stays
exactly `D`, and every possible prime below `D` stays in the Suzuki cutoff. -/
theorem p1_exists_upper_parameter_preserving_natCeil_carrier
    (D : ℕ) (hD : 2 ≤ D) :
    ∃ t : ℝ, 1 < t ∧ t ≤ 2 ∧
      2 ≤ Nat.ceil ((D : ℝ) ^ (1 / t)) ∧
      ∀ p : ℕ, p < D → p < Nat.ceil ((D : ℝ) ^ (1 / t)) := by
  have hD0 : (D : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (show 0 < D by omega))
  have hc : ContinuousAt (fun t : ℝ => (D : ℝ) ^ (1 / t)) 1 := by
    apply ContinuousAt.rpow continuousAt_const
    · exact continuousAt_const.div continuousAt_id (by norm_num)
    · exact Or.inl hD0
  obtain ⟨delta, hdelta, hnear⟩ :=
    Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  let d : ℝ := min delta 1 / 2
  let t : ℝ := 1 + d
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hddelta : d < delta := by
    have hm := min_le_left delta (1 : ℝ)
    dsimp [d]
    linarith
  have hd1 : d ≤ 1 / 2 := by
    have hm := min_le_right delta (1 : ℝ)
    dsimp [d]
    linarith
  have ht1 : 1 < t := by dsimp [t]; linarith
  have ht2 : t ≤ 2 := by dsimp [t]; linarith
  have hdist : dist t (1 : ℝ) < delta := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht1)]
    dsimp [t]
    linarith
  have hrootNear := hnear hdist
  simp only [one_div_one, Real.rpow_one, Real.dist_eq] at hrootNear
  have hroot : (D : ℝ) - 1 < (D : ℝ) ^ (1 / t) := by
    have hh := (abs_lt.mp hrootNear).1
    linarith
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hroot1 : (1 : ℝ) < (D : ℝ) ^ (1 / t) := by linarith
  have hz2 : 2 ≤ Nat.ceil ((D : ℝ) ^ (1 / t)) := by
    have hz : (1 : ℕ) < Nat.ceil ((D : ℝ) ^ (1 / t)) :=
      Nat.lt_ceil.mpr (by simpa only [Nat.cast_one] using hroot1)
    omega
  refine ⟨t, ht1, ht2, hz2, ?_⟩
  intro p hp
  have hp1 : (p : ℝ) + 1 ≤ D := by
    exact_mod_cast (Nat.succ_le_iff.mpr hp)
  exact Nat.lt_ceil.mpr (by linarith)

/-- The same actual upper density is nonnegative, including the legal wall
`R = y`.  This follows from the positive finite boundary expansion. -/
theorem p1_actualSmallRosserPlusDensity_nonneg
    (N cap : ℕ) (hEven : Even N) (y R : ℝ)
    (hcap : y ≤ (cap : ℝ)) (hR : 1 < R) (hyR : y ≤ R) :
    0 ≤ actualSmallRosserPlusDensity N cap y R := by
  have hlevel : ∀ p ∈ actualSmallPrimeFinset N cap y, (p : ℝ) < R :=
    fun p hp => (mem_actualSmallPrimeFinset.mp hp).2.2.2.trans_le hyR
  have hratio :
      0 ≤ actualSmallRosserPlusDensity N cap y R / actualSmallEulerProduct N cap y := by
    rw [actualSmallRosserPlusDensity_ratio_eq_one_add_boundary
      N cap hEven y R hcap hR hlevel]
    apply add_nonneg zero_le_one
    apply Finset.sum_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro s hs
    apply actualUpperRosserBoundaryTerm_nonneg N cap hEven y hq
    exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1).trans
      (Finset.filter_subset _ _)
  have hV := actualSmallEulerProduct_pos N cap y hEven
  have hmul := mul_nonneg hratio hV.le
  simpa only [div_mul_cancel₀ _ hV.ne'] using hmul

/-- One genuine arithmetic ratio bound works uniformly all the way to
`R = y`.  The threshold and constant precede the target, cap and real levels.
No compact set separated from one is used. -/
theorem exists_p1_actualSmallRosserPlusDensity_endpoint_euler_bound :
    ∃ Y : ℝ, 4 ≤ Y ∧
      ∀ N cap : ℕ, Even N → ∀ y R : ℝ,
        Y ≤ y → y ≤ R → y ≤ (cap : ℝ) →
          actualSmallRosserPlusDensity N cap y R ≤
            (2 * Real.exp Real.eulerMascheroniConstant + 1) *
              actualSmallEulerProduct N cap y := by
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
    exists_sourceSigma_fixed_lower_threshold (16 : ℝ) 2 (by norm_num)
  have herrEv := eventually_all_depth_suzuki_error_compact
    jr1965Section13HatLayers jr1965Section13HatSourceContract.toSection13HatContract
    (C := C) (K := K') (a := 1) (b := 2) (d := 16) (Δ := (1 / 2 : ℝ))
    (ρ := 1) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨DE, hDE⟩ := eventually_atTop.mp herrEv
  let Y : ℝ := max 4 (max Dσ DE)
  refine ⟨Y, le_max_left _ _, ?_⟩
  intro N cap hEven y R hY hyR hcap
  have hy4 : (4 : ℝ) ≤ y := (le_max_left _ _).trans hY
  let D : ℕ := Nat.ceil R
  let S := goldbachB8PlusBoundingSieve N hEven y
  have hRD : R ≤ (D : ℝ) := Nat.le_ceil _
  have hyD : y ≤ (D : ℝ) := hyR.trans hRD
  have hD2 : 2 ≤ D := by
    have htwo : (2 : ℝ) ≤ D := (by linarith : (2 : ℝ) ≤ y).trans hyD
    exact_mod_cast htwo
  obtain ⟨t, ht1, ht2, hz2, hpreserve⟩ :=
    p1_exists_upper_parameter_preserving_natCeil_carrier D hD2
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < Nat.ceil ((D : ℝ) ^ (1 / t)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ goldbachB10ProdPrimes N y :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    have hpy := prime_dvd_goldbachB10ProdPrimes_lt hprime hpdvd
    have hpD : p < D := Nat.lt_ceil.mpr (hpy.trans_le hyR)
    exact hpreserve p hpD
  have hlocal' : HasDimensionOneLocalProductBound S K' :=
    HasDimensionOneLocalProductBound.mono (hlocal N hEven y) hKK'
  have hDσD : Dσ ≤ (D : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hY.trans hyD))
  have hDED : DE ≤ (D : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hY.trans hyD))
  have htSigma : t ≤ sourceSigma (D : ℝ) 16 := ht2.trans (hDσ _ hDσD)
  have hmain := upperRosserDensity_at_natCeil_of_allDepth_of_one_lt
    jr1965Section13HatLayers jr1965Section13HatSourceContract S
    (hdepth S K' hK' hlocal') D t hD2 ht1 htSigma hz2 hcut
  have herr := hDE (D : ℝ) hDED
    (2 * S.prodPrimes.primeFactors.card + 1) t ⟨ht1.le, ht2⟩
  have hfactor : suzukiContinuousUpperFactor t ≤
      2 * Real.exp Real.eulerMascheroniConstant := by
    rw [suzukiContinuousUpperFactor_eq_initial_of_actual_limits t ht1 (by linarith)]
    apply (div_le_iff₀ (by linarith : 0 < t)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1.le
      (show 0 ≤ 2 * Real.exp Real.eulerMascheroniConstant by positivity)
  have hdict : actualSmallRosserPlusDensity N cap y R =
      S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) :=
    actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N cap hEven y R hcap
  have hVdict : actualSmallEulerProduct N cap y =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S :=
    actualSmallEulerProduct_eq_b8_sieveProductPrimeFactors N cap hEven y hcap
  rw [← hdict, ← hVdict] at hmain
  have hV0 := (actualSmallEulerProduct_pos N cap y hEven).le
  calc
    actualSmallRosserPlusDensity N cap y R ≤
        actualSmallEulerProduct N cap y *
          (suzukiContinuousUpperFactor t +
            C * Real.exp (Real.sqrt K') *
              errorEnvelope jr1965Section13HatLayers
                (2 * S.prodPrimes.primeFactors.card + 1) (D : ℝ) 16 t *
                  (Real.log (D : ℝ)) ^ (-(1 / 2 : ℝ))) := hmain
    _ ≤ actualSmallEulerProduct N cap y *
        (2 * Real.exp Real.eulerMascheroniConstant + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [herr.2]) hV0
    _ = _ := mul_comm _ _

/-- Uniform absolute bound in the manuscript normalization.  The sole
cutoff-size condition is `N^a <= y`, with fixed `a > 0`.  The residual level
may equal the prime cutoff, and no upper bound on it is needed. -/
theorem exists_p1_actualSmallRosserPlusDensity_endpoint_normalized_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ, ∀ y R : ℝ,
        (N : ℝ) ^ a ≤ y → y ≤ R → y ≤ (cap : ℝ) →
          |actualSmallRosserPlusDensity N cap y R *
            Real.log (N : ℝ) / singularSeries N| ≤ M := by
  obtain ⟨Y, hY4, hratio⟩ :=
    exists_p1_actualSmallRosserPlusDensity_endpoint_euler_bound
  obtain ⟨B, hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  let A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge : ∀ᶠ N : ℕ in atTop, Y ≤ (N : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop Y)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hlarge
  refine ⟨A * B / a, div_pos (mul_pos hA hB) ha,
    max N1 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap y R hay hyR hcap
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hYr : Y ≤ y :=
    (hN1 N ((le_max_left _ _).trans hN)).trans hay
  have hy4 : (4 : ℝ) ≤ y := hY4.trans hYr
  have hypos : 0 < y := by linarith
  have hR : 1 < R := (by linarith : (1 : ℝ) < y).trans_le hyR
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hloglower : a * Real.log (N : ℝ) ≤ Real.log y := by
    have hl := Real.log_le_log
      (Real.rpow_pos_of_pos (zero_lt_one.trans hNreal) a) hay
    simpa only [Real.log_rpow (zero_lt_one.trans hNreal)] using hl
  have hV0 := (actualSmallEulerProduct_pos N cap y hEven).le
  have hEuler' := hEuler N cap hNpos hEven y hy4 hcap
  have hEulerMul : actualSmallEulerProduct N cap y * Real.log y ≤
      B * singularSeries N := (div_le_iff₀ hlogy).mp hEuler'
  have hEulerNorm : actualSmallEulerProduct N cap y * Real.log (N : ℝ) /
      singularSeries N ≤ B / a := by
    apply (div_le_div_iff₀ (singularSeries_pos N) ha).mpr
    calc
      actualSmallEulerProduct N cap y * Real.log (N : ℝ) * a =
          actualSmallEulerProduct N cap y * (a * Real.log (N : ℝ)) := by ring
      _ ≤ actualSmallEulerProduct N cap y * Real.log y :=
        mul_le_mul_of_nonneg_left hloglower hV0
      _ ≤ B * singularSeries N := hEulerMul
  have hdensity := hratio N cap hEven y R hYr hyR hcap
  change actualSmallRosserPlusDensity N cap y R ≤
    A * actualSmallEulerProduct N cap y at hdensity
  have hnonneg : 0 ≤ actualSmallRosserPlusDensity N cap y R *
      Real.log (N : ℝ) / singularSeries N :=
    div_nonneg
      (mul_nonneg (p1_actualSmallRosserPlusDensity_nonneg
        N cap hEven y R hcap hR hyR) hlogN.le) (singularSeries_pos N).le
  rw [abs_of_nonneg hnonneg]
  calc
    actualSmallRosserPlusDensity N cap y R * Real.log (N : ℝ) / singularSeries N ≤
        (A * actualSmallEulerProduct N cap y) * Real.log (N : ℝ) / singularSeries N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdensity hlogN.le) (singularSeries_pos N).le
    _ = A * (actualSmallEulerProduct N cap y * Real.log (N : ℝ) /
        singularSeries N) := by ring
    _ ≤ A * (B / a) := mul_le_mul_of_nonneg_left hEulerNorm hA.le
    _ = A * B / a := by ring

/-- In particular the bound is uniform on `s >= 1`, hence on every closed
near-one strip `[1,1+delta]`; the endpoint is included without a margin. -/
theorem exists_p1_actualSmallRosserPlusDensity_nearOne_normalized_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ, ∀ u s : ℝ,
        a ≤ u → 1 ≤ s → (N : ℝ) ^ u ≤ (cap : ℝ) →
          |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u)
              ((N : ℝ) ^ (s * u)) * Real.log (N : ℝ) / singularSeries N| ≤ M := by
  obtain ⟨M, hM, N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_endpoint_normalized_bound a ha
  refine ⟨M, hM, N0, hN0, ?_⟩
  intro N hN hEven cap u s hau hs hcap
  have hNreal : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N from (by omega : 1 ≤ N0).trans hN)
  have hu : 0 < u := ha.trans_le hau
  apply hbound N hN hEven cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u))
  · exact Real.rpow_le_rpow_of_exponent_le hNreal hau
  · exact Real.rpow_le_rpow_of_exponent_le hNreal (by nlinarith)
  · exact hcap

/-- Literal rank-four quotient residual, with the same last-prime cutoff
and natural tuple product as `fourthTuplePlusResidualP1`.  Its bound requires
no extra own-cube test and no strict residual margin. -/
theorem exists_p1_fourthTuplePlusResidual_uniform_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ, ∀ p : Fin 4 → ℕ, ∀ lambda : ℝ,
        (N : ℝ) ^ a ≤ (p (Fin.last 3) : ℝ) →
        (p (Fin.last 3) : ℝ) ≤ (N : ℝ) ^ lambda / (∏ i, p i : ℕ) →
        (p (Fin.last 3) : ℝ) ≤ (cap : ℝ) →
          |actualSmallRosserPlusDensity N cap (p (Fin.last 3) : ℝ)
              ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) *
            Real.log (N : ℝ) / singularSeries N| ≤ M := by
  obtain ⟨M, hM, N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_endpoint_normalized_bound a ha
  exact ⟨M, hM, N0, hN0, fun N hN hEven cap p lambda hcut hlevel hcap =>
    hbound N hN hEven cap (p (Fin.last 3) : ℝ)
      ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) hcut hlevel hcap⟩

end

end ImbalancedChen
