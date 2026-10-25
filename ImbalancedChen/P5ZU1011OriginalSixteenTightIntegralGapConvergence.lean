import ImbalancedChen.P5ZU1011OriginalSixteenTightDensityDiagonal
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine diagonal convergence of the explicit original16 rational gap

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The functions integrated below are the ACTUAL finite rational programs.
Generated Ico ownership identifies their values with their owner-cell
coefficients. Actual source/eligibility/query wall nullity supplies AE
pointwise convergence; the formula-derived fixed density bound supplies
domination on the original cube. Dominated convergence therefore proves
that rationalUpper(n,n+1)-rationalLower(n,n+1) tends to zero.

No integral-gap, cell-error, boundary-mass, domination, H248 agreement or
mean premise is an input. No concrete numerical instance is evaluated,
and no saved endpoint is claimed to pass.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightIntegralGapConvergence

noncomputable section

open Set MeasureTheory Filter Topology U11Integral
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open U1011OriginalSixteenTightGridLocalGeometry U1011OriginalSixteenTightOrdinaryEndpointLimits
open U1011OriginalSixteenTightDensityDiagonal U1011OriginalSixteenTightUniformBounds
open U1011OriginalSixteenTightRationalIntegralCertificates
open U1011OriginalSixteenRationalIntegralCertificates (cell_constant_integrable integral_cell_constant)
open Classical
open scoped BigOperators

def lowerSample (n : ℕ) (v : LogFour) : ℝ :=
  ∑ j ∈ inner n, (cell n j).indicator (fun _ => (densityLower n (n + 1) j : ℝ)) v
def upperSample (n : ℕ) (v : LogFour) : ℝ :=
  ∑ j ∈ outer n, (cell n j).indicator (fun _ => (densityUpper n (n + 1) j : ℝ)) v
def sampleGap (n : ℕ) (v : LogFour) : ℝ := upperSample n v - lowerSample n v

private theorem sample_eq_owner (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ)
    {v : LogFour} (hv : v ∈ cube) :
    (∑ j ∈ S, (cell n j).indicator (fun _ => (q j : ℝ)) v) =
      if owner n v ∈ S then (q (owner n v) : ℝ) else 0 := by
  by_cases ho : owner n v ∈ S
  · rw [if_pos ho, Finset.sum_eq_single (owner n v)]
    · exact indicator_of_mem (owner_mem n hv) _
    · intro j hj hjo
      exact indicator_of_notMem (fun hcell => hjo (owner_unique n hv hcell)) _
    · intro hn
      exact (hn ho).elim
  · rw [if_neg ho]
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : v ∉ cell n j := by
      intro hcell
      have heq := owner_unique n hv hcell
      exact ho (heq ▸ hj)
    exact indicator_of_notMem hnot _

private theorem sample_eq_zero_outside (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ)
    {v : LogFour} (hv : v ∉ cube) :
    (∑ j ∈ S, (cell n j).indicator (fun _ => (q j : ℝ)) v) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply indicator_of_notMem
  intro hcell
  apply hv
  rw [← cells_union n]
  exact mem_iUnion.mpr ⟨j, hcell⟩

private theorem sample_abs_bound (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ)
    (hq : ∀ j, 0 ≤ q j ∧ q j ≤ densityBound) (v : LogFour) :
    |∑ j ∈ S, (cell n j).indicator (fun _ => (q j : ℝ)) v| ≤
      cube.indicator (fun _ => (densityBound : ℝ)) v := by
  by_cases hv : v ∈ cube
  · rw [sample_eq_owner n S q hv, indicator_of_mem hv]
    by_cases ho : owner n v ∈ S
    · rw [if_pos ho, abs_of_nonneg (by exact_mod_cast (hq (owner n v)).1)]
      exact_mod_cast (hq (owner n v)).2
    · rw [if_neg ho, abs_zero]
      exact_mod_cast densityBound_nonneg
  · simp only [sample_eq_zero_outside n S q hv, indicator_of_notMem hv, abs_zero, le_refl]

def domination (v : LogFour) : ℝ := cube.indicator (fun _ => 2 * (densityBound : ℝ)) v

theorem lowerSample_integrable (n : ℕ) : Integrable (lowerSample n) :=
  integrable_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)
theorem upperSample_integrable (n : ℕ) : Integrable (upperSample n) :=
  integrable_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)
theorem sampleGap_integrable (n : ℕ) : Integrable (sampleGap n) :=
  (upperSample_integrable n).sub (lowerSample_integrable n)

theorem sampleGap_dominated (n : ℕ) (v : LogFour) : ‖sampleGap n v‖ ≤ domination v := by
  have hL := sample_abs_bound n (inner n) (fun j => densityLower n (n + 1) j)
    (fun j => ⟨(generated_density_bounds n (n + 1) (by omega) j).1,
      (generated_density_bounds n (n + 1) (by omega) j).2.1⟩) v
  have hU := sample_abs_bound n (outer n) (fun j => densityUpper n (n + 1) j)
    (fun j => ⟨(generated_density_bounds n (n + 1) (by omega) j).2.2.1,
      (generated_density_bounds n (n + 1) (by omega) j).2.2.2⟩) v
  have h := (abs_sub_le (upperSample n v) (lowerSample n v)).trans (add_le_add hU hL)
  rw [Real.norm_eq_abs]
  change |upperSample n v - lowerSample n v| ≤ domination v
  by_cases hv : v ∈ cube
  · simpa only [domination, indicator_of_mem hv, two_mul] using h
  · simpa only [domination, indicator_of_notMem hv, add_zero] using h

theorem domination_integrable : Integrable domination := by
  have hc : IntegrableOn (fun _ : LogFour => 2 * (densityBound : ℝ))
      (Icc (fun _ : Fin 4 => (a : ℝ)) (fun _ => (b : ℝ))) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hsub : cube ⊆ Icc (fun _ : Fin 4 => (a : ℝ)) (fun _ => (b : ℝ)) := by
    intro v hv
    have h := mem_logPrimeBox.mp hv
    exact ⟨fun i => (h i).1, fun i => (h i).2.le⟩
  exact (hc.mono_set hsub).integrable_indicator (measurableSet_logPrimeBox _ _)

theorem sampleGap_tendsto_zero (v : LogFour)
    (hsource : ∀ i : Fin 6, sourceForms i v ≠ sourceBounds i)
    (helig : ∀ p : Policy, ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g)
    (hquery : ∀ p : Policy, v 3 ≠ 0 → OriginalSixteenSingleStateLocal.OffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => sampleGap n v) atTop (𝓝 0) := by
  by_cases hc : v ∈ cube
  · by_cases hv : v ∈ sourceDomain
    · have hw : v 3 ≠ 0 := (originalDomain_denominators_pos ∅ v hv).1.ne'
      have ht := diagonal_density_gap_tendsto hv hc helig (fun p => hquery p hw)
      apply ht.congr'
      filter_upwards [eventually_owner_inner hv hc hsource] with n hn
      have ho := domain_cell_is_outer n hv (owner_mem n hc)
      rw [sampleGap, upperSample, lowerSample,
        sample_eq_owner n (outer n) (fun j => densityUpper n (n + 1) j) hc,
        sample_eq_owner n (inner n) (fun j => densityLower n (n + 1) j) hc,
        if_pos ho, if_pos hn, Rat.cast_sub]
    · have hni (n : ℕ) : owner n v ∉ inner n :=
        fun hi => hv (inner_cell_subset_domain n hi (owner_mem n hc))
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_owner_not_outer hv hc hsource] with n hn
      rw [sampleGap, upperSample, lowerSample,
        sample_eq_owner n (outer n) (fun j => densityUpper n (n + 1) j) hc,
        sample_eq_owner n (inner n) (fun j => densityLower n (n + 1) j) hc,
        if_neg hn, if_neg (hni n), sub_self]
  · apply tendsto_const_nhds.congr
    intro n
    rw [sampleGap, upperSample, lowerSample,
      sample_eq_zero_outside n (outer n) (fun j => densityUpper n (n + 1) j) hc,
      sample_eq_zero_outside n (inner n) (fun j => densityLower n (n + 1) j) hc,
      sub_self]

theorem ae_sampleGap_tendsto_zero :
    ∀ᵐ v : LogFour ∂volume, Tendsto (fun n => sampleGap n v) atTop (𝓝 0) := by
  filter_upwards [ae_no_actual_source_walls, ae_no_actual_eligibility_walls,
    ae_actual_ratio_offKnots] with v hs he hq
  exact sampleGap_tendsto_zero v hs he hq

theorem integral_sampleGap_eq (n : ℕ) :
    (∫ v, sampleGap n v) = ((rationalUpper n (n + 1) - rationalLower n (n + 1) : ℚ) : ℝ) := by
  have hU : (∫ v, upperSample n v) = (rationalUpper n (n + 1) : ℝ) := by
    rw [upperSample, integral_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)]
    calc
      (∑ j ∈ outer n, ∫ v, (cell n j).indicator (fun _ => (densityUpper n (n + 1) j : ℝ)) v) =
          ∑ j ∈ outer n, ((densityUpper n (n + 1) j * cellVolume n : ℚ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact integral_cell_constant n j _
      _ = (rationalUpper n (n + 1) : ℝ) := by simp [rationalUpper]
  have hL : (∫ v, lowerSample n v) = (rationalLower n (n + 1) : ℝ) := by
    rw [lowerSample, integral_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)]
    calc
      (∑ j ∈ inner n, ∫ v, (cell n j).indicator (fun _ => (densityLower n (n + 1) j : ℝ)) v) =
          ∑ j ∈ inner n, ((densityLower n (n + 1) j * cellVolume n : ℚ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact integral_cell_constant n j _
      _ = (rationalLower n (n + 1) : ℝ) := by simp [rationalLower]
  rw [sampleGap, integral_sub (upperSample_integrable n) (lowerSample_integrable n), hU, hL, Rat.cast_sub]

/-- The requested TRUE diagonal gap limit for the explicit automatic
original16 rational program. All AE geometry, domination and endpoint
limits are supplied by actual source proofs above, not by hypotheses. -/
theorem tendsto_diagonal_rational_enclosure_gap :
    Tendsto (fun n : ℕ => ((rationalUpper n (n + 1) - rationalLower n (n + 1) : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence domination
    (fun n => (sampleGap_integrable n).aestronglyMeasurable) domination_integrable
    (fun n => Eventually.of_forall (sampleGap_dominated n)) ae_sampleGap_tendsto_zero
  simpa only [integral_sampleGap_eq, integral_zero] using ht

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightIntegralGapConvergence
