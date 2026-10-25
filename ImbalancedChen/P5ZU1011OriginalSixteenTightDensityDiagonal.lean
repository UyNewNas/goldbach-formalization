import ImbalancedChen.P5ZU1011OriginalSixteenTightUniformBounds

/-!
# Diagonal endpoint convergence with the actual prime-harmonic weight

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Actual computed minimum gap collapse and its pointwise actual-envelope
sandwich force BOTH cost endpoints to the true original nonlinear cost.
The generated reciprocal coordinate products converge to the genuine
harmonic weight. Thus BOTH computed weighted density endpoints converge
to the actual weighted kernel, and their diagonal difference tends zero.
Every limit is derived from the preceding actual-program primitives.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightDensityDiagonal

noncomputable section

open Set MeasureTheory Filter Topology U11Integral
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open U1011OriginalSixteenTightGridLocalGeometry U1011OriginalSixteenTightMinimumDiagonal
open U1011OriginalSixteenTightRationalIntegralCertificates
open U1011OriginalSixteenRationalIntegralCertificates (weight weightLower weightUpper weightedKernel actualEnvelope_nonneg)
open OriginalSixteenEnvelopeBoxBounds (actualEnvelope)
open OriginalSixteenSingleStateLocal
open scoped BigOperators

theorem generated_weight_endpoints_tendsto {v : LogFour} (hv : v ∈ cube) :
    Tendsto (fun n => (weightLower n (owner n v) : ℝ)) atTop (𝓝 (weight v)) ∧
      Tendsto (fun n => (weightUpper n (owner n v) : ℝ)) atTop (𝓝 (weight v)) := by
  have hpos (i : Fin 4) : v i ≠ 0 := by
    have h := (mem_logPrimeBox.mp hv i).1
    exact ne_of_gt (lt_of_lt_of_le (by norm_num [a] : (0 : ℝ) < (a : ℝ)) h)
  have hL (i : Fin 4) : Tendsto (fun n => 1 / ((gridBox n (owner n v)).hi i : ℝ)) atTop
      (𝓝 (1 / v i)) := tendsto_const_nhds.div (owner_hi_tendsto hv i) (hpos i)
  have hU (i : Fin 4) : Tendsto (fun n => 1 / ((gridBox n (owner n v)).lo i : ℝ)) atTop
      (𝓝 (1 / v i)) := tendsto_const_nhds.div (owner_lo_tendsto hv i) (hpos i)
  constructor
  · simpa only [weightLower, weight, Rat.cast_prod, Rat.cast_div, Rat.cast_one] using
      tendsto_finsetProd (Finset.univ : Finset (Fin 4)) (fun i _ => hL i)
  · simpa only [weightUpper, weight, Rat.cast_prod, Rat.cast_div, Rat.cast_one] using
      tendsto_finsetProd (Finset.univ : Finset (Fin 4)) (fun i _ => hU i)

theorem diagonal_cost_endpoints_tendsto {v : LogFour} (hv : v ∈ sourceDomain) (hc : v ∈ cube)
    (hno : ∀ p : Policy, ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g)
    (hqueries : ∀ p : Policy, OffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => (boxLower (n + 1) (gridBox n (owner n v)) : ℝ)) atTop (𝓝 (actualEnvelope v)) ∧
      Tendsto (fun n => (boxUpper (n + 1) (gridBox n (owner n v)) : ℝ)) atTop (𝓝 (actualEnvelope v)) := by
  have ht := diagonal_minimum_gap_tendsto hv hc hno hqueries
  have hb (n : ℕ) := box_bounds (n + 1) (by omega) (gridBox n (owner n v))
    (cell_subset_closedBox n (owner n v) (owner_mem n hc)) hv
  have hL (n : ℕ) : |(boxLower (n + 1) (gridBox n (owner n v)) : ℝ) - actualEnvelope v| ≤ diagonalGap n v := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hb n).1)]
    simp only [diagonalGap, Rat.cast_sub]
    linarith only [(hb n).2]
  have hU (n : ℕ) : |(boxUpper (n + 1) (gridBox n (owner n v)) : ℝ) - actualEnvelope v| ≤ diagonalGap n v := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hb n).2)]
    simp only [diagonalGap, Rat.cast_sub]
    linarith only [(hb n).1]
  constructor
  · rw [Metric.tendsto_nhds]
    intro eps heps
    filter_upwards [ht.eventually (gt_mem_nhds heps)] with n hn
    rw [Real.dist_eq]
    exact (hL n).trans_lt hn
  · rw [Metric.tendsto_nhds]
    intro eps heps
    filter_upwards [ht.eventually (gt_mem_nhds heps)] with n hn
    rw [Real.dist_eq]
    exact (hU n).trans_lt hn

theorem diagonal_density_endpoints_tendsto {v : LogFour} (hv : v ∈ sourceDomain) (hc : v ∈ cube)
    (hno : ∀ p : Policy, ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g)
    (hqueries : ∀ p : Policy, OffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => (densityLower n (n + 1) (owner n v) : ℝ)) atTop (𝓝 (weightedKernel v)) ∧
      Tendsto (fun n => (densityUpper n (n + 1) (owner n v) : ℝ)) atTop (𝓝 (weightedKernel v)) := by
  have hcost := diagonal_cost_endpoints_tendsto hv hc hno hqueries
  have hweight := generated_weight_endpoints_tendsto hc
  have hE0 := actualEnvelope_nonneg hv
  have hL := ((tendsto_const_nhds (x := (0 : ℝ))).max hcost.1).mul hweight.1
  have hU := ((tendsto_const_nhds (x := (0 : ℝ))).max hcost.2).mul hweight.2
  constructor
  · simpa only [densityLower, Rat.cast_mul, Rat.cast_max, Rat.cast_zero,
      weightedKernel, max_eq_right hE0] using hL
  · simpa only [densityUpper, Rat.cast_mul, Rat.cast_max, Rat.cast_zero,
      weightedKernel, max_eq_right hE0] using hU

theorem diagonal_density_gap_tendsto {v : LogFour} (hv : v ∈ sourceDomain) (hc : v ∈ cube)
    (hno : ∀ p : Policy, ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g)
    (hqueries : ∀ p : Policy, OffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => ((densityUpper n (n + 1) (owner n v) -
      densityLower n (n + 1) (owner n v) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have h := diagonal_density_endpoints_tendsto hv hc hno hqueries
  simpa only [Rat.cast_sub, sub_self] using h.2.sub h.1

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightDensityDiagonal
