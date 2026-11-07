import ImbalancedChen.P5ZU1011OriginalSixteenTightGridLocalGeometry
import ImbalancedChen.P5ZU1011OriginalSixteenOrdinaryBoxRate

/-!
# Actual endpoint limits on the generated original16 grid

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The generated box has sideSum=4*step and the original compact guard.
The proved actual residual width is therefore at most 10*step. Both
residual endpoints converge to the actual residual, and both ordinary
ratio endpoints converge to the actual query. Every actually eligible
policy eventually has the fixed rational residual floor a/2>0.

The generated Buchstab switched width has the explicit form A*step+B/m.
On the diagonal m=n+1 this width tends to zero, and both directed switched
endpoints converge to the actual switched cost. No endpoint-limit,
switched-bound or ordinary-query supplier is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightGridEndpointLimits

noncomputable section

open Set MeasureTheory Filter Topology U11Integral
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open U1011OriginalSixteenTightGridLocalGeometry
open OriginalSixteenOrdinaryBoxBounds OriginalSixteenOrdinaryBoxRate
open OriginalSixteenTightSwitchedRate
open scoped BigOperators

theorem generated_compact (n : ℕ) (j : Index n) : Compact (gridBox n j) := by
  intro i
  simpa only [OriginalSixteenSwitchedBoxBounds.a, a, b] using gridBox_corner_bounds n j i

theorem generated_sideSum (n : ℕ) (j : Index n) : sideSum (gridBox n j) = 4 * step n := by
  simp only [sideSum, corner_difference]
  ring

theorem actual_residual_endpoint_errors (p : Policy) {v : LogFour} (hv : v ∈ cube) (n : ℕ) :
    |(residualLower p (gridBox n (owner n v)) : ℝ) - typedResidual p v| ≤ 10 * (step n : ℝ) ∧
      |(residualUpper p (gridBox n (owner n v)) : ℝ) - typedResidual p v| ≤ 10 * (step n : ℝ) := by
  have hb := residual_bounds p (gridBox n (owner n v))
    (cell_subset_closedBox n (owner n v) (owner_mem n hv))
  have hq := (residual_width p (gridBox n (owner n v)) (gridBox_valid n (owner n v))).2
  rw [generated_sideSum] at hq
  have hwidth : (residualUpper p (gridBox n (owner n v)) : ℝ) -
      (residualLower p (gridBox n (owner n v)) : ℝ) ≤ 10 * (step n : ℝ) := by
    have hR : ((residualUpper p (gridBox n (owner n v)) -
        residualLower p (gridBox n (owner n v)) : ℚ) : ℝ) ≤
        (((5 / 2 : ℚ) * (4 * step n) : ℚ) : ℝ) := by exact_mod_cast hq
    push_cast at hR
    linarith only [hR]
  rw [abs_of_nonpos (sub_nonpos.mpr hb.1), abs_of_nonneg (sub_nonneg.mpr hb.2)]
  constructor <;> linarith only [hb.1, hb.2, hwidth]

theorem residualLower_tendsto (p : Policy) {v : LogFour} (hv : v ∈ cube) :
    Tendsto (fun n => (residualLower p (gridBox n (owner n v)) : ℝ)) atTop (𝓝 (typedResidual p v)) := by
  have hz : Tendsto (fun n : ℕ => 10 * (step n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_step.const_mul 10
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hz.eventually (gt_mem_nhds heps)] with n hn
  rw [Real.dist_eq]
  exact (actual_residual_endpoint_errors p hv n).1.trans_lt hn

theorem residualUpper_tendsto (p : Policy) {v : LogFour} (hv : v ∈ cube) :
    Tendsto (fun n => (residualUpper p (gridBox n (owner n v)) : ℝ)) atTop (𝓝 (typedResidual p v)) := by
  have hz : Tendsto (fun n : ℕ => 10 * (step n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_step.const_mul 10
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hz.eventually (gt_mem_nhds heps)] with n hn
  rw [Real.dist_eq]
  exact (actual_residual_endpoint_errors p hv n).2.trans_lt hn

theorem ratioLower_tendsto (p : Policy) {v : LogFour} (hv : v ∈ cube) (hw : v 3 ≠ 0) :
    Tendsto (fun n => (ratioLower p (gridBox n (owner n v)) : ℝ)) atTop
      (𝓝 (typedResidual p v / v 3)) := by
  simpa only [ratioLower, Rat.cast_div] using
    (residualLower_tendsto p hv).div (owner_hi_tendsto hv 3) hw

theorem ratioUpper_tendsto (p : Policy) {v : LogFour} (hv : v ∈ cube) (hw : v 3 ≠ 0) :
    Tendsto (fun n => (ratioUpper p (gridBox n (owner n v)) : ℝ)) atTop
      (𝓝 (typedResidual p v / v 3)) := by
  simpa only [ratioUpper, Rat.cast_div] using
    (residualUpper_tendsto p hv).div (owner_lo_tendsto hv 3) hw

def residualFloor : ℚ := a / 2

theorem residualFloor_pos : 0 < residualFloor := by norm_num [residualFloor, a]

theorem eventually_actual_eligible_positive_floor (p : Policy) {v : LogFour}
    (hv : v ∈ sourceDomain) (hc : v ∈ cube) (he : TypedEligible p v) :
    ∀ᶠ n : ℕ in atTop, PositiveGuards p (gridBox n (owner n v)) ∧
      residualFloor ≤ residualLower p (gridBox n (owner n v)) := by
  have hsmall := typedEligible_residual_gt_smallest p v he
  have hbase : (a : ℝ) ≤ v 3 := hv.1
  have hgap : (residualFloor : ℝ) < typedResidual p v := by
    norm_num [residualFloor, a] at hbase ⊢
    linarith only [hsmall, hbase]
  filter_upwards [(residualLower_tendsto p hc).eventually (lt_mem_nhds hgap)] with n hn
  have hQ : residualFloor < residualLower p (gridBox n (owner n v)) := by exact_mod_cast hn
  exact ⟨⟨U1011OriginalSixteenRationalIntegralCertificates.grid_lo_pos n (owner n v) 3,
    residualFloor_pos.trans hQ⟩, hQ.le⟩

def switchedRateA : ℚ :=
  (((OriginalSixteenSwitchedBoxBounds.k / OriginalSixteenSwitchedBoxBounds.a) *
    ((1 / OriginalSixteenSwitchedBoxBounds.a + 1 / OriginalSixteenSwitchedBoxBounds.a ^ 2) / 2) +
      OriginalSixteenSwitchedBoxBounds.k / OriginalSixteenSwitchedBoxBounds.a ^ 2) * 4)
def switchedRateB : ℚ := 3000 * OriginalSixteenSwitchedBoxBounds.k / OriginalSixteenSwitchedBoxBounds.a

theorem diagonal_switched_width (n : ℕ) (j : Index n) :
    0 ≤ OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) (gridBox n j) -
      OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) (gridBox n j) ∧
      OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) (gridBox n j) -
        OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) (gridBox n j) ≤
          switchedRateA * step n + switchedRateB / (n + 1 : ℕ) := by
  have h := switched_width_rate (n + 1) (by omega) (gridBox n j)
    (gridBox_valid n j) (generated_compact n j)
  rw [generated_sideSum] at h
  exact ⟨h.1, by convert h.2 using 1 <;> dsimp [switchedRateA, switchedRateB] <;> ring⟩

theorem diagonal_switched_gap_tendsto (v : LogFour) :
    Tendsto (fun n => ((OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) (gridBox n (owner n v)) -
      OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) (gridBox n (owner n v)) : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have hA : Tendsto (fun n : ℕ => (switchedRateA : ℝ) * (step n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_step.const_mul (switchedRateA : ℝ)
  have hB : Tendsto (fun n : ℕ => (switchedRateB : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (switchedRateB : ℝ)
  apply squeeze_zero (g := fun n : ℕ => (switchedRateA : ℝ) * (step n : ℝ) +
    (switchedRateB : ℝ) / ((n : ℝ) + 1))
  · intro n
    exact_mod_cast (diagonal_switched_width n (owner n v)).1
  · intro n
    have h := (diagonal_switched_width n (owner n v)).2
    exact_mod_cast h
  · simpa only [zero_add] using hA.add hB

theorem diagonal_switched_endpoints_tendsto {v : LogFour}
    (hv : v ∈ sourceDomain) (hc : v ∈ cube) :
    Tendsto (fun n => (OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1)
      (gridBox n (owner n v)) : ℝ)) atTop
        (𝓝 (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)) ∧
      Tendsto (fun n => (OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1)
        (gridBox n (owner n v)) : ℝ)) atTop
          (𝓝 (switchedKernel currentK LiLiuPrereqBuchstab.buchstab v)) := by
  have hb (n : ℕ) := OriginalSixteenTightSwitchedBoxes.switched_box_bounds (n + 1)
    (by omega) ∅ (gridBox n (owner n v))
    (cell_subset_closedBox n (owner n v) (owner_mem n hc)) hv
  have hL (n : ℕ) :
      |(OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) (gridBox n (owner n v)) : ℝ) -
        switchedKernel currentK LiLiuPrereqBuchstab.buchstab v| ≤
      ((OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) (gridBox n (owner n v)) -
        OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) (gridBox n (owner n v)) : ℚ) : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hb n).1), Rat.cast_sub]
    linarith only [(hb n).2]
  have hU (n : ℕ) :
      |(OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) (gridBox n (owner n v)) : ℝ) -
        switchedKernel currentK LiLiuPrereqBuchstab.buchstab v| ≤
      ((OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) (gridBox n (owner n v)) -
        OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) (gridBox n (owner n v)) : ℚ) : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hb n).2), Rat.cast_sub]
    linarith only [(hb n).1]
  constructor
  · rw [Metric.tendsto_nhds]
    intro eps heps
    filter_upwards [(diagonal_switched_gap_tendsto v).eventually (gt_mem_nhds heps)] with n hn
    rw [Real.dist_eq]
    exact (hL n).trans_lt hn
  · rw [Metric.tendsto_nhds]
    intro eps heps
    filter_upwards [(diagonal_switched_gap_tendsto v).eventually (gt_mem_nhds heps)] with n hn
    rw [Real.dist_eq]
    exact (hU n).trans_lt hn

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightGridEndpointLimits
