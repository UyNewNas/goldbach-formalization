import ImbalancedChen.P5U7OriginalInnerCellWidth

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual generated two-regime U7 rational upper/lower sums have a proved
vanishing gap. The complete finite boundary contribution and the actual
inner interval-coefficient widths are paid explicitly. Neither geometric
coverage nor coefficient oscillation nor a saved endpoint check is an
assumption. No numerical certificate is evaluated.
-/

namespace ImbalancedChen.P5U7OriginalRationalCoverConvergence

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open P5U7OriginalStraddlingCells P5U7OriginalStaircaseGeometry
open P5U7OriginalRationalCoverCertificate P5U7OriginalGridBoundaryArea
open P5U7OriginalBoundaryCostRate P5U7OriginalInnerCellWidth
open P5U7OriginalUniformLogTail

theorem inner_subset_outer (m : ℕ) (hm : 0 < m) : inner m ⊆ outer m := by
  intro i hi
  have hh := (Finset.mem_filter.mp hi).2
  have hv := cell_valid m hm i
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · exact hv.2.1.trans (hh.1.trans hv.2.2.2.2)
  · linarith only [hh.2, hv.2.1, hv.2.2.2.2]

theorem generated_area_nonneg (m : ℕ) (hm : 0 < m) (i : Index m) :
    0 ≤ (cell m i).area := by
  have hv := cell_valid m hm i
  exact mul_nonneg (sub_nonneg.mpr hv.2.1) (sub_nonneg.mpr hv.2.2.2.2)

theorem full_grid_area (m : ℕ) (hm : 0 < m) :
    (∑ i : Index m, (cell m i).area) = (thi - tlo) * (uhi - ulo) := by
  have harea (i : Index m) : (cell m i).area = tStep m * uStep m := by
    unfold Box.area
    rw [(cell_widths m i).1, (cell_widths m i).2]
  simp_rw [harea]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul]
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  unfold tStep uStep
  field_simp [hm0]
  <;> ring

theorem inner_grid_area_le_one (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ inner m, (cell m i).area) ≤ 1 := by
  have hh : (∑ i ∈ inner m, (cell m i).area) ≤ ∑ i : Index m, (cell m i).area :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => generated_area_nonneg m hm i)
  rw [full_grid_area m hm] at hh
  exact hh.trans (by norm_num [thi, tlo, uhi, ulo])

def innerRate (n m : ℕ) : ℚ := 40000 * (tStep m + uStep m) + 125 * rate n
def totalRate (n m : ℕ) : ℚ := 125 * areaRate m + innerRate n m

theorem innerRate_nonneg (n m : ℕ) : 0 ≤ innerRate n m := by
  have hs := step_nonneg m
  have hr := rate_nonneg n
  unfold innerRate
  positivity

/-- Exact finite accounting of all actual outer cells: retained inner
coefficient widths plus the entire boundary cost, with no omission. -/
theorem rational_gap_decomposition (n m : ℕ) (hm : 0 < m) :
    rationalUpper n m - rationalLower n m = rationalBoundaryCost n m +
      ∑ i ∈ inner m, ((cell m i).upper n - (cell m i).lower n) * (cell m i).area := by
  have hsplit := Finset.sum_sdiff
    (f := fun i : Index m => (cell m i).upper n * (cell m i).area)
    (inner_subset_outer m hm)
  unfold rationalUpper rationalLower rationalBoundaryCost boundaryIndices
  have hinner : (∑ i ∈ inner m, ((cell m i).upper n - (cell m i).lower n) * (cell m i).area) =
      (∑ i ∈ inner m, (cell m i).upper n * (cell m i).area) -
      (∑ i ∈ inner m, (cell m i).lower n * (cell m i).area) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hinner]
  linarith only [hsplit]

/-- The WHOLE generated rational certificate gap has a genuine explicit
mesh-plus-Taylor rate. All terms on the right are finite rational formulas. -/
theorem rational_gap_le_totalRate (n m : ℕ) (hm : 0 < m) :
    0 ≤ rationalUpper n m - rationalLower n m ∧
      rationalUpper n m - rationalLower n m ≤ totalRate n m := by
  have hL := rationalLower_le_actual_integral n m hm
  have hU := actual_integral_le_rationalUpper n m hm
  have hzero : (0 : ℝ) ≤ (rationalUpper n m : ℝ) - (rationalLower n m : ℝ) := by
    linarith only [hL, hU]
  refine ⟨by exact_mod_cast hzero, ?_⟩
  have hinner : (∑ i ∈ inner m,
      ((cell m i).upper n - (cell m i).lower n) * (cell m i).area) ≤ innerRate n m := by
    calc
      _ ≤ ∑ i ∈ inner m, innerRate n m * (cell m i).area := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (generated_inner_cell_width n m hm hi).2
          (generated_area_nonneg m hm i)
      _ = innerRate n m * (∑ i ∈ inner m, (cell m i).area) := by rw [Finset.mul_sum]
      _ ≤ innerRate n m * 1 := mul_le_mul_of_nonneg_left
        (inner_grid_area_le_one m hm) (innerRate_nonneg n m)
      _ = innerRate n m := mul_one _
  rw [rational_gap_decomposition n m hm]
  exact add_le_add (rationalBoundaryCost_le n m hm) hinner

theorem tendsto_steps :
    Tendsto (fun m : ℕ => (tStep m : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => (uStep m : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  constructor
  · simpa only [tStep, Rat.cast_div, Rat.cast_natCast, div_eq_mul_inv, mul_zero] using
      hi.const_mul ((thi - tlo : ℚ) : ℝ)
  · simpa only [uStep, Rat.cast_div, Rat.cast_natCast, div_eq_mul_inv, mul_zero] using
      hi.const_mul ((uhi - ulo : ℚ) : ℝ)

theorem tendsto_totalRate_diagonal :
    Tendsto (fun m : ℕ => (totalRate m m : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_areaRate.const_mul (125 : ℝ)).add
    (((tendsto_steps.1.add tendsto_steps.2).const_mul (40000 : ℝ)).add
      (tendsto_rate.const_mul (125 : ℝ)))
  simpa only [totalRate, innerRate, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
    zero_add, mul_zero] using h

/-- Actual generated two-regime rational upper-minus-lower gap tends to
zero when the grid and log precision increase together. This does not
evaluate or assert any saved original endpoint comparison. -/
theorem tendsto_actual_rational_gap :
    Tendsto (fun m : ℕ => (rationalUpper m m : ℝ) - (rationalLower m m : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_totalRate_diagonal
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact_mod_cast (rational_gap_le_totalRate m m (by omega)).1
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact_mod_cast (rational_gap_le_totalRate m m (by omega)).2

end

end ImbalancedChen.P5U7OriginalRationalCoverConvergence
