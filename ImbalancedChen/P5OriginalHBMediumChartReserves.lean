import ImbalancedChen.P5ActualHBMediumRoleSupports

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Numeric original-chart supplier: actual group R, n >= R/128,
-- X^a <= R <= C X, exact REAL HB cube y^3=2R.
-- The two explicit power-growth thresholds are fixed chart reserves,
-- not hypotheses asserting that a medium slot or long branch exists.
namespace ImbalancedChen.P5Z.OriginalHBMediumChartReserves
noncomputable section
open Classical
open ActualRoughHeathBrownWords ActualHBDyadicOccurrenceFamily
open ActualHBMediumBranchPartition ActualHBMediumRoleSupports

theorem original_chart_numeric_reserves {X zeta a C R y : ℝ} {n : ℕ}
    (hX : 1 ≤ X) (hzeta : 0 ≤ zeta) (hC : 0 ≤ C)
    (hgroup : X^a ≤ R) (hR : R ≤ C*X)
    (hdyadic : R/128 ≤ (n : ℝ)) (hcomplete : (n : ℝ) ≤ C*X)
    (hy : 0 ≤ y) (hcube : y^3 = 2*R)
    (hshortGrowth : 8192 < X^(a-18*zeta))
    (hlongGrowth : 2*C < X^(3*zeta/4)) :
    1 ≤ originalLower X zeta ∧ 1 ≤ originalUpper X zeta ∧
      64*(originalLower X zeta)^6 < (n : ℝ) ∧
      (n : ℝ) < (originalUpper X zeta)^3 ∧
      y ≤ originalUpper X zeta := by
  have hXp : 0 < X := by linarith
  have hA : 1 ≤ originalLower X zeta := by
    exact Real.one_le_rpow hX (by linarith)
  have hB : 1 ≤ originalUpper X zeta := by
    exact Real.one_le_rpow hX (by linarith)
  have hA6 : (originalLower X zeta)^6 = X^(18*zeta) := by
    unfold originalLower
    rw [← Real.rpow_natCast,← Real.rpow_mul hXp.le]
    congr 1
    ring
  have hB3 : (originalUpper X zeta)^3 = X*X^(3*zeta/4) := by
    unfold originalUpper
    rw [← Real.rpow_natCast,← Real.rpow_mul hXp.le]
    have he : (1/3+zeta/4)*(3 : ℝ) = 1+3*zeta/4 := by ring
    rw [he,Real.rpow_add hXp,Real.rpow_one]
  have hexp : X^a = X^(18*zeta)*X^(a-18*zeta) := by
    rw [← Real.rpow_add hXp]
    congr 1
    ring
  have hp : 0 < X^(18*zeta) := Real.rpow_pos_of_pos hXp _
  have hbig : 8192*X^(18*zeta) < X^a := by
    rw [hexp]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hshortGrowth hp
  have hsmall : 64*(originalLower X zeta)^6 < (n : ℝ) := by
    rw [hA6]
    linarith
  have hlong : C*X < (originalUpper X zeta)^3 := by
    rw [hB3]
    have hc : C < X^(3*zeta/4) := lt_of_le_of_lt (by linarith : C ≤ 2*C) hlongGrowth
    simpa only [mul_comm] using mul_lt_mul_of_pos_right hc hXp
  have hcubeBound : y^3 ≤ (originalUpper X zeta)^3 := by
    rw [hcube,hB3]
    have hmul := mul_lt_mul_of_pos_right hlongGrowth hXp
    nlinarith
  have hyB := (pow_le_pow_iff_left₀ hy (by linarith : 0 ≤ originalUpper X zeta)
    (by decide : (3 : ℕ) ≠ 0)).mp hcubeBound
  exact ⟨hA,hB,hsmall,hcomplete.trans_lt hlong,hyB⟩

-- Genuine original supports discharge all short/long numeric inputs.
-- The result retains Type I and gives actual non-Mobius long roles.
theorem original_actual_noMedium_from_chart {z X zeta a C R y : ℝ}
    (hz : 0 ≤ z) (hX : 1 ≤ X) (hzeta : 0 ≤ zeta) (hC : 0 ≤ C)
    {j n : ℕ} {bs : List HBRightClosedDyadicRoles.Block}
    (hj : j ∈ Finset.range 3) (hn : blockCoefficient z y j n bs ≠ 0)
    (hgroup : X^a ≤ R) (hR : R ≤ C*X)
    (hdyadic : R/128 ≤ (n : ℝ)) (hcomplete : (n : ℝ) ≤ C*X)
    (hy : 0 ≤ y) (hcube : y^3 = 2*R)
    (hshortGrowth : 8192 < X^(a-18*zeta))
    (hlongGrowth : 2*C < X^(3*zeta/4))
    (hbranch : firstMedium (originalLower X zeta) (originalUpper X zeta) bs = none) :
    ((longBlocks (originalUpper X zeta) bs).length = 1 ∨
      (longBlocks (originalUpper X zeta) bs).length = 2) ∧
    (∀ rb ∈ (roles j).zip bs,
      originalUpper X zeta < (ActualHBDyadicProductWindow.lower rb.2 : ℝ) →
      rb.1 = .one ∨ rb.1 = .logarithm) := by
  obtain ⟨hA,hB,hshort,hcomp,hyB⟩ := original_chart_numeric_reserves hX hzeta hC
    hgroup hR hdyadic hcomplete hy hcube hshortGrowth hlongGrowth
  exact original_noMedium_actual_alternative hz hA hB hyB hj hn hbranch hshort hcomp

end
end ImbalancedChen.P5Z.OriginalHBMediumChartReserves
