import ImbalancedChen.Part5OriginalH430D8FirstAffinePositive

/-!
P5.6 / h34. Additive payment for the two ORIGINAL D8 affine pieces.

Unlike the old full-D8 >= 103/1000 theorem, the second-only exported
certificate does not already include the first term. These are distinct
actual source integrals, glued by the original D8 piece definition.
No changes to root norms, action bank, seven-source /5, fixed manuscript,
seed, PP assumptions or external analytic input.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430D8TwoAffineAdditive
noncomputable section

open Set MeasureTheory
open scoped Interval
open P2EnhancedSeedPairD8Geometry
open P2EnhancedSeedPairD8Integral
open P2EnhancedSeedPairD8PieceSum
open P2EnhancedSeedActualSevenLogIdentity

/-- The genuine second-affine set integral is the ordinary interval
integral of the original outer kernel; no idealized count measure. -/
private theorem second_piece_exact :
    (∫ u in Ioo cut uHi, secondSlice u) =
      ∫ u in cut..uHi, outerSlice u := by
  calc
    _ = ∫ u in Ioo cut uHi, outerSlice u := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact (second_affine_piece ⟨hu.1.le,hu.2.le⟩).2.symm
    _ = _ := by
      rw [integral_Ioo_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le literal_geometry.2.1.le]

/-- Separate lower payments: first >= 1/200, second >= 103/1000.
No term is paid twice. Both are integrals in the literal original D8. -/
theorem genuine_d8_two_affine_ge_108_per_1000 :
    (108/1000 : ℝ) ≤ d8Logs := by
  have hFirst :=
    Part5OriginalH430D8FirstAffinePositive.genuine_d8_first_affine_ge_1_over_200
  have hSecond :=
    Part5OriginalH430D8SecondFourCell.genuine_d8_second_four_cell_ge_103_per_1000
  unfold d8Logs
  rw [second_piece_exact]
  linarith only [hFirst,hSecond]

/-- All seven ORIGINAL integrals, normalized by the same frozen /5.
This partial coefficient bound does not prove the required lambda >= 13/100. -/
theorem actual_lambda_ge_517_over_5000 :
    (517/5000 : ℝ) ≤ lambda := by
  have h0 :=
    Part5OriginalH430ThreeSingletonFourCell.original_singleton_zero_ge_89_per_1000
  have h1 :=
    Part5OriginalH430ThreeSingletonFourCell.original_singleton_one_ge_8_per_1000
  have h2 :=
    Part5OriginalH430ThreeSingletonFourCell.original_singleton_two_ge_45_per_1000
  have h5 :=
    Part5OriginalH430FourCellD5Darboux.genuine_four_cell_D5_ge_13_over_100
  have h6 :=
    Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 :=
    Part5OriginalH430D7EightCellRationalLower.genuine_d7_eight_cell_ge_27_per_1000
  have h8 := genuine_d8_two_affine_ge_108_per_1000
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430D8TwoAffineAdditive
