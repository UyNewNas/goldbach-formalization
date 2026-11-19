import ImbalancedChen.Part5OriginalH430EightCellSingletonChain

/-!
P5.6 → h34, frozen seven-source W2 D5+ exact domain.
Concrete four-first and eight-second rational Darboux cells; the entire
third affine interval is retained as a nonnegative genuine integral.
The two public supplier declarations in the preexisting D5 four-cell module
are exposed without changing their proof bodies or hypotheses.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430D5TwelveCellRational
noncomputable section
open Set MeasureTheory Certificates
open scoped Interval
open P2EnhancedSeedSingletonPrimitive (a0)
open P2EnhancedSeedD5PlusGeometry
open P2EnhancedSeedD5PlusLogFubini
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly
open Part5OriginalH430FourCellD5Darboux (cellMass first_cell second_cell)

/-- Actual D5 first affine contribution: 4 disjoint
rational cells on the original slice; no finite integral is postulated. -/
theorem first_four_cells_ge_70_per_1000 :
    (70/1000 : ℝ) ≤ (∫ u in ((50/227 : ℚ) : ℝ)..((117/454 : ℚ) : ℝ), outerSlice u) := by
  have h0 := first_cell (50/227) (417/1816) (249700/191821)
    (by norm_num [a0]) (by norm_num) (by norm_num [cutOne])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h1 := first_cell (417/1816) (217/908) (15980800/11631309)
    (by norm_num [a0]) (by norm_num) (by norm_num [cutOne])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h2 := first_cell (217/908) (451/1816) (3995200/2750709)
    (by norm_num [a0]) (by norm_num) (by norm_num [cutOne])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h3 := first_cell (451/1816) (117/454) (639232/415645)
    (by norm_num [a0]) (by norm_num) (by norm_num [cutOne])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have hRational :
      (70/1000 : ℝ) ≤ ((cellMass (50/227) (417/1816) (249700/191821) +
          cellMass (417/1816) (217/908) (15980800/11631309) +
          cellMass (217/908) (451/1816) (3995200/2750709) +
          cellMass (451/1816) (117/454) (639232/415645) : ℚ) : ℝ) := by
    norm_num [cellMass, logSeriesLower, logParameter, Finset.sum_range_succ]
  have hCast :
      ((cellMass (50/227) (417/1816) (249700/191821) +
          cellMass (417/1816) (217/908) (15980800/11631309) +
          cellMass (217/908) (451/1816) (3995200/2750709) +
          cellMass (451/1816) (117/454) (639232/415645) : ℚ) : ℝ) =
        (cellMass (50/227) (417/1816) (249700/191821) : ℝ) +
        (cellMass (417/1816) (217/908) (15980800/11631309) : ℝ) +
        (cellMass (217/908) (451/1816) (3995200/2750709) : ℝ) +
        (cellMass (451/1816) (117/454) (639232/415645) : ℝ) := by
    simp only [Rat.cast_add]
  have j1 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j3 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  linarith only [hRational, hCast, h0, h1, h2, h3,
    j1, j2, j3]

/-- Actual D5 second affine contribution: 8 disjoint
rational cells on the original slice; no finite integral is postulated. -/
theorem second_eight_cells_ge_93_per_1000 :
    (93/1000 : ℝ) ≤ (∫ u in ((117/454 : ℚ) : ℝ)..((19/58 : ℚ) : ℝ), outerSlice u) := by
  have h0 := second_cell (117/454) (1754/6583) (1163375/748081)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h1 := second_cell (1754/6583) (3623/13166) (26876800/18125869)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h2 := second_cell (3623/13166) (1869/6583) (3229075/2283918)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h3 := second_cell (1869/6583) (3853/13166) (8262800/6130123)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h4 := second_cell (3853/13166) (1984/6583) (2968025/2310368)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h5 := second_cell (1984/6583) (4083/13166) (22700000/18549069)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h6 := second_cell (4083/13166) (2099/6583) (300775/258177)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h7 := second_cell (2099/6583) (19/58) (400/361)
    (by norm_num [cutOne]) (by norm_num) (by norm_num [cutTwo])
    (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have hRational :
      (93/1000 : ℝ) ≤ ((cellMass (117/454) (1754/6583) (1163375/748081) +
          cellMass (1754/6583) (3623/13166) (26876800/18125869) +
          cellMass (3623/13166) (1869/6583) (3229075/2283918) +
          cellMass (1869/6583) (3853/13166) (8262800/6130123) +
          cellMass (3853/13166) (1984/6583) (2968025/2310368) +
          cellMass (1984/6583) (4083/13166) (22700000/18549069) +
          cellMass (4083/13166) (2099/6583) (300775/258177) +
          cellMass (2099/6583) (19/58) (400/361) : ℚ) : ℝ) := by
    norm_num [cellMass, logSeriesLower, logParameter, Finset.sum_range_succ]
  have hCast :
      ((cellMass (117/454) (1754/6583) (1163375/748081) +
          cellMass (1754/6583) (3623/13166) (26876800/18125869) +
          cellMass (3623/13166) (1869/6583) (3229075/2283918) +
          cellMass (1869/6583) (3853/13166) (8262800/6130123) +
          cellMass (3853/13166) (1984/6583) (2968025/2310368) +
          cellMass (1984/6583) (4083/13166) (22700000/18549069) +
          cellMass (4083/13166) (2099/6583) (300775/258177) +
          cellMass (2099/6583) (19/58) (400/361) : ℚ) : ℝ) =
        (cellMass (117/454) (1754/6583) (1163375/748081) : ℝ) +
        (cellMass (1754/6583) (3623/13166) (26876800/18125869) : ℝ) +
        (cellMass (3623/13166) (1869/6583) (3229075/2283918) : ℝ) +
        (cellMass (1869/6583) (3853/13166) (8262800/6130123) : ℝ) +
        (cellMass (3853/13166) (1984/6583) (2968025/2310368) : ℝ) +
        (cellMass (1984/6583) (4083/13166) (22700000/18549069) : ℝ) +
        (cellMass (4083/13166) (2099/6583) (300775/258177) : ℝ) +
        (cellMass (2099/6583) (19/58) (400/361) : ℝ) := by
    simp only [Rat.cast_add]
  have j1 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j3 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j4 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j5 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j6 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  have j7 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
    (intervalIntegrable_outerSlice (by norm_num [a0]) (by norm_num) (by norm_num [top]))
  linarith only [hRational, hCast, h0, h1, h2, h3, h4, h5, h6, h7,
    j1, j2, j3, j4, j5, j6, j7]

/-- The two disjoint original affine pieces are combined exactly once.
The genuine third support [19/58,1/3] has a separate nonnegative payment. -/
theorem genuine_twelve_cell_D5_ge_163_per_1000 :
    (163/1000 : ℝ) ≤ d5Logs := by
  have hFirst := first_four_cells_ge_70_per_1000
  have hSecond := second_eight_cells_ge_93_per_1000
  have hFirstEq : (∫ u in ((50/227 : ℚ) : ℝ)..((117/454 : ℚ) : ℝ), outerSlice u) =
      (∫ u in a0..cutOne, outerSlice u) := by
    congr 1 <;> norm_num [a0, cutOne]
  have hSecondEq : (∫ u in ((117/454 : ℚ) : ℝ)..((19/58 : ℚ) : ℝ), outerSlice u) =
      (∫ u in cutOne..cutTwo, outerSlice u) := by
    congr 1 <;> norm_num [cutOne, cutTwo]
  rw [hFirstEq] at hFirst
  rw [hSecondEq] at hSecond
  have ho := three_cut_order
  have hI1 := intervalIntegrable_outerSlice (le_refl a0)
    ho.1.le (ho.2.1.le.trans ho.2.2.le)
  have hI2 := intervalIntegrable_outerSlice ho.1.le
    ho.2.1.le ho.2.2.le
  have hI12 := intervalIntegrable_outerSlice (le_refl a0)
    (ho.1.le.trans ho.2.1.le) ho.2.2.le
  have hI3 := intervalIntegrable_outerSlice
    (ho.1.le.trans ho.2.1.le) ho.2.2.le (le_refl top)
  have hTail : 0 ≤ ∫ u in cutTwo..top, outerSlice u := by
    have h := intervalIntegral.integral_mono_on ho.2.2.le
      intervalIntegrable_const hI3
      (fun u hu =>
        Part5OriginalH430D5D7PositiveRationalLower.actual_d5_outer_nonneg
          ⟨(ho.1.le.trans ho.2.1.le).trans hu.1, hu.2⟩)
    simpa only [intervalIntegral.integral_const, smul_zero] using h
  have hJoin := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hAll := intervalIntegral.integral_add_adjacent_intervals hI12 hI3
  rw [Part5OriginalH430D5D7PositiveRationalLower.actual_d5Logs_eq_outer]
  linarith only [hFirst, hSecond, hTail, hJoin, hAll]

/-- Literal seven original feedback sources and unchanged /5 normalization. -/
theorem actual_lambda_ge_577_over_5000 :
    (577/5000 : ℝ) ≤ lambda := by
  have h0 := Part5OriginalH430EightCellSingletonChain.original_singleton_zero_ge_106_per_1000
  have h1 := Part5OriginalH430EightCellSingletonChain.original_singleton_one_ge_10_per_1000
  have h2 := Part5OriginalH430EightCellSingletonChain.original_singleton_two_ge_53_per_1000
  have h5 := genuine_twelve_cell_D5_ge_163_per_1000
  have h6 := Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 := Part5OriginalH430D7EightCellRationalLower.genuine_d7_eight_cell_ge_27_per_1000
  have h8 := Part5OriginalH430D8TwoAffineAdditive.genuine_d8_two_affine_ge_108_per_1000
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430D5TwelveCellRational
