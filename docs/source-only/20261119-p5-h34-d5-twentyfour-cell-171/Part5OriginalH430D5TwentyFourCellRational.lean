import ImbalancedChen.Part5OriginalH430D5TwelveCellRational

/-!
P5.6 h34; original D5 physical domains, fixed manuscript ba6ec11d.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
Genuine 8+16-cell Darboux lower proof candidates. Third affine
support is retained as nonnegative; no substitute integrals.
-/

namespace ImbalancedChen.Part5OriginalH430D5TwentyFourCellRational
noncomputable section
open Set MeasureTheory Certificates
open scoped Interval
open P2EnhancedSeedSingletonPrimitive (a0)
open P2EnhancedSeedD5PlusGeometry
open P2EnhancedSeedD5PlusLogFubini
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly
open Part5OriginalH430FourCellD5Darboux (cellMass first_cell second_cell)

/-- Actual outer interval additivity on the inherited D5 slice. -/
private theorem join_actual (x y z : ℚ)
    (hx : a0 ≤ (x : ℝ)) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : (z : ℝ) ≤ top) :
    (∫ u in (x : ℝ)..(y : ℝ), outerSlice u) +
      (∫ u in (y : ℝ)..(z : ℝ), outerSlice u) =
      ∫ u in (x : ℝ)..(z : ℝ), outerSlice u := by
  have hxyR : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_outerSlice hx hxyR (hyzR.trans hz))
    (intervalIntegrable_outerSlice (hx.trans hxyR) hyzR hz)

/-- 8 genuine disjoint first affine cells of the unchanged original D5. -/
theorem original_first_eight_ge_733_per_10000 :
    (733/10000 : ℝ) ≤ ∫ u in ((50/227 : ℚ) : ℝ)..((117/454 : ℚ) : ℝ), outerSlice u := by
  have h0 := first_cell (50/227) (817/3632) (249700/191821)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h1 := first_cell (817/3632) (417/1816) (2556928/1912293)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h2 := first_cell (417/1816) (851/3632) (15980800/11631309)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h3 := first_cell (851/3632) (217/908) (63923200/45259909)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h4 := first_cell (217/908) (885/3632) (3995200/2750709)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h5 := first_cell (885/3632) (451/1816) (63923200/42779541)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h6 := first_cell (451/1816) (919/3632) (639232/415645)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have h7 := first_cell (919/3632) (117/454) (63923200/40366221)
    (by norm_num [a0]) (by norm_num)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap, supportSum])
  have hRat : (733/10000 : ℝ) ≤
      ((cellMass (50/227) (817/3632) (249700/191821) +
          cellMass (817/3632) (417/1816) (2556928/1912293) +
          cellMass (417/1816) (851/3632) (15980800/11631309) +
          cellMass (851/3632) (217/908) (63923200/45259909) +
          cellMass (217/908) (885/3632) (3995200/2750709) +
          cellMass (885/3632) (451/1816) (63923200/42779541) +
          cellMass (451/1816) (919/3632) (639232/415645) +
          cellMass (919/3632) (117/454) (63923200/40366221) : ℚ) : ℝ) := by
    norm_num [cellMass, logSeriesLower, logParameter, Finset.sum_range_succ]
  have hCast : ((cellMass (50/227) (817/3632) (249700/191821) +
          cellMass (817/3632) (417/1816) (2556928/1912293) +
          cellMass (417/1816) (851/3632) (15980800/11631309) +
          cellMass (851/3632) (217/908) (63923200/45259909) +
          cellMass (217/908) (885/3632) (3995200/2750709) +
          cellMass (885/3632) (451/1816) (63923200/42779541) +
          cellMass (451/1816) (919/3632) (639232/415645) +
          cellMass (919/3632) (117/454) (63923200/40366221) : ℚ) : ℝ) =
      (cellMass (50/227) (817/3632) (249700/191821) : ℝ) +
      (cellMass (817/3632) (417/1816) (2556928/1912293) : ℝ) +
      (cellMass (417/1816) (851/3632) (15980800/11631309) : ℝ) +
      (cellMass (851/3632) (217/908) (63923200/45259909) : ℝ) +
      (cellMass (217/908) (885/3632) (3995200/2750709) : ℝ) +
      (cellMass (885/3632) (451/1816) (63923200/42779541) : ℝ) +
      (cellMass (451/1816) (919/3632) (639232/415645) : ℝ) +
      (cellMass (919/3632) (117/454) (63923200/40366221) : ℝ) := by
    simp only [Rat.cast_add]
  have s2 := join_actual (50/227) (817/3632) (417/1816)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s3 := join_actual (50/227) (417/1816) (851/3632)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s4 := join_actual (50/227) (851/3632) (217/908)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s5 := join_actual (50/227) (217/908) (885/3632)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s6 := join_actual (50/227) (885/3632) (451/1816)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s7 := join_actual (50/227) (451/1816) (919/3632)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s8 := join_actual (50/227) (919/3632) (117/454)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  linarith only [hRat, hCast, h0, h1, h2, h3, h4, h5, h6, h7,
    s2, s3, s4, s5, s6, s7, s8]

/-- 16 genuine disjoint second affine cells of the unchanged original D5. -/
theorem original_second_sixteen_ge_977_per_10000 :
    (977/10000 : ℝ) ≤ ∫ u in ((117/454 : ℚ) : ℝ)..((19/58 : ℚ) : ℝ), outerSlice u := by
  have h0 := second_cell (117/454) (6901/26332) (113772400/71432251)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h1 := second_cell (6901/26332) (1754/6583) (1163375/748081)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h2 := second_cell (1754/6583) (7131/26332) (109595600/72172851)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h3 := second_cell (7131/26332) (3623/13166) (26876800/18125869)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h4 := second_cell (3623/13166) (7361/26332) (11713200/8089739)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h5 := second_cell (7361/26332) (1869/6583) (3229075/2283918)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h6 := second_cell (1869/6583) (7591/26332) (101242000/73336651)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h7 := second_cell (7591/26332) (3853/13166) (8262800/6130123)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h8 := second_cell (3853/13166) (7821/26332) (97065200/73759851)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h9 := second_cell (7821/26332) (1984/6583) (2968025/2310368)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h10 := second_cell (1984/6583) (8051/26332) (30962800/24692417)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h11 := second_cell (8051/26332) (4083/13166) (22700000/18549069)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h12 := second_cell (4083/13166) (8281/26332) (88711600/74288851)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h13 := second_cell (8281/26332) (2099/6583) (300775/258177)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h14 := second_cell (2099/6583) (8511/26332) (84534800/74394651)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have h15 := second_cell (8511/26332) (19/58) (400/361)
    (by norm_num [cutOne]) (by norm_num)
    (by norm_num [cutTwo]) (by norm_num)
    (by norm_num [logSeriesLower, logParameter, Finset.sum_range_succ])
    (by norm_num [cap])
  have hRat : (977/10000 : ℝ) ≤
      ((cellMass (117/454) (6901/26332) (113772400/71432251) +
          cellMass (6901/26332) (1754/6583) (1163375/748081) +
          cellMass (1754/6583) (7131/26332) (109595600/72172851) +
          cellMass (7131/26332) (3623/13166) (26876800/18125869) +
          cellMass (3623/13166) (7361/26332) (11713200/8089739) +
          cellMass (7361/26332) (1869/6583) (3229075/2283918) +
          cellMass (1869/6583) (7591/26332) (101242000/73336651) +
          cellMass (7591/26332) (3853/13166) (8262800/6130123) +
          cellMass (3853/13166) (7821/26332) (97065200/73759851) +
          cellMass (7821/26332) (1984/6583) (2968025/2310368) +
          cellMass (1984/6583) (8051/26332) (30962800/24692417) +
          cellMass (8051/26332) (4083/13166) (22700000/18549069) +
          cellMass (4083/13166) (8281/26332) (88711600/74288851) +
          cellMass (8281/26332) (2099/6583) (300775/258177) +
          cellMass (2099/6583) (8511/26332) (84534800/74394651) +
          cellMass (8511/26332) (19/58) (400/361) : ℚ) : ℝ) := by
    norm_num [cellMass, logSeriesLower, logParameter, Finset.sum_range_succ]
  have hCast : ((cellMass (117/454) (6901/26332) (113772400/71432251) +
          cellMass (6901/26332) (1754/6583) (1163375/748081) +
          cellMass (1754/6583) (7131/26332) (109595600/72172851) +
          cellMass (7131/26332) (3623/13166) (26876800/18125869) +
          cellMass (3623/13166) (7361/26332) (11713200/8089739) +
          cellMass (7361/26332) (1869/6583) (3229075/2283918) +
          cellMass (1869/6583) (7591/26332) (101242000/73336651) +
          cellMass (7591/26332) (3853/13166) (8262800/6130123) +
          cellMass (3853/13166) (7821/26332) (97065200/73759851) +
          cellMass (7821/26332) (1984/6583) (2968025/2310368) +
          cellMass (1984/6583) (8051/26332) (30962800/24692417) +
          cellMass (8051/26332) (4083/13166) (22700000/18549069) +
          cellMass (4083/13166) (8281/26332) (88711600/74288851) +
          cellMass (8281/26332) (2099/6583) (300775/258177) +
          cellMass (2099/6583) (8511/26332) (84534800/74394651) +
          cellMass (8511/26332) (19/58) (400/361) : ℚ) : ℝ) =
      (cellMass (117/454) (6901/26332) (113772400/71432251) : ℝ) +
      (cellMass (6901/26332) (1754/6583) (1163375/748081) : ℝ) +
      (cellMass (1754/6583) (7131/26332) (109595600/72172851) : ℝ) +
      (cellMass (7131/26332) (3623/13166) (26876800/18125869) : ℝ) +
      (cellMass (3623/13166) (7361/26332) (11713200/8089739) : ℝ) +
      (cellMass (7361/26332) (1869/6583) (3229075/2283918) : ℝ) +
      (cellMass (1869/6583) (7591/26332) (101242000/73336651) : ℝ) +
      (cellMass (7591/26332) (3853/13166) (8262800/6130123) : ℝ) +
      (cellMass (3853/13166) (7821/26332) (97065200/73759851) : ℝ) +
      (cellMass (7821/26332) (1984/6583) (2968025/2310368) : ℝ) +
      (cellMass (1984/6583) (8051/26332) (30962800/24692417) : ℝ) +
      (cellMass (8051/26332) (4083/13166) (22700000/18549069) : ℝ) +
      (cellMass (4083/13166) (8281/26332) (88711600/74288851) : ℝ) +
      (cellMass (8281/26332) (2099/6583) (300775/258177) : ℝ) +
      (cellMass (2099/6583) (8511/26332) (84534800/74394651) : ℝ) +
      (cellMass (8511/26332) (19/58) (400/361) : ℝ) := by
    simp only [Rat.cast_add]
  have s2 := join_actual (117/454) (6901/26332) (1754/6583)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s3 := join_actual (117/454) (1754/6583) (7131/26332)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s4 := join_actual (117/454) (7131/26332) (3623/13166)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s5 := join_actual (117/454) (3623/13166) (7361/26332)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s6 := join_actual (117/454) (7361/26332) (1869/6583)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s7 := join_actual (117/454) (1869/6583) (7591/26332)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s8 := join_actual (117/454) (7591/26332) (3853/13166)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s9 := join_actual (117/454) (3853/13166) (7821/26332)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s10 := join_actual (117/454) (7821/26332) (1984/6583)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s11 := join_actual (117/454) (1984/6583) (8051/26332)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s12 := join_actual (117/454) (8051/26332) (4083/13166)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s13 := join_actual (117/454) (4083/13166) (8281/26332)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s14 := join_actual (117/454) (8281/26332) (2099/6583)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s15 := join_actual (117/454) (2099/6583) (8511/26332)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  have s16 := join_actual (117/454) (8511/26332) (19/58)
    (by norm_num [a0]) (by norm_num) (by norm_num) (by norm_num [top])
  linarith only [hRat, hCast, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16]

/-- Sum two disjoint original affine intervals, and retain the third
as separately nonnegative, avoiding any repeated integral payment. -/
theorem genuine_twentyfour_cell_D5_ge_171_per_1000 :
    (171/1000 : ℝ) ≤ d5Logs := by
  have hFirst := original_first_eight_ge_733_per_10000
  have hSecond := original_second_sixteen_ge_977_per_10000
  have hFirstEq :
      (∫ u in ((50/227 : ℚ) : ℝ)..((117/454 : ℚ) : ℝ), outerSlice u) =
      ∫ u in a0..cutOne, outerSlice u := by
    congr 1 <;> norm_num [a0, cutOne]
  have hSecondEq :
      (∫ u in ((117/454 : ℚ) : ℝ)..((19/58 : ℚ) : ℝ), outerSlice u) =
      ∫ u in cutOne..cutTwo, outerSlice u := by
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

/-- Unmodified seven original sources and exact /5 normalization.
This is still below the target lambda >=13/100. -/
theorem actual_lambda_ge_117_over_1000 :
    (117/1000 : ℝ) ≤ lambda := by
  have h0 := Part5OriginalH430EightCellSingletonChain.original_singleton_zero_ge_106_per_1000
  have h1 := Part5OriginalH430EightCellSingletonChain.original_singleton_one_ge_10_per_1000
  have h2 := Part5OriginalH430EightCellSingletonChain.original_singleton_two_ge_53_per_1000
  have h5 := genuine_twentyfour_cell_D5_ge_171_per_1000
  have h6 := Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 := Part5OriginalH430D7EightCellRationalLower.genuine_d7_eight_cell_ge_27_per_1000
  have h8 := Part5OriginalH430D8TwoAffineAdditive.genuine_d8_two_affine_ge_108_per_1000
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430D5TwentyFourCellRational
