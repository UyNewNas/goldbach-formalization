import ImbalancedChen.Part3AllLevelCentralNormalization
import ImbalancedChen.Part3ActualContinuedZeroCuspMean

/-!
New mathematical source, 2026-10-26. UNCOMPILED / ZERO FORMAL CREDIT.

Physical Fourier means of the genuine ordinary central extension. The
infinite-series interchange is the proved norm-summable actual K-series
integer-mean theorem, not an assumed Fourier reconstruction. The finite
oldform sum is integrated using continuous traces. At the center we
integrate the actual pointwise parameter derivative, whose value was
proved from the true completion-factor pole. No differentiation of an
integral is silently used. Both cusp formulas retain the literal definition
of the ordinary extension; no manuscript convention is imposed.
-/

noncomputable section
open Set Complex
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.ActualContinuedZeroCuspMean20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.OrdinaryCentralFourierMeans20261026b

theorem dilation_list_continuous (T : List (ℕ+ × ℂ)) (s : ℂ)
    (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => (T.map (fun t => t.2 *
      completedActualEisenstein s (pnatDilate t.1 (horizontalPoint y hy x)))).sum) := by
  induction T with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  | cons t T ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (continuous_const.mul (completed_integer_dilation_continuous s t.1 y hy)).add ih

/-- Finite interchange after the genuine infinite-series mean theorem. -/
theorem dilation_list_mean (T : List (ℕ+ × ℂ)) (s : ℂ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, (T.map (fun t => t.2 *
      completedActualEisenstein s (pnatDilate t.1 (horizontalPoint y hy x)))).sum) =
      (T.map (fun t => t.2 * completedConstant ((t.1 : ℝ) * y) s)).sum := by
  induction T with
  | nil => simp
  | cons t T ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [intervalIntegral.integral_add
        ((continuous_const.mul (completed_integer_dilation_continuous s t.1 y hy)).intervalIntegrable 0 1)
        ((dilation_list_continuous T s y hy).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul, completed_integer_dilation_mean s t.1 y hy, ih]

theorem completed_infinity_trace_continuous (N : ℕ) (s : ℂ)
    (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => completedLevelOldform N s (horizontalPoint y hy x)) :=
  (dilation_list_continuous (oldformTerms (canonicalPrimeList N) s) s y hy).div_const _

/-- Actual all-level infinity zero Fourier mean, including s=1/2. -/
theorem completed_infinity_mean (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, completedLevelOldform N s (horizontalPoint y hy x)) =
      completedInfinityConstant N s y := by
  unfold completedLevelOldform completedOldformNumerator completedInfinityConstant
  rw [intervalIntegral.integral_div, dilation_list_mean _ s y hy]

/-- The ordinary mean uses the holomorphic reciprocal constructed from the
true Lambda pole. It remains meaningful at the center. -/
theorem ordinary_infinity_mean (N : ℕ) (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, centralOrdinaryLevel N s (horizontalPoint y hy x)) =
      inverseCompletion s * completedInfinityConstant N s y := by
  unfold centralOrdinaryLevel
  rw [intervalIntegral.integral_const_mul, completed_infinity_mean N s y hy]

theorem ordinary_zeroCusp_mean (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs : s ∈ centralNormalizationDomain) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      centralOrdinaryLevel N s (frickeSL N hN • horizontalPoint y hy x)) =
      inverseCompletion s * completedReflectedConstant N s y := by
  have hs0 : s ≠ 0 := by intro he; subst s; simpa using hs.1
  have hr : s ∈ completedRegularDomain N :=
    ⟨hs0, hs.2.1, oldformNormalization_ne_zero_of_re_pos _ s hs.1⟩
  unfold centralOrdinaryLevel
  rw [intervalIntegral.integral_const_mul, completed_zeroCusp_mean N hN s hr y hy]

theorem ordinary_infinity_mean_center (N : ℕ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, centralOrdinaryLevel N (1 / 2) (horizontalPoint y hy x)) = 0 := by
  simp only [centralOrdinaryLevel_center, intervalIntegral.integral_zero]

theorem ordinary_zeroCusp_mean_center (N : ℕ) (hN : 0 < N) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      centralOrdinaryLevel N (1 / 2) (frickeSL N hN • horizontalPoint y hy x)) = 0 := by
  simp only [centralOrdinaryLevel_center, intervalIntegral.integral_zero]

/-- Integrability is a conclusion from actual K-series normal convergence. -/
theorem ordinary_central_derivative_infinity_continuous (N : ℕ) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ =>
      deriv (fun s : ℂ => centralOrdinaryLevel N s (horizontalPoint y hy x)) (1 / 2)) := by
  simp_rw [centralOrdinaryLevel_deriv_center]
  exact continuous_const.mul (completed_infinity_trace_continuous N (1 / 2) y hy)

/-- Genuine integral of the actual pointwise ordinary central derivative. -/
theorem ordinary_central_derivative_infinity_mean (N : ℕ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      deriv (fun s : ℂ => centralOrdinaryLevel N s (horizontalPoint y hy x)) (1 / 2)) =
      2 * completedInfinityConstant N (1 / 2) y := by
  simp_rw [centralOrdinaryLevel_deriv_center]
  rw [intervalIntegral.integral_const_mul, completed_infinity_mean N (1 / 2) y hy]

theorem ordinary_central_derivative_zeroCusp_continuous (N : ℕ) (hN : 0 < N)
    (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => deriv (fun s : ℂ =>
      centralOrdinaryLevel N s (frickeSL N hN • horizontalPoint y hy x)) (1 / 2)) := by
  simp_rw [centralOrdinaryLevel_deriv_center]
  exact continuous_const.mul (completed_zeroCusp_trace_continuous N hN (1 / 2)
    (criticalStrip_subset_completedRegularDomain N (by norm_num)) y hy)

theorem ordinary_central_derivative_zeroCusp_mean (N : ℕ) (hN : 0 < N)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, deriv (fun s : ℂ =>
      centralOrdinaryLevel N s (frickeSL N hN • horizontalPoint y hy x)) (1 / 2)) =
      2 * completedReflectedConstant N (1 / 2) y := by
  simp_rw [centralOrdinaryLevel_deriv_center]
  rw [intervalIntegral.integral_const_mul, completed_zeroCusp_mean N hN (1 / 2)
    (criticalStrip_subset_completedRegularDomain N (by norm_num)) y hy]

end ImbalancedChen.Part3.OrdinaryCentralFourierMeans20261026b
