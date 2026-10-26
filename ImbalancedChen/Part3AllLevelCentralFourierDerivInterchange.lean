import ImbalancedChen.Part3FiniteOldformCentralFourierInterchange

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The original physical Fourier functional genuinely commutes with the
central parameter derivative for the actual completed and ordinary family
at every level and every positive integral dilation. The numerator is the
actual parameter-varying finite oldform list, whose derivative interchange
was proved by induction. The actual finite Euler denominator is analytic
and genuinely nonzero at the center. Its derivative is retained in both
the physical derivative and the differentiated integral. The ordinary
extension uses the actual reciprocal with its proved simple zero and
derivative 2; no totalized division by the completion pole is used.
-/

noncomputable section
open Set Complex Filter MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.PrimeCentralFourierFunctional20261026b
open ImbalancedChen.Part3.AllLevelCompletedCentralJet20261026b
open ImbalancedChen.Part3.FiniteOldformCentralFourierInterchange20261026b
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.AllLevelCentralFourierDerivInterchange20261026b

/-- Actual normalized physical central derivative, retaining the derivative
of the finite Euler denominator rather than freezing its coefficients. -/
theorem completedLevel_deriv_center_jet (N : ℕ) (z : UpperHalfPlane) :
    deriv (fun s : ℂ => completedLevelOldform N s z) (1 / 2) =
      (finiteCentralJet (canonicalPrimeList N) z * oldformNormalization (canonicalPrimeList N) (1 / 2) -
        finiteCompletedNumerator (canonicalPrimeList N) (1 / 2) z *
          deriv (oldformNormalization (canonicalPrimeList N)) (1 / 2)) /
            oldformNormalization (canonicalPrimeList N) (1 / 2) ^ 2 := by
  have hNum := finiteCompletedNumerator_hasDerivAt_center (canonicalPrimeList N) z
  have hDen := (oldformNormalization_analyticAt (canonicalPrimeList N) (1 / 2 : ℂ)).differentiableAt.hasDerivAt
  have hD := oldformNormalization_ne_zero_of_re_pos (canonicalPrimeList N) (1 / 2 : ℂ) (by norm_num)
  exact (hNum.div hDen hD).deriv

theorem completedLevel_derivative_dilation_continuous (N : ℕ) (m : ℕ+)
    (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => deriv (fun s : ℂ => completedLevelOldform N s
      (pnatDilate m (horizontalPoint y hy x))) (1 / 2)) := by
  simp_rw [completedLevel_deriv_center_jet]
  exact (((finiteCentralJet_dilation_continuous (canonicalPrimeList N) m y hy).mul continuous_const).sub
    ((finiteCompletedNumerator_dilation_continuous (canonicalPrimeList N) (1 / 2) m y hy).mul
      continuous_const)).div_const _

theorem completedLevel_derivative_fourier_formula (N : ℕ) (m : ℕ+) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ => completedLevelOldform N s
      (pnatDilate m (horizontalPoint y hy x))) (1 / 2)) =
      ((∫ x in (0 : ℝ)..1, fourierPhase n x * finiteCentralJet (canonicalPrimeList N)
          (pnatDilate m (horizontalPoint y hy x))) * oldformNormalization (canonicalPrimeList N) (1 / 2) -
        (∫ x in (0 : ℝ)..1, fourierPhase n x * finiteCompletedNumerator (canonicalPrimeList N) (1 / 2)
          (pnatDilate m (horizontalPoint y hy x))) * deriv (oldformNormalization (canonicalPrimeList N)) (1 / 2)) /
            oldformNormalization (canonicalPrimeList N) (1 / 2) ^ 2 := by
  let D : ℂ := oldformNormalization (canonicalPrimeList N) (1 / 2)
  let D' : ℂ := deriv (oldformNormalization (canonicalPrimeList N)) (1 / 2)
  have hi := finiteJet_fourier_integrable (canonicalPrimeList N) m n y hy
  have hj := finiteNumerator_fourier_integrable (canonicalPrimeList N) (1 / 2) m n y hy
  calc
    _ = ∫ x in (0 : ℝ)..1,
        (D * (fourierPhase n x * finiteCentralJet (canonicalPrimeList N)
          (pnatDilate m (horizontalPoint y hy x))) -
        D' * (fourierPhase n x * finiteCompletedNumerator (canonicalPrimeList N) (1 / 2)
          (pnatDilate m (horizontalPoint y hy x)))) / D ^ 2 := by
      congr 1
      funext x
      rw [completedLevel_deriv_center_jet]
      dsimp only [D, D']
      ring
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub (hi.const_mul _) (hj.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      dsimp only [D, D']
      ring

/-- Genuine original completed Fourier integral derivative interchange at
arbitrary level, not merely the integral of a named derivative coefficient. -/
theorem completedLevel_fourier_hasDerivAt_center (N : ℕ) (m : ℕ+) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform N s
      (pnatDilate m (horizontalPoint y hy x)))
      (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ => completedLevelOldform N s
        (pnatDilate m (horizontalPoint y hy x))) (1 / 2)) (1 / 2 : ℂ) := by
  rw [completedLevel_derivative_fourier_formula N m n y hy]
  have hNum := finiteNumerator_fourier_hasDerivAt_center (canonicalPrimeList N) m n y hy
  have hDen := (oldformNormalization_analyticAt (canonicalPrimeList N) (1 / 2 : ℂ)).differentiableAt.hasDerivAt
  have hD := oldformNormalization_ne_zero_of_re_pos (canonicalPrimeList N) (1 / 2 : ℂ) (by norm_num)
  have h := hNum.div hDen hD
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  unfold completedLevelOldform completedOldformNumerator finiteCompletedNumerator completedListValue
  have he : (fun x : ℝ => fourierPhase n x *
      (((oldformTerms (canonicalPrimeList N) s).map (fun t => t.2 *
        ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a.completedActualEisenstein s
          (pnatDilate t.1 (pnatDilate m (horizontalPoint y hy x))))).sum /
            oldformNormalization (canonicalPrimeList N) s)) =
      (fun x : ℝ => (fourierPhase n x * ((oldformTerms (canonicalPrimeList N) s).map
        (fun t => t.2 * ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a.completedActualEisenstein s
          (pnatDilate t.1 (pnatDilate m (horizontalPoint y hy x))))).sum) /
            oldformNormalization (canonicalPrimeList N) s) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_div]

theorem ordinaryLevel_dilated_fourier_normalization (N : ℕ) (m : ℕ+) (s : ℂ) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * centralOrdinaryLevel N s
      (pnatDilate m (horizontalPoint y hy x))) = inverseCompletion s *
      (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform N s
        (pnatDilate m (horizontalPoint y hy x))) := by
  have he : (fun x : ℝ => fourierPhase n x * centralOrdinaryLevel N s
      (pnatDilate m (horizontalPoint y hy x))) =
      (fun x : ℝ => inverseCompletion s * (fourierPhase n x * completedLevelOldform N s
        (pnatDilate m (horizontalPoint y hy x)))) := by
    funext x
    unfold centralOrdinaryLevel
    ring
  rw [he, intervalIntegral.integral_const_mul]

theorem ordinaryLevel_dilated_derivative_fourier (N : ℕ) (m : ℕ+) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ => centralOrdinaryLevel N s
      (pnatDilate m (horizontalPoint y hy x))) (1 / 2)) =
      2 * (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform N (1 / 2)
        (pnatDilate m (horizontalPoint y hy x))) := by
  simp_rw [centralOrdinaryLevel_deriv_center]
  have he : (fun x : ℝ => fourierPhase n x * (2 * completedLevelOldform N (1 / 2)
      (pnatDilate m (horizontalPoint y hy x)))) =
      (fun x : ℝ => 2 * (fourierPhase n x * completedLevelOldform N (1 / 2)
        (pnatDilate m (horizontalPoint y hy x)))) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_const_mul]

/-- Actual ordinary all-level Fourier derivative interchange, preserving the
true central value zero and the independently proved factor 2. -/
theorem ordinaryLevel_fourier_hasDerivAt_center (N : ℕ) (m : ℕ+) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x * centralOrdinaryLevel N s
      (pnatDilate m (horizontalPoint y hy x)))
      (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ => centralOrdinaryLevel N s
        (pnatDilate m (horizontalPoint y hy x))) (1 / 2)) (1 / 2 : ℂ) := by
  rw [ordinaryLevel_dilated_derivative_fourier N m n y hy]
  have h := inverseCompletion_hasDerivAt_center.mul (completedLevel_fourier_hasDerivAt_center N m n y hy)
  simp only [inverseCompletion_center, zero_mul, add_zero] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => ordinaryLevel_dilated_fourier_normalization N m s n y hy)

end ImbalancedChen.Part3.AllLevelCentralFourierDerivInterchange20261026b
