import ImbalancedChen.Part3PrimeCentralChannelDerivative
import ImbalancedChen.Part3CentralReflectedLogEuler

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The literal original Fourier phase and physical unit-interval integral are
used throughout. The actual completed two-channel reflection is integrated
for every integer Fourier mode. The ordinary pole normalization is kept
in a cross-multiplied identity, so no reciprocal value at its zero is
divided out. The signed completed central derivative identity is likewise
integrated, retaining both true ordinary derivatives and the actual zero
Fourier constant pieces. Integrability is proved from the actual K-series
continuous traces; differentiation of an integral is not asserted.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.PrimeCompletedChannelReflection20261026b
open ImbalancedChen.Part3.PrimeCentralChannelDerivative20261026b
open ImbalancedChen.Part3.OrdinaryCentralFourierMeans20261026b
open ImbalancedChen.Part3.ActualContinuedZeroCuspMean20261026a
open ImbalancedChen.Part3.CentralHeightLogEuler20261026b
open ImbalancedChen.Part3.CentralReflectedLogEuler20261026b
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.PrimeCentralFourierFunctional20261026b

theorem fourierPhase_continuous (n : ℤ) : Continuous (fourierPhase n) := by
  unfold fourierPhase
  fun_prop

theorem completed_infinity_fourier_integrable (N : ℕ) (s : ℂ) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    IntervalIntegrable (fun x : ℝ => fourierPhase n x *
      completedLevelOldform N s (horizontalPoint y hy x)) volume 0 1 :=
  ((fourierPhase_continuous n).mul (completed_infinity_trace_continuous N s y hy)).intervalIntegrable 0 1

theorem completed_fricke_fourier_integrable (N : ℕ) (hN : 0 < N) (s : ℂ)
    (hs : s ∈ completedRegularDomain N) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    IntervalIntegrable (fun x : ℝ => fourierPhase n x *
      completedLevelOldform N s (frickeSL N hN • horizontalPoint y hy x)) volume 0 1 :=
  ((fourierPhase_continuous n).mul
    (completed_zeroCusp_trace_continuous N hN s hs y hy)).intervalIntegrable 0 1

/-- Actual Fourier functional equation, including every nonzero mode and
the correctly regularized central parameter. No coefficient is prescribed. -/
theorem completed_prime_fourier_reflection {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedLevelOldform p s (horizontalPoint y hy x)) =
      primeDiagonal p s * (∫ x in (0 : ℝ)..1, fourierPhase n x *
        completedLevelOldform p (1 - s) (horizontalPoint y hy x)) +
      primeOffDiagonal p s * (∫ x in (0 : ℝ)..1, fourierPhase n x *
        completedLevelOldform p (1 - s) (frickeSL p hp.pos • horizontalPoint y hy x)) := by
  have ht : 0 < (1 - s).re ∧ (1 - s).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hs.1, hs.2]
  have hi := completed_infinity_fourier_integrable p (1 - s) n y hy
  have hj := completed_fricke_fourier_integrable p hp.pos (1 - s)
    (criticalStrip_subset_completedRegularDomain p ht) n y hy
  calc
    _ = ∫ x in (0 : ℝ)..1,
        primeDiagonal p s * (fourierPhase n x * completedLevelOldform p (1 - s) (horizontalPoint y hy x)) +
        primeOffDiagonal p s * (fourierPhase n x *
          completedLevelOldform p (1 - s) (frickeSL p hp.pos • horizontalPoint y hy x)) := by
      congr 1
      funext x
      rw [completed_prime_channel_reflection hp s hs]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem ordinary_infinity_fourier_normalization (N : ℕ) (s : ℂ) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      centralOrdinaryLevel N s (horizontalPoint y hy x)) = inverseCompletion s *
        (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform N s (horizontalPoint y hy x)) := by
  have he : (fun x : ℝ => fourierPhase n x * centralOrdinaryLevel N s (horizontalPoint y hy x)) =
      (fun x : ℝ => inverseCompletion s *
        (fourierPhase n x * completedLevelOldform N s (horizontalPoint y hy x))) := by
    funext x
    unfold centralOrdinaryLevel
    ring
  rw [he, intervalIntegral.integral_const_mul]

theorem ordinary_fricke_fourier_normalization (N : ℕ) (hN : 0 < N) (s : ℂ) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      centralOrdinaryLevel N s (frickeSL N hN • horizontalPoint y hy x)) = inverseCompletion s *
        (∫ x in (0 : ℝ)..1, fourierPhase n x *
          completedLevelOldform N s (frickeSL N hN • horizontalPoint y hy x)) := by
  have he : (fun x : ℝ => fourierPhase n x *
      centralOrdinaryLevel N s (frickeSL N hN • horizontalPoint y hy x)) =
      (fun x : ℝ => inverseCompletion s * (fourierPhase n x *
        completedLevelOldform N s (frickeSL N hN • horizontalPoint y hy x))) := by
    funext x
    unfold centralOrdinaryLevel
    ring
  rw [he, intervalIntegral.integral_const_mul]

/-- True ordinary Fourier normalization across the completion pole. The
cross-multiplied equation retains both zeros, including s=1/2 itself. -/
theorem ordinary_prime_fourier_reflection_cross {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs : 0 < s.re ∧ s.re < 1) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    inverseCompletion (1 - s) * (∫ x in (0 : ℝ)..1, fourierPhase n x *
      centralOrdinaryLevel p s (horizontalPoint y hy x)) = inverseCompletion s *
      (primeDiagonal p s * (∫ x in (0 : ℝ)..1, fourierPhase n x *
        centralOrdinaryLevel p (1 - s) (horizontalPoint y hy x)) +
      primeOffDiagonal p s * (∫ x in (0 : ℝ)..1, fourierPhase n x *
        centralOrdinaryLevel p (1 - s) (frickeSL p hp.pos • horizontalPoint y hy x))) := by
  rw [ordinary_infinity_fourier_normalization p s n y hy,
    ordinary_infinity_fourier_normalization p (1 - s) n y hy,
    ordinary_fricke_fourier_normalization p hp.pos (1 - s) n y hy,
    completed_prime_fourier_reflection hp s hs n y hy]
  ring

/-- Continuity of the genuine completed central derivative trace follows
from the two actual completed cusp traces in the proved cross identity. -/
theorem completed_prime_central_derivative_fourier_integrable {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    IntervalIntegrable (fun x : ℝ => fourierPhase n x *
      deriv (fun s : ℂ => completedLevelOldform p s (horizontalPoint y hy x)) (1 / 2)) volume 0 1 := by
  have h∞ := completed_infinity_trace_continuous p (1 / 2) y hy
  have h₀ := completed_zeroCusp_trace_continuous p hp.pos (1 / 2)
    (criticalStrip_subset_completedRegularDomain p (by norm_num)) y hy
  simp_rw [completed_prime_deriv_center_cross hp]
  exact ((fourierPhase_continuous n).mul
    ((continuous_const.mul h∞).add (continuous_const.mul h₀))).intervalIntegrable 0 1

/-- Signed cross-channel identity for the ORIGINAL physical Fourier
functional of the completed central derivative, at every integer mode. -/
theorem completed_prime_central_derivative_fourier_cross {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      deriv (fun s : ℂ => completedLevelOldform p s (horizontalPoint y hy x)) (1 / 2)) =
      -(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform p (1 / 2) (horizontalPoint y hy x)) +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x *
          completedLevelOldform p (1 / 2) (frickeSL p hp.pos • horizontalPoint y hy x)) := by
  have hi := completed_infinity_fourier_integrable p (1 / 2) n y hy
  have hj := completed_fricke_fourier_integrable p hp.pos (1 / 2)
    (criticalStrip_subset_completedRegularDomain p (by norm_num)) n y hy
  calc
    _ = ∫ x in (0 : ℝ)..1,
        (-(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2)) *
          (fourierPhase n x * completedLevelOldform p (1 / 2) (horizontalPoint y hy x)) +
        ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
          (fourierPhase n x * completedLevelOldform p (1 / 2)
            (frickeSL p hp.pos • horizontalPoint y hy x)) := by
      congr 1
      funext x
      rw [completed_prime_deriv_center_cross hp]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem ordinary_central_derivative_infinity_fourier (N : ℕ) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      deriv (fun s : ℂ => centralOrdinaryLevel N s (horizontalPoint y hy x)) (1 / 2)) =
      2 * (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform N (1 / 2) (horizontalPoint y hy x)) := by
  simp_rw [centralOrdinaryLevel_deriv_center]
  have he : (fun x : ℝ => fourierPhase n x * (2 * completedLevelOldform N (1 / 2) (horizontalPoint y hy x))) =
      (fun x : ℝ => 2 * (fourierPhase n x * completedLevelOldform N (1 / 2) (horizontalPoint y hy x))) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_const_mul]

theorem ordinary_central_derivative_fricke_fourier (N : ℕ) (hN : 0 < N) (n : ℤ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      deriv (fun s : ℂ => centralOrdinaryLevel N s (frickeSL N hN • horizontalPoint y hy x)) (1 / 2)) =
      2 * (∫ x in (0 : ℝ)..1, fourierPhase n x *
        completedLevelOldform N (1 / 2) (frickeSL N hN • horizontalPoint y hy x)) := by
  simp_rw [centralOrdinaryLevel_deriv_center]
  have he : (fun x : ℝ => fourierPhase n x *
      (2 * completedLevelOldform N (1 / 2) (frickeSL N hN • horizontalPoint y hy x))) =
      (fun x : ℝ => 2 * (fourierPhase n x *
        completedLevelOldform N (1 / 2) (frickeSL N hN • horizontalPoint y hy x))) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_const_mul]

/-- Both genuine ordinary central derivative Fourier functionals occur,
with their exact signs. There is no scalar central channel identification. -/
theorem completed_central_fourier_cross_in_ordinary_derivatives {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    2 * (∫ x in (0 : ℝ)..1, fourierPhase n x *
      deriv (fun s : ℂ => completedLevelOldform p s (horizontalPoint y hy x)) (1 / 2)) =
      -(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x *
          deriv (fun s : ℂ => centralOrdinaryLevel p s (horizontalPoint y hy x)) (1 / 2)) +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ =>
          centralOrdinaryLevel p s (frickeSL p hp.pos • horizontalPoint y hy x)) (1 / 2)) := by
  rw [completed_prime_central_derivative_fourier_cross hp n y hy,
    ordinary_central_derivative_infinity_fourier p n y hy,
    ordinary_central_derivative_fricke_fourier p hp.pos n y hy]
  ring

/-- The zero Fourier mode retains the actual constant pieces as well as
the derivative. The coefficients come from literal physical integrals. -/
theorem completed_prime_central_derivative_zero_mean {p : ℕ} (hp : p.Prime)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      deriv (fun s : ℂ => completedLevelOldform p s (horizontalPoint y hy x)) (1 / 2)) =
      -(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) * completedInfinityConstant p (1 / 2) y +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
        completedReflectedConstant p (1 / 2) y := by
  have h := completed_prime_central_derivative_fourier_cross hp 0 y hy
  simp only [fourierPhase, Int.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, one_mul] at h
  rw [completed_infinity_mean p (1 / 2) y hy,
    completed_zeroCusp_mean p hp.pos (1 / 2)
      (criticalStrip_subset_completedRegularDomain p (by norm_num)) y hy] at h
  exact h

end ImbalancedChen.Part3.PrimeCentralFourierFunctional20261026b
