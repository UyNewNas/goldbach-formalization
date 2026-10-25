import ImbalancedChen.Part3ActualCanonicalEisensteinFourierSeries
import ImbalancedChen.Part3PrimitiveEisensteinHorizontalContinuity

/-!
Pointwise reconstruction of the literal complex primitive Eisenstein series
throughout Re(s)>1. The actual horizontal trace descends continuously to
R/Z by its proved periodicity. Its native AddCircle Fourier coefficients
are the actual scalar integrals, already evaluated canonically. Absolute
coefficient summability was proved from the actual Fourier-Bessel decay.
The pinned Fourier Hilbert-basis reconstruction theorem then gives equality
at every point, followed by the exact positive/negative signed regrouping.

No reconstruction, HasSum target, coefficient equality or normal-convergence
hypothesis is supplied by the caller. SOURCE_WRITTEN_UNCOMPILED.
-/

namespace ImbalancedChen.Part3ActualEisensteinPointwiseFourier

noncomputable section

open Set Filter
open scoped Topology BigOperators UpperHalfPlane
open Part3.PrimitiveEisensteinParameterAnalytic
open Part3.PrimitiveEisensteinFourierParameterAnalytic
open Part3.PrimitiveEisensteinHorizontalContinuity
open Part3.ActualComplexEisensteinCanonicalFourier
open Part3ActualCanonicalEisensteinFourierSeries
open Part3ActualRamanujanBesselNormalConvergence

/-- The actual continuous period-one primitive trace on the native circle. -/
def traceCircle (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun := (primitiveComplexEisenstein_horizontal_periodic y hy s hs).lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact (primitiveComplexEisenstein_horizontal_continuous y hy s hs).quotient_liftOn' _

@[simp] theorem traceCircle_coe_apply (y : ℝ) (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    traceCircle y hy s hs (x : AddCircle (1 : ℝ)) =
      primitiveComplexEisenstein s (horizontalPoint y hy x) := rfl

private theorem native_negative_phase (n : ℤ) (x : ℝ) :
    AddCircle.fourier (-n) (x : AddCircle (1 : ℝ)) = fourierPhase n x := by
  rw [AddCircle.fourier_coe_apply]
  unfold fourierPhase
  simp only [div_one]
  push_cast
  congr 1
  ring

/-- The native circle coefficient is exactly the actual literal Fourier
integral, with the original negative phase and period-one normalization. -/
theorem traceCircle_fourierCoeff (y : ℝ) (hy : 0 < y)
    (s : ℂ) (hs : 1 < s.re) (n : ℤ) :
    AddCircle.fourierCoeff (traceCircle y hy s hs) n =
      complexCanonicalCoefficient s y n := by
  calc
    _ = actualPrimitiveFourier y hy n s := by
      rw [AddCircle.fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)]
      simp only [div_one, one_smul, zero_add, smul_eq_mul]
      unfold actualPrimitiveFourier fourierIntegrand
      apply intervalIntegral.integral_congr
      intro x _hx
      rw [native_negative_phase, traceCircle_coe_apply]
    _ = _ := actualPrimitiveFourier_eq_complexCanonical y hy n s hs

/-- This is a genuine HasSum conclusion for the physical trace, derived
from its proved continuous periodic realization and actual coefficients. -/
theorem primitiveComplexEisenstein_fourier_hasSum
    (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    HasSum (fun n : ℤ => complexCanonicalCoefficient s y n *
      AddCircle.fourier n (x : AddCircle (1 : ℝ)))
      (primitiveComplexEisenstein s (horizontalPoint y hy x)) := by
  have hcoeff : AddCircle.fourierCoeff (traceCircle y hy s hs) =
      complexCanonicalCoefficient s y :=
    funext (traceCircle_fourierCoeff y hy s hs)
  have hsum : Summable (AddCircle.fourierCoeff (traceCircle y hy s hs)) := by
    rw [hcoeff]
    exact canonicalCoefficient_summable s hy
  have h := AddCircle.has_pointwise_sum_fourier_series_of_summable
    (f := traceCircle y hy s hs) hsum (x : AddCircle (1 : ℝ))
  simpa only [hcoeff, traceCircle_coe_apply, smul_eq_mul] using h

/-- The literal full pointwise Fourier expansion on the true initial
complex halfplane, with its exact constant, Gamma/zeta factor, sqrt height,
and positive/negative Bessel pairs. Every real horizontal x is covered. -/
theorem primitiveComplexEisenstein_pointwise_fourier
    (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) (x : ℝ) :
    primitiveComplexEisenstein s (horizontalPoint y hy x) =
      (y : ℂ) ^ s + complexScattering s * (y : ℂ) ^ (1 - s) +
        nonzeroNormalization s y * ∑' k : ℕ, nonzeroFrequencyPair k s y x := by
  calc
    _ = ∑' n : ℤ, complexCanonicalCoefficient s y n *
        AddCircle.fourier n (x : AddCircle (1 : ℝ)) :=
      (primitiveComplexEisenstein_fourier_hasSum y hy s hs x).tsum_eq.symm
    _ = _ := canonicalFourierSeries_eq s hy x

end

end ImbalancedChen.Part3ActualEisensteinPointwiseFourier
