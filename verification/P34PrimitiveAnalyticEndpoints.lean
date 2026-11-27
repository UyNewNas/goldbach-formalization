import ImbalancedChen.Part3RealEisensteinSeedConvergence
import ImbalancedChen.Part3PrimitiveEisensteinParameterAnalytic
import ImbalancedChen.Part3PrimitiveEisensteinFourierParameterAnalytic

open Set MeasureTheory UpperHalfPlane
open scoped UpperHalfPlane BigOperators Topology
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

example : ∀ (s : ℝ), 1 < s → ∀ z : ℍ, Summable (seed s z) :=
  @seed_summable

example : ∀ (s : ℝ), 1 < s → ∀ z : ℍ,
    Summable (fun v : EisensteinSeries.gammaSet 1 1 0 => seed s z v.1) :=
  @primitiveSeed_summable

example : ∀ (s : ℝ), 1 < s → TendstoLocallyUniformly
    (fun F : Finset (Fin 2 → ℤ) => fun z : ℍ => ∑ v ∈ F, seed s z v)
    (fun z : ℍ => ∑' v : Fin 2 → ℤ, seed s z v) Filter.atTop :=
  @seed_tendstoLocallyUniformly

example : ∀ (z : ℍ) (s : ℂ), 1 < s.re →
    HasDerivAt (fun w : ℂ => primitiveComplexEisenstein w z)
      ((1 / 2 : ℂ) * ∑' v : EisensteinSeries.gammaSet 1 1 0, complexSeedDerivative z v s) s :=
  @primitiveComplexEisenstein_hasDerivAt

example : ∀ z : ℍ,
    AnalyticOnNhd ℂ (fun s => primitiveComplexEisenstein s z) {s : ℂ | 1 < s.re} :=
  @primitiveComplexEisenstein_analyticOnNhd

example : ∀ (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ), 1 < s.re →
    HasDerivAt (actualPrimitiveFourier y hy n)
      (∫ x in (0 : ℝ)..1, fourierIntegrandDerivative y hy n s x) s :=
  @actualPrimitiveFourier_hasDerivAt

example : ∀ (y : ℝ) (hy : 0 < y) (n : ℤ),
    AnalyticOnNhd ℂ (actualPrimitiveFourier y hy n) {s : ℂ | 1 < s.re} :=
  @actualPrimitiveFourier_analyticOnNhd

example (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ) :
    seed s z v = z.im ^ s * ‖(v 0 : ℂ) * (z : ℂ) + (v 1 : ℂ)‖ ^ (-(2 * s)) := rfl

example (s : ℂ) (z : ℍ) :
    primitiveComplexEisenstein s z =
      (1 / 2 : ℂ) * ∑' v : EisensteinSeries.gammaSet 1 1 0, complexSeed z v s := rfl

example (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) :
    actualPrimitiveFourier y hy n s = ∫ x in (0 : ℝ)..1,
      Complex.exp (((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I) *
        primitiveComplexEisenstein s (horizontalPoint y hy x) := rfl

example (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) (x : ℝ) :
    fourierIntegrandDerivative y hy n s x =
      Complex.exp (((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I) *
        ((1 / 2 : ℂ) * ∑' v : EisensteinSeries.gammaSet 1 1 0,
          complexSeedDerivative (horizontalPoint y hy x) v s) := rfl
