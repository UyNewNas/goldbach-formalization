import ImbalancedChen.Part3ActualComplexEisensteinCanonicalFourier

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.ActualEisensteinCanonicalFourier20261025a
open ImbalancedChen.Part3.ActualComplexEisensteinCanonicalFourier
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

example (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖fourierBesselTerm n s y x‖) :=
  fourierBessel_norm_summable s hy x

example {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => ∑' n, nonzeroFrequencyPair n s y x) :=
  nonzeroFrequencyPair_sum_differentiable hy x

example (s : ℝ) (hs : 1 < s) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    actualEisensteinFourier 1 s y hy n = canonicalFourierCoefficient s y n :=
  actualEisensteinFourier_eq_canonical s hs y hy n

example (y : ℝ) (hy : 0 < y) (n : ℤ) (s : ℂ) (hs : 1 < s.re) :
    actualPrimitiveFourier y hy n s = complexCanonicalCoefficient s y n :=
  actualPrimitiveFourier_eq_complexCanonical y hy n s hs

example (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : 1 < s.re) :
    actualPrimitiveFourier y hy 0 s =
      (y : ℂ) ^ s + complexScattering s * (y : ℂ) ^ (1 - s) :=
  actualPrimitiveFourier_zero_complex y hy s hs

example (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    actualPrimitiveFourier y hy n s = complexNonzeroCoefficient s y n :=
  actualPrimitiveFourier_nonzero_complex y hy n hn s hs

-- Literal normalization check, independent of the coefficient alias spelling.
example (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    actualPrimitiveFourier y hy n s =
      ((2 : ℂ) * (Real.pi : ℂ) ^ s) / (Complex.Gamma s * riemannZeta (2 * s)) *
        (((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) *
          ImbalancedChen.Part3ActualRamanujanDirichletSeries.divisorFactor n.natAbs (2 * s) *
          (Real.sqrt y : ℂ) *
          ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly.complexOrderK (s - 1 / 2)
            (2 * Real.pi * |(n : ℝ)| * y)) :=
  actualPrimitiveFourier_nonzero_complex y hy n hn s hs

example (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (v : EisensteinSeries.gammaSet 1 1 0) :
    (primitivePairEquiv g v).val = Matrix.vecMul v.val g.val := rfl
