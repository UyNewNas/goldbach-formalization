import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/- Diagnostic reduction of existing source. No full-module acceptance. -/

namespace ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
noncomputable section
open Complex UpperHalfPlane EisensteinSeries Set Metric Topology
open scoped UpperHalfPlane

abbrev PrimitivePair := EisensteinSeries.gammaSet 1 1 0

def positiveBase (z : ℍ) (v : PrimitivePair) : ℝ :=
  z.im / ‖(v.1 0 : ℂ) * (z : ℂ) + (v.1 1 : ℂ)‖ ^ 2

def complexSeed (z : ℍ) (v : PrimitivePair) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log (positiveBase z v) : ℂ))

def complexSeedDerivative (z : ℍ) (v : PrimitivePair) (s : ℂ) : ℂ :=
  (Real.log (positiveBase z v) : ℂ) * complexSeed z v s

end
end ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic

namespace ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
noncomputable section
open Set MeasureTheory Complex Metric Topology UpperHalfPlane EisensteinSeries
open scoped UpperHalfPlane
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic

def horizontalPoint (y : ℝ) (hy : 0 < y) (x : ℝ) : ℍ := ⟨⟨x, y⟩, hy⟩

theorem complexSeed_horizontal_measurable (y : ℝ) (hy : 0 < y)
    (v : PrimitivePair) (s : ℂ) :
    Measurable (fun x : ℝ => complexSeed (horizontalPoint y hy x) v s) := by
  unfold complexSeed positiveBase horizontalPoint UpperHalfPlane.im
  fun_prop

theorem complexSeedDerivative_horizontal_measurable (y : ℝ) (hy : 0 < y)
    (v : PrimitivePair) (s : ℂ) :
    Measurable (fun x : ℝ => complexSeedDerivative (horizontalPoint y hy x) v s) := by
  unfold complexSeedDerivative complexSeed positiveBase horizontalPoint UpperHalfPlane.im
  fun_prop

end
end ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
