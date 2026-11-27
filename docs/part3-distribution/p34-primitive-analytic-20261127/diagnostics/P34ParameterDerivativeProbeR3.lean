import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.CauchyIntegral

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

theorem complexSeed_hasDerivAt (z : ℍ) (v : PrimitivePair) (s : ℂ) :
    HasDerivAt (complexSeed z v) (complexSeedDerivative z v s) s := by
  unfold complexSeedDerivative complexSeed
  simpa only [mul_comm] using
    (hasDerivAt_mul_const (x := s) (Real.log (positiveBase z v) : ℂ)).cexp

end

end ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
