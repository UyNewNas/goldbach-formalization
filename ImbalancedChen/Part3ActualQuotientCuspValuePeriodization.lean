import ImbalancedChen.Part3RealChartToPhysicalCuspWeak
import ImbalancedChen.Part3ActualPullbackLocalH1Transfer
import ImbalancedChen.Part3GammaInfinityTranslationStrip

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ACTUAL arbitrary Gamma0 quotient L² value has a true period-one
real-chart pullback, proved from orbitProjection and the actual T in
Gamma0(N). It therefore has an exact circle-valued representative whose
real lift is the original chart pullback. No automorphy, regularity,
boundary trace or derivative periodicity premise is inserted. Membership
of this cylinder function in global physical L² remains separately
licensed by the actual geometric norm suppliers.
-/
namespace ImbalancedChen.Part3.ActualQuotientCuspValuePeriodization20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0QuotientCellPushforward20261025a
open ActualPullbackLocalH1Transfer20261026b GammaInfinityTranslationStrip20261025a
open CuspCylinderMeasure20261024z RealChartToPhysicalCuspWeak20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The arbitrary native quotient L² representative is pointwise
T-invariant after orbit projection. This includes every real height,
with the genuine zero extension below the upper chart. -/
theorem actual_quotient_pullback_period_one (N : ℕ) [NeZero N] (f : QuotientL2 N) (y : ℝ) :
    Function.Periodic (fun x : ℝ => actualPlanePullback N f (x, y)) 1 := by
  intro x
  by_cases hy : 0 < y
  · let z : UpperHalfPlane := ⟨⟨x, y⟩, hy⟩
    let z1 : UpperHalfPlane := ⟨⟨x + 1, y⟩, hy⟩
    let γ : CongruenceSubgroup.Gamma0 N := (infinityTranslation N 1).val
    have hT : γ • z = z1 := by
      change translate 1 z = z1
      apply UpperHalfPlane.ext
      apply Complex.ext
      · change (translate 1 z).re = x + 1
        rw [translate_re]
        simp only [Int.cast_one, z]
        ring
      · change (translate 1 z).im = y
        rw [translate_eq_vadd, UpperHalfPlane.vadd_im]
        rfl
    calc
      actualPlanePullback N f (x + 1, y) = f (orbitProjection N z1) := by
        simp only [actualPlanePullback, dif_pos hy, z1]
      _ = f (orbitProjection N (γ • z)) := by rw [hT]
      _ = f (orbitProjection N z) := by rw [orbitProjection_smul]
      _ = actualPlanePullback N f (x, y) := by
        simp only [actualPlanePullback, dif_pos hy, z]
  · simp only [actualPlanePullback, dif_neg hy]

def actualOrbitCylinderValue (N : ℕ) [NeZero N] (f : QuotientL2 N) (z : CuspCylinder) : ℂ :=
  (actual_quotient_pullback_period_one N f (z.2 : ℝ)).lift z.1

/-- Exact value descent, before any Lp quotient or geometric licensing. -/
@[simp] theorem actualOrbitCylinderValue_coe (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (x : ℝ) (y : PositiveHeight) :
    actualOrbitCylinderValue N f ((x : UnitAddCircle), y) = actualPlanePullback N f (x, (y : ℝ)) :=
  Function.Periodic.lift_coe _ x

theorem real_lift_actualOrbitCylinderValue (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    realCylinderLift (actualOrbitCylinderValue N f) = actualPlanePullback N f := by
  funext p
  by_cases hp : 0 < p.2
  · rw [realCylinderLift, dif_pos hp, actualOrbitCylinderValue_coe]
  · simp only [realCylinderLift, actualPlanePullback, dif_neg hp]

end
end ImbalancedChen.Part3.ActualQuotientCuspValuePeriodization20261026b
