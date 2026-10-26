import ImbalancedChen.Part3ActualQuotientInfinityCylinderFourier
import ImbalancedChen.Part3CuspUpperBandMixedFourierConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every literal integer Fourier coefficient of EVERY original quotient L2
vector belongs to the actual dy/y^2 height L2 space on every high infinity
tail. A native coefficient vector is constructed by the proved spatial
cylinder map, zero extension, and existing cylinder Fourier adjoint.
Its norm is bounded by the original physical quotient norm. In particular
the original quotient MEAN has genuine infinity endpoint L2 admissibility.
Small-height growth and differential regularity are not asserted.
-/
namespace ImbalancedChen.Part3.ActualInfinityFourierHeightL220261026b

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane ENNReal
open Gamma0QuotientCellPushforward20261025a
open CuspCylinderMeasure20261024z
open ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open ActualPoincareSpectralCoefficient20261026a
open ActualHighStripNativeCylinderMeasure20261026b
open ActualHighStripCylinderL2Equivalence20261026b
open ActualInfinityHighTailL2Pullback20261026b
open ActualQuotientInfinityCylinderFourier20261026b
open CuspUpperBandMixedFourierConvergence20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def actualInfinityCylinderExtension (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (f : QuotientL2 N) : CylinderL2 :=
  restrictedZeroExtensionVector cylinderMeasure (closedCylinderTail Y)
    (closedCylinderTail_measurable Y) (actualQuotientInfinityCylinder N hY f)

theorem actualInfinityCylinderExtension_norm (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (f : QuotientL2 N) :
    ‖actualInfinityCylinderExtension N hY f‖ = ‖actualQuotientInfinityCylinder N hY f‖ :=
  (restrictedZeroExtension cylinderMeasure (closedCylinderTail Y)
    (closedCylinderTail_measurable Y)).norm_map _

theorem actualInfinityCylinderExtension_ae (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (f : QuotientL2 N) :
    actualInfinityCylinderExtension N hY f =ᵐ[cylinderMeasure]
      (closedCylinderTail Y).indicator
        (fun p => f (orbitProjection N
          (ActualHighStripCylinderL2Equivalence20261026b.nativeCylinderPoint p))) := by
  have hp := (ae_restrict_iff' (closedCylinderTail_measurable Y)).mp
    (actualQuotientInfinityCylinder_ae N hY f)
  filter_upwards [restrictedZeroExtensionVector_ae cylinderMeasure (closedCylinderTail Y)
    (closedCylinderTail_measurable Y) (actualQuotientInfinityCylinder N hY f), hp]
      with p he hp
  rw [he]
  by_cases hpt : p ∈ closedCylinderTail Y
  · simp only [Set.indicator_of_mem hpt, hp hpt]
  · simp only [Set.indicator_of_notMem hpt]

/-- This native height vector carries the literal quotient coefficient,
with its high tail cut off and zero extended below that tail. -/
def actualInfinityHeightCoefficient (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (f : QuotientL2 N) (m : ℤ) : HeightL2 :=
  cylinderCoefficient m (actualInfinityCylinderExtension N hY f)

theorem actualInfinityHeightCoefficient_norm_le (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (f : QuotientL2 N) (m : ℤ) :
    ‖actualInfinityHeightCoefficient N hY f m‖ ≤ ‖f‖ := by
  have hm : ‖cylinderCoefficient m‖ ≤ 1 := by
    rw [cylinderCoefficient, ContinuousLinearMap.adjoint.norm_map]
    exact (modeEmbedding m).norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖cylinderCoefficient m‖ * ‖actualInfinityCylinderExtension N hY f‖ :=
      (cylinderCoefficient m).le_opNorm _
    _ ≤ 1 * ‖actualInfinityCylinderExtension N hY f‖ :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ = ‖actualQuotientInfinityCylinder N hY f‖ := by
      rw [one_mul, actualInfinityCylinderExtension_norm]
    _ ≤ ‖f‖ := actualQuotientInfinityCylinder_norm_le N hY f

theorem actualInfinityHeightCoefficient_ae (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (f : QuotientL2 N) (m : ℤ) :
    actualInfinityHeightCoefficient N hY f m =ᵐ[heightMeasure]
      (closedHeightTail Y).indicator (fun y : PositiveHeight => actualTestFourier N f m (y : ℝ)) := by
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂heightMeasure.prod AddCircle.haarAddCircle,
      actualInfinityCylinderExtension N hY f (p.2, p.1) =
        (closedCylinderTail Y).indicator
          (fun z => f (orbitProjection N
            (ActualHighStripCylinderL2Equivalence20261026b.nativeCylinderPoint z))) (p.2, p.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (actualInfinityCylinderExtension_ae N hY f)
  have hsections := ae_ae_of_ae_prod hswap
  filter_upwards [cylinderCoefficient_ae m (actualInfinityCylinderExtension N hY f), hsections]
    with y hm hsec
  rw [hm]
  by_cases hy : y ∈ closedHeightTail Y
  · rw [Set.indicator_of_mem hy]
    have hs : (fun x : UnitAddCircle => actualInfinityCylinderExtension N hY f (x, y)) =ᵐ[
        AddCircle.haarAddCircle] (fun x => f (orbitProjection N
          (ActualHighStripCylinderL2Equivalence20261026b.nativeCylinderPoint (x, y)))) := by
      filter_upwards [hsec] with x hx
      simpa only [closedCylinderTail, closedHeightTail, Set.mem_setOf_eq,
        Set.indicator_of_mem hy] using hx
    change AddCircle.fourierCoeff (fun x : UnitAddCircle =>
      actualInfinityCylinderExtension N hY f (x, y)) m = _
    rw [congrFun (AddCircle.fourierCoeff_congr_ae hs) m]
    exact quotient_circle_coefficient_eq_actualFourier N f m y
  · rw [Set.indicator_of_notMem hy]
    have hs : (fun x : UnitAddCircle => actualInfinityCylinderExtension N hY f (x, y)) =ᵐ[
        AddCircle.haarAddCircle] (fun _ => 0) := by
      filter_upwards [hsec] with x hx
      simpa only [closedCylinderTail, closedHeightTail, Set.mem_setOf_eq,
        Set.indicator_of_notMem hy] using hx
    change AddCircle.fourierCoeff (fun x : UnitAddCircle =>
      actualInfinityCylinderExtension N hY f (x, y)) m = _
    rw [congrFun (AddCircle.fourierCoeff_congr_ae hs) m]
    simp

/-- Actual quotient L2 alone supplies infinity endpoint admissibility
of every original coefficient, including m=0, without continuity. -/
theorem actualTestFourier_memLp_infinity_tail (N : ℕ) [NeZero N] {Y : ℝ}
    (hY : 1 < Y) (f : QuotientL2 N) (m : ℤ) :
    MemLp (fun y : PositiveHeight => actualTestFourier N f m (y : ℝ)) 2
      (heightMeasure.restrict (closedHeightTail Y)) := by
  apply (memLp_indicator_iff_restrict (closedHeightTail_measurable Y)).mp
  exact (actualInfinityHeightCoefficient N hY f m).memLp.congr
    (actualInfinityHeightCoefficient_ae N hY f m)

end
end ImbalancedChen.Part3.ActualInfinityFourierHeightL220261026b
