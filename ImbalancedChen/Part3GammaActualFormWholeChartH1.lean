import ImbalancedChen.Part3GammaCompletedGradientClassicalRepresentative
import ImbalancedChen.Part3GammaActualAdjointWholeChartH1

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Every vector of the EXISTING actual energy form has ordinary H1_loc on
the whole positive chart, even when it has no operator output in L2.
The derivatives are constructed by the actual local completed gradient
and canonical planar L2 unitary. No elliptic PDE, adjoint membership,
smooth representative, H1 premise, or global ordinary L2 bound is used.
-/

namespace ImbalancedChen.Part3.GammaActualFormWholeChartH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a CompactC2ProductMollifier20261026a
open Gamma0PhysicalClosedDirichletForm20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CompactDefectMollifier20261026a UpperRectangleMollifierGeometry20261026b
open ActualPullbackLocalH1Transfer20261026b WholeUpperChartWeakH1Patching20261026b
open GammaActualAdjointWholeChartH120261026b
open GammaCompletedGradientClassicalRepresentative20261026b
open ArbitraryCompactFirstGradientIBP20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z

/-- Direct form-to-coordinate construction on an arbitrary positive
rectangle, using the same actual completed energy vector throughout. -/
theorem completed_every_positive_rectangle_H1 (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (L R c d : ℝ)
    (hLR : L ≤ R) (hcd : c ≤ d) (hcpos : 0 < c) :
    HasCoordinateLocalH1On (Icc L R ×ˢ Icc c d)
      (actualPlanePullback N (physicalProjection N e)) := by
  let Ω : Set Plane := Icc L R ×ˢ Icc c d
  let K := upperRectangle L R c d
  let F := actualPlanePullback N (physicalProjection N e)
  have hK : IsCompact K := upperRectangle_isCompact L R c d hcpos
  have hbound : ∀ z ∈ K, z.im ≤ d := fun z hz => hz.2.2
  have hΩ : MeasurableSet Ω := measurableSet_Icc.prod measurableSet_Icc
  have heq : localizedPlane N K d (physicalProjection N e) =ᵐ[
      (volume : Measure Plane).restrict Ω] F :=
    (ae_restrict_iff' hΩ).2 (Eventually.of_forall
      (localizedPlane_eq_actual_on_rectangle N hcpos hbound
        (physicalProjection N e) (Subset.refl K)))
  have hF : MemLp F 2 ((volume : Measure Plane).restrict Ω) :=
    (memLp_congr_ae heq).mp
      ((localizedPlane_memLp N hK (hcpos.le.trans hcd) (physicalProjection N e)).restrict Ω)
  let X := planarCompletedPartial N hK false e
  let Y := planarCompletedPartial N hK true e
  have hX : MemLp X 2 (volume : Measure Plane) := planarCompletedPartial_memLp N hK false e
  have hY : MemLp Y 2 (volume : Measure Plane) := planarCompletedPartial_memLp N hK true e
  refine ⟨hF,hX.toLp X,hY.toLp Y,?_⟩
  intro ψ hψ hc hs
  have hpos : Ω ⊆ MaassWeakOperatorCore20261024zz.positiveChart :=
    fun p hp => hcpos.trans_le hp.2.1
  have hUK : ∀ z : UpperHalfPlane, (z.re,z.im) ∈ Ω → z ∈ K := fun z hz => hz
  have hrep : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict K),
      (physicalProjection N e) (orbitProjection N z) = F (z.re,z.im) :=
    Eventually.of_forall (fun z => (actualPlanePullback_at_upper N (physicalProjection N e) z).symm)
  have hx := planarCompletedPartial_weak_for_representative N hK false e
    hpos hUK F hrep hψ hc hs
  have hy := planarCompletedPartial_weak_for_representative N hK true e
    hpos hUK F hrep hψ hc hs
  have hpx : (∫ p, star (ψ p) * (hX.toLp X) p) = ∫ p, star (ψ p) * X p := by
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp] with p hp
    rw [hp]
  have hpy : (∫ p, star (ψ p) * (hY.toLp Y) p) = ∫ p, star (ψ p) * Y p := by
    apply integral_congr_ae
    filter_upwards [hY.coeFn_toLp] with p hp
    rw [hp]
  constructor
  · simpa [X,coordinateDirection,ex,xDirection] using hpx.trans hx
  · simpa [Y,coordinateDirection,ey,yDirection] using hpy.trans hy

/-- The whole-chart ordinary weak gradient is patched from actual
completed local gradients. There is no operator-domain premise. -/
theorem completed_whole_upperChart_H1 (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    HasUpperChartWeakH1 (actualPlanePullback N (physicalProjection N e)) :=
  wholeChart_H1_of_rectangle_localH1 _ (completed_every_positive_rectangle_H1 N e)

theorem actual_form_whole_upperChart_H1 (N : ℕ) [NeZero N]
    (u : actualEnergyFormDomain N) :
    HasUpperChartWeakH1 (actualPlanePullback N (u : QuotientL2 N)) := by
  simpa only [actualEnergyLift_projection] using
    completed_whole_upperChart_H1 N (actualEnergyLift N u)

end
end ImbalancedChen.Part3.GammaActualFormWholeChartH120261026b
