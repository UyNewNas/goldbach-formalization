import ImbalancedChen.Part3PeriodicRealChartVerticalDescent
import ImbalancedChen.Part3AERealChartPhysicalWeakTransfer

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Generic licensing of the FULL physical vertical weak derivative from
ordinary arbitrary-test REAL chart weak data. Honest local chart L1 (or
compact raw L2), native mixed physical L2 vectors and restricted AE
matching of their real lifts are the primitive inputs. Native real lifts
are pointwise periodic without regularity of their representatives.

The genuine compact partition/Fubini descent supplies smooth circle
tests; actual circle L2 density and proved physical test functionals then
admit ALL continuous circle tests as required by 2358. No circle weak
law, smooth-value assumption, trace or test-continuity premise is used.
Actual Gamma chart specialization is deliberately owned separately.
-/
namespace ImbalancedChen.Part3.AERealChartPhysicalVerticalWeak20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a CuspPhysicalWeakTailModes20261026b
open CuspRawWeakDerivativeBridge20261026b CuspVerticalWeakCutoffProduct20261026b
open ProductConvolutionSecondDerivatives20261026a PeriodicCompactChartTests20261026b
open PeriodicChartHeightRigidity20261026b RealChartToPhysicalCuspWeak20261026b
open PeriodicRealChartVerticalDescent20261026b CuspContinuousCircleVerticalTests20261026b
open AERealChartPhysicalWeakTransfer20261026b
attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Exact chart-to-circle raw tensor integral transport on an open tail.
Actual raw Fubini on the physical mixed-L2 input justifies the product
integral; no global real-chart integrability is silently required. -/
theorem real_lift_vertical_tensor_integral {a : ℝ} (ha : 0 < a)
    (H : CuspCylinder → ℂ) (hH : MemLp H 2 (functionMeasure a))
    (φ : C(UnitAddCircle, ℂ)) {β : ℝ → ℝ} (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    (∫ y : ℝ, ∫ x in (0 : ℝ)..1, (β y : ℂ) * φ (x : UnitAddCircle) *
      realCylinderLift H (x, y)) =
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * H z ∂derivativeMeasure a := by
  let T : ℝ → ℂ := fun y => ∫ x in (0 : ℝ)..1,
    (β y : ℂ) * φ (x : UnitAddCircle) * realCylinderLift H (x, y)
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  calc
    _ = ∫ y in Ioi (0 : ℝ), T y := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hp : 0 < y
        · simp [T, hp]
        · simp [T, hp, realCylinderLift]
    _ = ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) *
        (∫ x : UnitAddCircle, φ x * H (x, y) ∂AddCircle.haarAddCircle) := by
      rw [← integral_subtype measurableSet_Ioi]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change (∫ x in (0 : ℝ)..1,
          (β (y : ℝ) : ℂ) * φ (x : UnitAddCircle) * realCylinderLift H (x, (y : ℝ))) = _
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul]
        rw [← onePeriodChartPair_lift φ H y]
        rfl
    _ = ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) *
        (∫ x : UnitAddCircle, φ x * H (x, y) ∂AddCircle.haarAddCircle)
          ∂(volume : Measure PositiveHeight).restrict (strictHeightTail a) := by
      rw [← integral_indicator (strictHeightTail_measurable a)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        by_cases hy : y ∈ strictHeightTail a
        · simp [hy]
        · have hb : β (y : ℝ) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
          simp [hy, hb]
    _ = _ := by
      rw [raw_tensor_fubini a H hH φ hβ hc hpos]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp_rw [mul_assoc]
        rw [integral_const_mul]

/-- Ordinary real-chart vertical weak differentiation of native real
lifts implies the FULL raw physical vertical convention, including every
continuous circle factor. Pointwise periodicity comes from the lift. -/
theorem real_chart_implies_full_physical_vertical_weak {a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a)
    (hU : LocallyIntegrableOn (realCylinderLift u) {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn (realCylinderLift d) {p : Plane | a < p.2} volume)
    (hchart : HasRealChartVerticalWeakDerivative {p : Plane | a < p.2}
      (realCylinderLift u) (realCylinderLift d)) :
    HasRawWeakPhysicalVerticalDerivative a u d := by
  apply smooth_circle_tests_imply_full_vertical_weak ha
  intro φ hφ β hβ hc hs
  have ht := real_chart_vertical_one_period_tensor hU hD
    (fun y hy => realCylinderLift_periodic u y)
    (fun y hy => realCylinderLift_periodic d y) hchart φ hφ hβ hc hs
  have hd : MemLp (d : CuspCylinder → ℂ) 2 (functionMeasure a) :=
    (Lp.memLp d).of_measure_le_smul (by simp) (functionMeasure_le_derivativeMeasure ha)
  rw [real_lift_vertical_tensor_integral ha d hd φ hβ.continuous hc hs,
    real_lift_vertical_tensor_integral ha u (Lp.memLp u) φ
      (contDiff_infty_iff_deriv.mp hβ).2.continuous hc.deriv
      (tsupport_deriv_subset.trans hs)] at ht
  exact ht

/-- Arbitrary-test vertical weak differentiation is invariant under
restricted AE representative replacement. Support of the ACTUAL
directional test derivative handles the complement of the local chart. -/
theorem vertical_chart_weak_congr_ae {Ω : Set Plane} (hΩ : MeasurableSet Ω)
    {F D U V : Plane → ℂ}
    (hF : F =ᵐ[(volume : Measure Plane).restrict Ω] U)
    (hD : D =ᵐ[(volume : Measure Plane).restrict Ω] V)
    (hw : HasRealChartVerticalWeakDerivative Ω F D) :
    HasRealChartVerticalWeakDerivative Ω U V := by
  have hf := (ae_restrict_iff' hΩ).mp hF
  have hd := (ae_restrict_iff' hΩ).mp hD
  intro Ψ hΨ hc hs
  have hleft : (∫ p : Plane, star (Ψ p) * V p) = ∫ p : Plane, star (Ψ p) * D p := by
    apply integral_congr_ae
    filter_upwards [hd] with p hp
    by_cases hpin : p ∈ Ω
    · rw [hp hpin]
    · have hn : p ∉ tsupport Ψ := fun h => hpin (hs h)
      simp [image_eq_zero_of_notMem_tsupport hn]
  have hright : (∫ p : Plane, star (directional yDirection Ψ p) * U p) =
      ∫ p : Plane, star (directional yDirection Ψ p) * F p := by
    apply integral_congr_ae
    filter_upwards [hf] with p hp
    by_cases hpin : p ∈ Ω
    · rw [hp hpin]
    · have hn : p ∉ tsupport Ψ := fun h => hpin (hs h)
      have hd0 : directional yDirection Ψ p = 0 := by
        simp only [directional, fderiv_of_notMem_tsupport ℝ hn, ContinuousLinearMap.zero_apply]
      simp [hd0]
  rw [hleft, hright]
  exact hw Ψ hΨ hc hs

/-- Minimal generic ABI for actual coherent chart witnesses and native
physical mixed-L2 vectors. The output has ALL continuous circle tests. -/
theorem ae_real_chart_implies_full_physical_vertical_weak {a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) (F D : Plane → ℂ)
    (hF : LocallyIntegrableOn F {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hchart : HasRealChartVerticalWeakDerivative {p : Plane | a < p.2} F D)
    (hvalue : F =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift u)
    (hderivative : D =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift d) :
    HasRawWeakPhysicalVerticalDerivative a u d := by
  have hΩ : MeasurableSet {p : Plane | a < p.2} :=
    (isOpen_lt continuous_const continuous_snd).measurableSet
  exact real_chart_implies_full_physical_vertical_weak ha u d
    (hF.congr hvalue) (hD.congr hderivative)
    (vertical_chart_weak_congr_ae hΩ hvalue hderivative hchart)

/-- Honest compact raw chart L2 may supply the local-L1 ABI; neither
global chart integrability nor regularity of native representatives is
silently inserted into the physical vertical weak conclusion. -/
theorem compact_L2_chart_implies_full_physical_vertical_weak {a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) (F D : Plane → ℂ)
    (hlocal : ∀ K : Set Plane, IsCompact K → K ⊆ {p : Plane | a < p.2} →
      MemLp F 2 ((volume : Measure Plane).restrict K) ∧
      MemLp D 2 ((volume : Measure Plane).restrict K))
    (hchart : HasRealChartVerticalWeakDerivative {p : Plane | a < p.2} F D)
    (hvalue : F =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift u)
    (hderivative : D =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift d) :
    HasRawWeakPhysicalVerticalDerivative a u d := by
  have hΩ : IsOpen {p : Plane | a < p.2} := isOpen_lt continuous_const continuous_snd
  exact ae_real_chart_implies_full_physical_vertical_weak ha u d F D
    (locallyIntegrableOn_of_compact_memLp hΩ (fun K hK hs => (hlocal K hK hs).1))
    (locallyIntegrableOn_of_compact_memLp hΩ (fun K hK hs => (hlocal K hK hs).2))
    hchart hvalue hderivative

end
end ImbalancedChen.Part3.AERealChartPhysicalVerticalWeak20261026b
