import ImbalancedChen.Part3PeriodicRealChartWeakDescent
import ImbalancedChen.Part3WeakDerivativeIntervalRigidity

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The descended compact-height distributional equation holds at almost
every actual height. Local L1 of each one-period pairing is proved by
compact real-rectangle integrability and genuine product Fubini. The
ordinary real-height compact smooth fundamental lemma then removes the
height test. No slice equation, boundary trace or height regularity of
the unknown is assumed.
-/
namespace ImbalancedChen.Part3.PeriodicChartHeightRigidity20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a PeriodicCompactChartTests20261026b
open PeriodicRealChartWeakDescent20261026b WeakDerivativeIntervalRigidity20261026a

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def onePeriodChartPair (φ : C(UnitAddCircle, ℂ)) (H : Plane → ℂ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, φ (x : UnitAddCircle) * H (x, y)

/-- Actual local height L1 follows from local chart L1 on compact
rectangles. The circle factor is controlled by its actual uniform norm. -/
theorem onePeriodChartPair_locallyIntegrable {a : ℝ} (φ : C(UnitAddCircle, ℂ))
    {H : Plane → ℂ} (hH : LocallyIntegrableOn H {p : Plane | a < p.2} volume) :
    LocallyIntegrableOn (onePeriodChartPair φ H) (Ioi a) volume := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hKa hK
  let R : Set Plane := Icc (0 : ℝ) 1 ×ˢ K
  have hR : IsCompact R := isCompact_Icc.prod hK
  have hRU : R ⊆ {p : Plane | a < p.2} := fun p hp => hKa hp.2
  have hφ := φ.continuous
  have hφc : Continuous (fun p : Plane => φ (p.1 : UnitAddCircle)) := by fun_prop
  have hφtop : MemLp (fun p : Plane => φ (p.1 : UnitAddCircle)) ⊤
      ((volume : Measure Plane).restrict R) :=
    memLp_top_of_bound hφc.aestronglyMeasurable ‖φ‖
      (Eventually.of_forall fun p => φ.norm_coe_le_norm _)
  have hi : Integrable (fun p : Plane => φ (p.1 : UnitAddCircle) * H p)
      ((volume : Measure Plane).restrict R) :=
    (hH.integrableOn_compact_subset hRU hR).mul_of_top_right hφtop
  change Integrable (fun p : Plane => φ (p.1 : UnitAddCircle) * H p)
    (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ K)) at hi
  rw [← Measure.prod_restrict] at hi
  have hy := hi.integral_prod_right
  have he : (fun y : ℝ => ∫ x in Icc (0 : ℝ) 1, φ (x : UnitAddCircle) * H (x, y)) =
      onePeriodChartPair φ H := by
    funext y
    rw [integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le zero_le_one).symm
  rwa [he] at hy

/-- Genuine local raw chart weak differentiation and periodic values
imply the circle Green equation on almost every height in the chart.
The AE statement is derived by the compact-height fundamental lemma. -/
theorem real_chart_weak_one_period_ae {a : ℝ} {F D : Plane → ℂ}
    (hF : LocallyIntegrableOn F {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hperiodF : ∀ y : ℝ, a < y → Function.Periodic (fun x => F (x, y)) 1)
    (hperiodD : ∀ y : ℝ, a < y → Function.Periodic (fun x => D (x, y)) 1)
    (hweak : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D)
    (φ ψ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    (htest : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) :
    ∀ᵐ y : ℝ, a < y → onePeriodChartPair φ D y = -onePeriodChartPair ψ F y := by
  have hDL := onePeriodChartPair_locallyIntegrable φ hD
  have hFL := onePeriodChartPair_locallyIntegrable ψ hF
  have hsum := hDL.add hFL
  have hz : ∀ᵐ y : ℝ, y ∈ Ioi a →
      onePeriodChartPair φ D y + onePeriodChartPair ψ F y = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hsum
    intro β hβ hc hs
    have hDi : Integrable (fun y : ℝ => (β y : ℂ) * onePeriodChartPair φ D y) := by
      simpa only [Complex.real_smul] using integrable_local_test_smul hDL hβ.continuous hc hs
    have hFi : Integrable (fun y : ℝ => (β y : ℂ) * onePeriodChartPair ψ F y) := by
      simpa only [Complex.real_smul] using integrable_local_test_smul hFL hβ.continuous hc hs
    have h := real_chart_weak_one_period_tensor hF hD hperiodF hperiodD hweak
      φ ψ hφ htest hβ hc hs
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul] at h
    change (∫ y : ℝ, (β y : ℂ) * onePeriodChartPair φ D y) =
      -(∫ y : ℝ, (β y : ℂ) * onePeriodChartPair ψ F y) at h
    simp only [Pi.add_apply, Complex.real_smul, mul_add]
    rw [integral_add hDi hFi]
    exact add_eq_zero_iff_eq_neg.mpr h
  filter_upwards [hz] with y hy
  intro hay
  exact eq_neg_iff_add_eq_zero.mpr (hy hay)

end
end ImbalancedChen.Part3.PeriodicChartHeightRigidity20261026b
