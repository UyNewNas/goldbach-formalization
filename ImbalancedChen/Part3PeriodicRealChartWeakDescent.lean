import ImbalancedChen.Part3PeriodicCompactChartTests
import ImbalancedChen.Part3LocalSmoothWeakDerivativeUniqueness

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Real-chart local weak horizontal differentiation descends to genuine
one-period raw tensor testing. Every compact partitioned product is
integrable by ordinary local L1 and actual compact test support. Actual
Bochner Fubini exposes the height slices; the integer unit partition
unfolds the main terms and its derivative cancels the seam term.
Only true period-one values of F and D are used, with NO H1 trace or
endpoint assumptions. Global physical mixed L² licensing is separate.
-/
namespace ImbalancedChen.Part3.PeriodicRealChartWeakDescent20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open SmoothIntegerUnitPartition20261026b PeriodicCompactPartitionUnfolding20261026b
open ProductConvolutionSecondDerivatives20261026a PeriodicCompactChartTests20261026b
open LocalSmoothWeakDerivativeUniqueness20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem compact_bilinear_product_integrable {a : ℝ} {H Ψ : Plane → ℂ}
    (hH : LocallyIntegrableOn H {p : Plane | a < p.2} volume)
    (hΨ : Continuous Ψ) (hc : HasCompactSupport Ψ)
    (hs : tsupport Ψ ⊆ {p : Plane | a < p.2}) :
    Integrable (fun p : Plane => Ψ p * H p) := by
  have hi := local_compact_test_product_integrable hH hΨ.star
    (hc.comp_left (by simp)) ((tsupport_comp_subset (by simp) Ψ).trans hs)
  simpa only [star_star] using hi

/-- Actual Fubini and periodic unfolding for a compact chart weight.
No regularity of H besides the displayed actual product integrability is
needed in this step. -/
theorem unfold_compact_chart_tensor {a : ℝ} (χ : ℝ → ℝ) (c : ℝ)
    (hl : ∀ x ≤ -1, χ x = 0) (hr : ∀ x, 1 ≤ x → χ x = 0)
    (ht : ∀ x ∈ Icc (0 : ℝ) 1, χ x + χ (x - 1) = c)
    (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ) (hs : tsupport β ⊆ Ioi a)
    (H : Plane → ℂ) (hperiod : ∀ y : ℝ, a < y → Function.Periodic (fun x => H (x, y)) 1)
    (hi : Integrable (fun p : Plane => periodicChartTensor χ φ β p * H p)) :
    (∫ p : Plane, periodicChartTensor χ φ β p * H p) =
      (c : ℂ) * (∫ y : ℝ, ∫ x in (0 : ℝ)..1,
        (β y : ℂ) * φ (x : UnitAddCircle) * H (x, y)) := by
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with y hy
  by_cases hay : a < y
  · let f : ℝ → ℂ := fun x => φ (x : UnitAddCircle) * (β y : ℂ) * H (x, y)
    have hp : Function.Periodic f 1 := by
      intro x
      simp only [f, AddCircle.coe_add, AddCircle.coe_period, add_zero, hperiod y hay x]
    have hif : Integrable (fun x => (χ x : ℂ) * f x) := by
      simpa only [periodicChartTensor, f, mul_assoc] using hy
    have hu := compact_periodic_weight_integral χ c hl hr ht f hp hif
    simpa only [periodicChartTensor, f, mul_assoc, mul_left_comm] using hu
  · have hb : β y = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hay (hs ht))
    simp [periodicChartTensor, hb]

/-- Descended raw one-period distributional equation. It is obtained
from the REAL chart weak equation, not assumed on circle slices. -/
theorem real_chart_weak_one_period_tensor {a : ℝ} {F D : Plane → ℂ}
    (hF : LocallyIntegrableOn F {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hperiodF : ∀ y : ℝ, a < y → Function.Periodic (fun x => F (x, y)) 1)
    (hperiodD : ∀ y : ℝ, a < y → Function.Periodic (fun x => D (x, y)) 1)
    (hweak : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D)
    (φ ψ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    (htest : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    (∫ y : ℝ, ∫ x in (0 : ℝ)..1, (β y : ℂ) * φ (x : UnitAddCircle) * D (x, y)) =
      -(∫ y : ℝ, ∫ x in (0 : ℝ)..1, (β y : ℂ) * ψ (x : UnitAddCircle) * F (x, y)) := by
  have hψ : ContDiff ℝ ∞ (fun t : ℝ => ψ (t : UnitAddCircle)) := by
    have he : (fun t : ℝ => ψ (t : UnitAddCircle)) =
        deriv (fun t : ℝ => φ (t : UnitAddCircle)) := funext fun t => (htest t).deriv.symm
    rw [he]
    exact (contDiff_infty_iff_deriv.mp hφ).2
  have hαd : ContDiff ℝ ∞ (deriv horizontalUnitPartition) :=
    (contDiff_infty_iff_deriv.mp horizontalUnitPartition_cinfty).2
  have hiD : Integrable (fun p : Plane =>
      periodicChartTensor horizontalUnitPartition φ β p * D p) :=
    compact_bilinear_product_integrable hD
      (periodicChartTensor_smooth horizontalUnitPartition_cinfty φ hφ hβ).continuous
      (periodicChartTensor_compact horizontalUnitPartition_compact φ hc)
      (periodicChartTensor_height_support φ hs)
  have hiSeam : Integrable (fun p : Plane =>
      periodicChartTensor (deriv horizontalUnitPartition) φ β p * F p) :=
    compact_bilinear_product_integrable hF
      (periodicChartTensor_smooth hαd φ hφ hβ).continuous
      (periodicChartTensor_compact horizontalUnitPartition_compact.deriv φ hc)
      (periodicChartTensor_height_support φ hs)
  have hiMain : Integrable (fun p : Plane =>
      periodicChartTensor horizontalUnitPartition ψ β p * F p) :=
    compact_bilinear_product_integrable hF
      (periodicChartTensor_smooth horizontalUnitPartition_cinfty ψ hψ hβ).continuous
      (periodicChartTensor_compact horizontalUnitPartition_compact ψ hc)
      (periodicChartTensor_height_support ψ hs)
  have hDunfold := unfold_compact_chart_tensor horizontalUnitPartition 1
    horizontalUnitPartition_zero_left horizontalUnitPartition_zero_right
    (fun x hx => partition_two_terms hx) φ β hs D hperiodD hiD
  have hMainUnfold := unfold_compact_chart_tensor horizontalUnitPartition 1
    horizontalUnitPartition_zero_left horizontalUnitPartition_zero_right
    (fun x hx => partition_two_terms hx) ψ β hs F hperiodF hiMain
  have hSeamUnfold := unfold_compact_chart_tensor (deriv horizontalUnitPartition) 0
    partition_derivative_zero_left partition_derivative_zero_right
    (fun x hx => partition_derivative_two_terms hx) φ β hs F hperiodF hiSeam
  have hw := local_weak_partition_tensor hweak φ ψ hφ htest hβ hc hs
  simp_rw [add_mul] at hw
  rw [integral_add hiSeam hiMain, hDunfold, hMainUnfold, hSeamUnfold] at hw
  simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, zero_add] using hw

end
end ImbalancedChen.Part3.PeriodicRealChartWeakDescent20261026b
