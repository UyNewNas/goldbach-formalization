import ImbalancedChen.Part3CuspContinuousCircleVerticalTests
import ImbalancedChen.Part3PeriodicRealChartWeakDescent

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Ordinary arbitrary-test REAL chart vertical weak differentiation descends
to genuine one-period vertical tensor testing. The actual compact integer
unit partition and existing integrable periodic unfolding are reused.
The partition depends only on x, so its vertical derivative is ZERO;
there is no seam derivative term and no endpoint trace assumption.
Local L1 supplies all compact test integrability before actual Fubini.
-/
namespace ImbalancedChen.Part3.PeriodicRealChartVerticalDescent20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a PlanarFrechetCompactGreen20261026b
open SmoothIntegerUnitPartition20261026b PeriodicCompactPartitionUnfolding20261026b
open PeriodicCompactChartTests20261026b PeriodicRealChartWeakDescent20261026b
open LocalSmoothWeakDerivativeUniqueness20261026b
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The ordinary local raw vertical distribution equation. This is
definitionally the arbitrary-test ABI used by actual normalized charts. -/
def HasRealChartVerticalWeakDerivative (Ω : Set Plane) (F D : Plane → ℂ) : Prop :=
  ∀ Ψ : Plane → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ω →
    (∫ p : Plane, star (Ψ p) * D p) =
      -(∫ p : Plane, star (directional yDirection Ψ p) * F p)

theorem partition_chart_vertical_derivative (φ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (p : Plane) :
    directional yDirection (periodicChartTensor horizontalUnitPartition φ β) p =
      periodicChartTensor horizontalUnitPartition φ (deriv β) p := by
  rw [directional_y_eq_slice
    (periodicChartTensor_smooth horizontalUnitPartition_cinfty φ hφ hβ)]
  have hd := ((hβ.differentiable (by simp) p.2).hasDerivAt.ofReal_comp).const_mul
    ((horizontalUnitPartition p.1 : ℂ) * φ (p.1 : UnitAddCircle))
  simpa only [periodicChartTensor, mul_assoc] using hd.deriv

/-- Inserting the actual conjugate compact product test gives a bilinear
vertical tensor equation. No alpha-prime term appears. -/
theorem local_vertical_partition_tensor {a : ℝ} {F D : Plane → ℂ}
    (hweak : HasRealChartVerticalWeakDerivative {p : Plane | a < p.2} F D)
    (φ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi a) :
    (∫ p : Plane, periodicChartTensor horizontalUnitPartition φ β p * D p) =
      -(∫ p : Plane, periodicChartTensor horizontalUnitPartition φ (deriv β) p * F p) := by
  let Ψ := periodicChartTensor horizontalUnitPartition φ β
  have hΨ := periodicChartTensor_smooth horizontalUnitPartition_cinfty φ hφ hβ
  have hcΨ := periodicChartTensor_compact horizontalUnitPartition_compact φ hc
  have hsΨ := periodicChartTensor_height_support φ hs
  have hw := hweak (fun p => star (Ψ p)) hΨ.star (hcΨ.comp_left (by simp))
    ((tsupport_comp_subset (by simp) Ψ).trans hsΨ)
  simpa only [star_star, directional_star, partition_chart_vertical_derivative φ hφ hβ, Ψ] using hw

private theorem compact_bilinear_integrable {a : ℝ} {H Ψ : Plane → ℂ}
    (hH : LocallyIntegrableOn H {p : Plane | a < p.2} volume)
    (hΨ : Continuous Ψ) (hc : HasCompactSupport Ψ)
    (hs : tsupport Ψ ⊆ {p : Plane | a < p.2}) :
    Integrable (fun p => Ψ p * H p) := by
  have h := local_compact_test_product_integrable hH hΨ.star
    (hc.comp_left (by simp)) ((tsupport_comp_subset (by simp) Ψ).trans hs)
  simpa only [star_star] using h

/-- Actual local real-chart vertical weak differentiation implies the
integrated one-period vertical law for every smooth circle test. -/
theorem real_chart_vertical_one_period_tensor {a : ℝ} {F D : Plane → ℂ}
    (hF : LocallyIntegrableOn F {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hperiodF : ∀ y : ℝ, a < y → Function.Periodic (fun x => F (x, y)) 1)
    (hperiodD : ∀ y : ℝ, a < y → Function.Periodic (fun x => D (x, y)) 1)
    (hweak : HasRealChartVerticalWeakDerivative {p : Plane | a < p.2} F D)
    (φ : C(UnitAddCircle, ℂ))
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi a) :
    (∫ y : ℝ, ∫ x in (0 : ℝ)..1, (β y : ℂ) * φ (x : UnitAddCircle) * D (x, y)) =
      -(∫ y : ℝ, ∫ x in (0 : ℝ)..1, (deriv β y : ℂ) * φ (x : UnitAddCircle) * F (x, y)) := by
  have hβd : ContDiff ℝ ∞ (deriv β) := (contDiff_infty_iff_deriv.mp hβ).2
  have hsd : tsupport (deriv β) ⊆ Ioi a := tsupport_deriv_subset.trans hs
  have hiD : Integrable (fun p : Plane => periodicChartTensor horizontalUnitPartition φ β p * D p) :=
    compact_bilinear_integrable hD
      (periodicChartTensor_smooth horizontalUnitPartition_cinfty φ hφ hβ).continuous
      (periodicChartTensor_compact horizontalUnitPartition_compact φ hc)
      (periodicChartTensor_height_support φ hs)
  have hiF : Integrable (fun p : Plane => periodicChartTensor horizontalUnitPartition φ (deriv β) p * F p) :=
    compact_bilinear_integrable hF
      (periodicChartTensor_smooth horizontalUnitPartition_cinfty φ hφ hβd).continuous
      (periodicChartTensor_compact horizontalUnitPartition_compact φ hc.deriv)
      (periodicChartTensor_height_support φ hsd)
  have hDu := unfold_compact_chart_tensor horizontalUnitPartition 1
    horizontalUnitPartition_zero_left horizontalUnitPartition_zero_right
    (fun x hx => partition_two_terms hx) φ β hs D hperiodD hiD
  have hFu := unfold_compact_chart_tensor horizontalUnitPartition 1
    horizontalUnitPartition_zero_left horizontalUnitPartition_zero_right
    (fun x hx => partition_two_terms hx) φ (deriv β) hsd F hperiodF hiF
  have hw := local_vertical_partition_tensor hweak φ hφ hβ hc hs
  rw [hDu, hFu] at hw
  simpa only [Complex.ofReal_one, one_mul] using hw

end
end ImbalancedChen.Part3.PeriodicRealChartVerticalDescent20261026b
