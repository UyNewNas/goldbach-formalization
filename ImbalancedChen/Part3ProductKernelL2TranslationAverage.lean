import ImbalancedChen.Part3CompactC2ProductMollifier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual normalized product kernel defines a genuine Bochner average
of translated native L2 classes. These averages are contractions and
converge strongly to every L2 vector, using native strong continuity of
translation. No convergence or uniform continuity of an L2 representative
is assumed. Identification of this native L2 integral with the pointwise
scalar convolution is a separate Fubini/representative bridge, not asserted
here. In particular this alone does not close finite-tensor H1 density.
-/

namespace ImbalancedChen.Part3.ProductKernelL2TranslationAverage20261026a
noncomputable section
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
open CompactC2ProductMollifier20261026a

abbrev PlaneL2 := Lp ℂ 2 (volume : Measure Plane)

def translation (f : PlaneL2) (t : Plane) : PlaneL2 := DomAddAct.mk t +ᵥ f

theorem translation_continuous (f : PlaneL2) : Continuous (translation f) :=
  DomAddAct.continuous_mk.vadd continuous_const

@[simp] theorem translation_zero (f : PlaneL2) : translation f 0 = f := by
  simp [translation]

@[simp] theorem translation_norm (f : PlaneL2) (t : Plane) :
    ‖translation f t‖ = ‖f‖ := DomAddAct.norm_vadd_Lp _ _

/-- Native L2 convolution with the actual positive normalized product
kernel. The output is an actual Bochner integral in the complete L2 space. -/
def productAverage (r : ℝ) (hr : 0 < r) (f : PlaneL2) : PlaneL2 :=
  (realProductKernel r hr ⋆[lsmul ℝ ℝ, volume] translation f) 0

theorem productAverage_integral (r : ℝ) (hr : 0 < r) (f : PlaneL2) :
    productAverage r hr f =
      ∫ t : Plane, realProductKernel r hr t • translation f (-t) := by
  simp only [productAverage, convolution_def, lsmul_apply, zero_sub]

theorem productAverage_integrable (r : ℝ) (hr : 0 < r) (f : PlaneL2) :
    Integrable (fun t : Plane => realProductKernel r hr t • translation f (-t)) volume := by
  exact ((translation_continuous f).comp continuous_neg).locallyIntegrable
    .integrable_smul_left_of_hasCompactSupport
      (realProductKernel_continuous r hr) (realProductKernel_compact r hr)

theorem productAverage_norm_le (r : ℝ) (hr : 0 < r) (f : PlaneL2) :
    ‖productAverage r hr f‖ ≤ ‖f‖ := by
  have h := dist_convolution_le (norm_nonneg f) (realProductKernel_support r hr)
    (realProductKernel_nonneg r hr) (realProductKernel_integral r hr)
    (translation_continuous f).aestronglyMeasurable
    (x₀ := (0 : Plane)) (z₀ := (0 : PlaneL2))
    (fun t _ => by simp)
  simpa only [productAverage, dist_zero_right] using h

def radius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  positivity

theorem radius_tendsto : Tendsto radius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Strong L2 approximate-identity theorem with no smoothness or support
assumption on f. The normalized product kernel is the actual supplier. -/
theorem productAverage_tendsto (f : PlaneL2) :
    Tendsto (fun n => productAverage (radius n) (radius_pos n) f) atTop (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp
    (show ContinuousAt (translation f) (0 : Plane) from
      (translation_continuous f).continuousAt) (ε / 2) (half_pos hε)
  have hr : ∀ᶠ n in atTop, radius n < δ :=
    radius_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [hr] with n hn
  have hb := dist_convolution_le (half_pos hε).le
    (realProductKernel_support (radius n) (radius_pos n))
    (realProductKernel_nonneg (radius n) (radius_pos n))
    (realProductKernel_integral (radius n) (radius_pos n))
    (translation_continuous f).aestronglyMeasurable
    (x₀ := (0 : Plane)) (z₀ := f) (fun t ht => by
      have hm := hmod ((Metric.mem_ball.mp ht).trans hn)
      simpa only [translation_zero] using hm.le)
  exact hb.trans_lt (half_lt_self hε)

end
end ImbalancedChen.Part3.ProductKernelL2TranslationAverage20261026a
