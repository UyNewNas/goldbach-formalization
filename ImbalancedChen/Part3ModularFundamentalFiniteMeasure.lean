import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import ImbalancedChen.Part3UpperHalfPlaneHyperbolicMeasure

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.
The set here is exactly mathlib's classical closed `ModularGroup.fd`, and
the measure is exactly its invariant `UpperHalfPlane.volume`. The finite
cusp volume proof uses `y > 1/2`, a width-one strip, and the genuine
integrability of `y ^ (-2)` above `1/2`. This is only a finite-measure
fundamental carrier; the full-plane `Lp` unitary action does not identify
an automorphic quotient Hilbert space or yield a spectral decomposition.
-/

namespace ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane

/-- The actual classical closed modular fundamental domain. -/
def modularFD : Set UpperHalfPlane := ModularGroup.fd

/-- The measurable width-one upper strip in complex coordinates. -/
private def cuspRect : Set (ℝ × ℝ) :=
  Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×ˢ Ioi (1 / 2 : ℝ)

private def cuspStrip : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' cuspRect

theorem modularFD_isClosed : IsClosed modularFD := by
  exact ModularGroup.isClosed_fd

theorem modularFD_measurable : MeasurableSet modularFD :=
  modularFD_isClosed.measurableSet

/-- The real-coordinate bound is supplied by the actual domain definition. -/
theorem modularFD_real_bound {z : UpperHalfPlane} (hz : z ∈ modularFD) :
    |z.re| ≤ (1 : ℝ) / 2 := hz.2

/-- The standard geometric inequality from mathlib's modular domain API. -/
theorem modularFD_three_le_four_im_sq {z : UpperHalfPlane} (hz : z ∈ modularFD) :
    3 ≤ 4 * z.im ^ 2 :=
  ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz

/-- A convenient strict positive-height bound for the cusp-volume integral. -/
theorem modularFD_half_lt_im {z : UpperHalfPlane} (hz : z ∈ modularFD) :
    (1 : ℝ) / 2 < z.im := by
  have hthree := modularFD_three_le_four_im_sq hz
  have him := z.im_pos
  by_contra h
  have hle : z.im ≤ (1 : ℝ) / 2 := le_of_not_gt h
  have hprod : 0 ≤ ((1 : ℝ) / 2 - z.im) * ((1 : ℝ) / 2 + z.im) :=
    mul_nonneg (sub_nonneg.mpr hle) (by linarith)
  nlinarith

private theorem modularFD_coe_subset_cuspStrip :
    (UpperHalfPlane.coe '' modularFD) ⊆ cuspStrip := by
  rintro w ⟨z, hz, rfl⟩
  change (z.re, z.im) ∈ cuspRect
  refine ⟨?_, modularFD_half_lt_im hz⟩
  exact abs_le.mp (modularFD_real_bound hz)

/-- `y ^ (-2)` is integrable on the genuine unbounded width-one strip. -/
private theorem cuspStrip_integrable :
    IntegrableOn (fun z : ℂ => z.im ^ (-2 : ℝ)) cuspStrip volume := by
  have hx : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))) := by
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hy : Integrable (fun y : ℝ => y ^ (-2 : ℝ))
      (volume.restrict (Ioi (1 / 2 : ℝ))) := by
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hrect : IntegrableOn (fun p : ℝ × ℝ => p.2 ^ (-2 : ℝ))
      cuspRect (volume : Measure (ℝ × ℝ)) := by
    change Integrable (fun p : ℝ × ℝ => p.2 ^ (-2 : ℝ))
      ((volume : Measure (ℝ × ℝ)).restrict
        (Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×ˢ Ioi (1 / 2 : ℝ)))
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa only [one_mul] using hx.mul_prod hy
  change IntegrableOn
    ((fun p : ℝ × ℝ => p.2 ^ (-2 : ℝ)) ∘ Complex.measurableEquivRealProd)
    (Complex.measurableEquivRealProd ⁻¹' cuspRect) volume
  exact (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.measurableEmbedding).2 hrect

private theorem modularFD_coe_integrable :
    IntegrableOn (fun z : ℂ => z.im ^ (-2 : ℝ))
      (UpperHalfPlane.coe '' modularFD) volume :=
  cuspStrip_integrable.mono_set modularFD_coe_subset_cuspStrip

private theorem density_eq_ofReal_rpow {w : ℂ}
    (hw : w ∈ UpperHalfPlane.coe '' modularFD) :
    (↑((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (w.im ^ (-2 : ℝ)) := by
  rw [modularFD, ModularGroup.coe_fd] at hw
  obtain ⟨him, -, -⟩ := hw
  have hrpow : w.im ^ (-2 : ℝ) = (1 / w.im) ^ 2 := by
    rw [show (-2 : ℝ) = (-1 : ℝ) * 2 by norm_num,
      Real.rpow_mul him.le, Real.rpow_natCast, Real.rpow_neg_one]
    simp only [one_div]
  rw [hrpow, ENNReal.ofReal_eq_coe_nnreal (sq_nonneg (1 / w.im))]
  congr 1
  apply Subtype.ext
  simp [Real.nnnorm_of_nonneg him.le, NNReal.coe_div, NNReal.coe_pow]

/-- Finite hyperbolic volume of mathlib's actual classical modular domain. -/
theorem modularFD_finite :
    (volume : Measure UpperHalfPlane) modularFD < ∞ := by
  calc
    (volume : Measure UpperHalfPlane) modularFD =
        ∫⁻ w : ℂ in UpperHalfPlane.coe '' modularFD,
          (↑((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
      UpperHalfPlane.volume_eq_lintegral modularFD
    _ = ∫⁻ w : ℂ in UpperHalfPlane.coe '' modularFD,
          ENNReal.ofReal (w.im ^ (-2 : ℝ)) := by
      apply setLIntegral_congr_fun ModularGroup.isClosed_coe_fd.measurableSet
      intro w hw
      exact density_eq_ofReal_rpow hw
    _ < ∞ := modularFD_coe_integrable.setLIntegral_lt_top

/-- The open classical cell has positive mass and lies in the closed cell. -/
theorem modularFD_pos :
    0 < (volume : Measure UpperHalfPlane) modularFD := by
  letI : Measure.IsOpenPosMeasure
      ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z.coordinateMeasure := by
    exact Measure.IsOpenPosMeasure.comap (volume : Measure ℂ)
      UpperHalfPlane.isOpenEmbedding_coe
  letI : Measure.IsOpenPosMeasure (volume : Measure UpperHalfPlane) := by
    exact ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z.
      coordinateMeasure_absolutelyContinuous_hyperbolic.isOpenPosMeasure
  have hnonempty : (ModularGroup.fdo : Set UpperHalfPlane).Nonempty := by
    refine ⟨⟨⟨0, 2⟩, by norm_num⟩, ?_⟩
    constructor <;> norm_num [ModularGroup.fdo, Complex.normSq_apply]
  have hpositive : 0 < (volume : Measure UpperHalfPlane) ModularGroup.fdo :=
    ModularGroup.isOpen_fdo.measure_pos volume hnonempty
  exact lt_of_lt_of_le hpositive (measure_mono ModularGroup.fdo_subset_fd)

end
end ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
