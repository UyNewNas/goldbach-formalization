import ImbalancedChen.Part3CuspCylinderMeasure
import ImbalancedChen.Part3CuspHorizontalDerivativeParseval
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24; uncompiled.

The first import supplies the literal period-one cylinder measure
`haarAddCircle.prod heightMeasure`, with `heightMeasure = dy/y²` on positive
heights.  The second supplies the all-integer Fourier proof of the sharp
period-one Poincaré inequality.  This file integrates that inequality on an
actual cusp tail.  `D` is the physical horizontal derivative: in the
normalized circle coordinate `t=x/w`, the derivative is `w*D`.

The assumptions include continuity of both cylinder functions and finite
tail energies.  Continuity gives the slice integrability needed by Parseval;
the tail energy hypotheses give the Bochner integrability needed by Fubini.
There is no global quotient Laplacian or automorphic spectral assertion.
-/

noncomputable section

namespace P3CuspCylinderTailPoincareSourceOnly

open Set MeasureTheory
open ImbalancedChen.Part3.CuspCylinderMeasure20261024z
open P3CuspHorizontalDerivativeParsevalSourceOnly

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

def heightTail (Y : ℝ) : Set PositiveHeight :=
  {y | Y ≤ (y : ℝ)}

def cylinderTail (Y : ℝ) : Set CuspCylinder :=
  univ ×ˢ heightTail Y

theorem heightTail_measurable (Y : ℝ) : MeasurableSet (heightTail Y) := by
  exact (isClosed_Ici.preimage continuous_subtype_val).measurableSet

theorem cylinderTail_measurable (Y : ℝ) : MeasurableSet (cylinderTail Y) :=
  MeasurableSet.univ.prod (heightTail_measurable Y)

private theorem cylinderTail_measure (Y : ℝ) :
    (AddCircle.haarAddCircle (T := (1 : ℝ))).prod
      (heightMeasure.restrict (heightTail Y)) =
        cylinderMeasure.restrict (cylinderTail Y) := by
  simpa only [Measure.restrict_univ, cylinderMeasure, cylinderTail] using
    (Measure.prod_restrict (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
      (ν := heightMeasure) univ (heightTail Y))

private theorem rawCylinderTail_measure (Y : ℝ) :
    (AddCircle.haarAddCircle (T := (1 : ℝ))).prod
      ((volume : Measure PositiveHeight).restrict (heightTail Y)) =
        ((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
          (volume : Measure PositiveHeight)).restrict (cylinderTail Y) := by
  simpa only [Measure.restrict_univ, cylinderTail] using
    (Measure.prod_restrict (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
      (ν := (volume : Measure PositiveHeight)) univ (heightTail Y))

private theorem restricted_height_density (Y : ℝ) :
    heightMeasure.restrict (heightTail Y) =
      ((volume : Measure PositiveHeight).restrict (heightTail Y)).withDensity
        (fun y => (heightDensity y : ℝ≥0∞)) := by
  exact restrict_withDensity (μ := (volume : Measure PositiveHeight))
    (heightTail_measurable Y) _

/-- Circle Haar energy equals the real-coordinate energy over one period.
This uses the actual AddCircle preimage formula and the nullity of endpoints. -/
private theorem circle_energy_eq_interval (u : UnitAddCircle → ℂ) :
    (∫ x : UnitAddCircle, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ t in (0 : ℝ)..1, ‖u (t : UnitAddCircle)‖ ^ 2 := by
  calc
    (∫ x : UnitAddCircle, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle) =
        ∫ t in Ico (0 : ℝ) 1, ‖u (t : UnitAddCircle)‖ ^ 2 :=
      circle_integral_eq_Ico _
    _ = ∫ t in Ioc (0 : ℝ) 1, ‖u (t : UnitAddCircle)‖ ^ 2 :=
      integral_Ico_eq_integral_Ioc
    _ = ∫ t in (0 : ℝ)..1, ‖u (t : UnitAddCircle)‖ ^ 2 :=
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

/-- For each tail height, the actual Fourier theorem gives the sharp slice
bound in the normalized chart.  The physical derivative has the width factor
`w`, so the constant is `w²/(4π²)`. -/
private theorem horizontal_slice_poincare
    (w Y : ℝ) (hw : 0 < w) (F D : CuspCylinder → ℂ)
    (hFcont : Continuous F) (hDcont : Continuous D)
    (hderiv : ∀ y : PositiveHeight, Y ≤ (y : ℝ) →
      ∀ t ∈ [[(0 : ℝ), 1]],
        HasDerivAt (fun s : ℝ => F ((s : UnitAddCircle), y))
          ((w : ℂ) * D ((t : UnitAddCircle), y)) t)
    (hzero : ∀ y : PositiveHeight, Y ≤ (y : ℝ) →
      (∫ x : UnitAddCircle, F (x, y) ∂AddCircle.haarAddCircle) = 0)
    (y : PositiveHeight) (hy : Y ≤ (y : ℝ)) :
    (4 * Real.pi ^ 2) *
        (∫ x : UnitAddCircle, ‖F (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle) ≤
      w ^ 2 *
        (∫ x : UnitAddCircle, ‖D (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  let f : ℝ → ℂ := fun t => F ((t : UnitAddCircle), y)
  let g : ℝ → ℂ := fun t => (w : ℂ) * D ((t : UnitAddCircle), y)
  have hfcont : Continuous f := by fun_prop
  have hgcont : Continuous g := by fun_prop
  have hint : IntervalIntegrable g volume 0 1 := hgcont.intervalIntegrable 0 1
  have hfL2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm
      hfcont.measurable.aestronglyMeasurable).2
      (hfcont.norm.pow 2).integrableOn_Ioc
  have hgL2 : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm
      hgcont.measurable.aestronglyMeasurable).2
      (hgcont.norm.pow 2).integrableOn_Ioc
  have hperiod : f 1 = f 0 := by
    change F (((1 : ℝ) : UnitAddCircle), y) =
      F (((0 : ℝ) : UnitAddCircle), y)
    congr 1
    simpa using (AddCircle.coe_add_period (1 : ℝ) (0 : ℝ))
  have hmean : (∫ t in (0 : ℝ)..1, f t) = 0 := by
    change (∫ t in (0 : ℝ)..1, F ((t : UnitAddCircle), y)) = 0
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hzvol : (∫ x : UnitAddCircle, F (x, y)) = 0 := by
      simpa only [circleHaar_eq_volume] using hzero y hy
    simpa only [zero_add] using
      (AddCircle.integral_preimage 1 0 (fun x : UnitAddCircle => F (x, y))).trans
        hzvol
  have hs := period_one_poincare f g (hderiv y hy) hperiod hint hfL2 hgL2 hmean
  have hFcircle := circle_energy_eq_interval (fun x => F (x, y))
  have hDcircle := circle_energy_eq_interval (fun x => D (x, y))
  have hgenergy : (∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2) =
      w ^ 2 * (∫ x : UnitAddCircle, ‖D (x, y)‖ ^ 2
        ∂AddCircle.haarAddCircle) := by
    have hpoint (t : ℝ) : ‖g t‖ ^ 2 =
        w ^ 2 * ‖D ((t : UnitAddCircle), y)‖ ^ 2 := by
      simp [g, norm_mul, Complex.norm_ofReal, abs_of_pos hw] <;> ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul]
    rw [hDcircle]
  rw [← hFcircle, hgenergy] at hs
  exact hs

/-- Actual cylinder tail (L²) control from horizontal differentiation.
The left measure is precisely `dx dy/y²` in the normalized cusp chart; the
right measure is `dx dy`.  Finite energy is required only on the tail. -/
theorem cylinder_tail_l2_control
    (w Y : ℝ) (hw : 0 < w) (hY : 0 < Y)
    (F D : CuspCylinder → ℂ)
    (hFcont : Continuous F) (hDcont : Continuous D)
    (hderiv : ∀ y : PositiveHeight, Y ≤ (y : ℝ) →
      ∀ t ∈ [[(0 : ℝ), 1]],
        HasDerivAt (fun s : ℝ => F ((s : UnitAddCircle), y))
          ((w : ℂ) * D ((t : UnitAddCircle), y)) t)
    (hzero : ∀ y : PositiveHeight, Y ≤ (y : ℝ) →
      (∫ x : UnitAddCircle, F (x, y) ∂AddCircle.haarAddCircle) = 0)
    (hFtail : Integrable (fun z : CuspCylinder => ‖F z‖ ^ 2)
      (cylinderMeasure.restrict (cylinderTail Y)))
    (hDtail : Integrable (fun z : CuspCylinder => ‖D z‖ ^ 2)
      (((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
        (volume : Measure PositiveHeight)).restrict (cylinderTail Y))) :
    (∫ z in cylinderTail Y, ‖F z‖ ^ 2 ∂cylinderMeasure) ≤
      (w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) *
        (∫ z in cylinderTail Y, ‖D z‖ ^ 2
          ∂((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
            (volume : Measure PositiveHeight))) := by
  let A : PositiveHeight → ℝ := fun y =>
    ∫ x : UnitAddCircle, ‖F (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle
  let B : PositiveHeight → ℝ := fun y =>
    ∫ x : UnitAddCircle, ‖D (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle
  let C : ℝ := w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)
  have hFprod : Integrable (fun z : CuspCylinder => ‖F z‖ ^ 2)
      ((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
        (heightMeasure.restrict (heightTail Y))) := by
    rw [cylinderTail_measure]
    exact hFtail
  have hDprod : Integrable (fun z : CuspCylinder => ‖D z‖ ^ 2)
      ((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
        ((volume : Measure PositiveHeight).restrict (heightTail Y))) := by
    rw [rawCylinderTail_measure]
    exact hDtail
  have hAint : Integrable A (heightMeasure.restrict (heightTail Y)) :=
    hFprod.integral_prod_right
  have hBint : Integrable B ((volume : Measure PositiveHeight).restrict
      (heightTail Y)) := hDprod.integral_prod_right
  have hweighted : Integrable (fun y : PositiveHeight =>
      (heightDensity y : ℝ) * A y)
      ((volume : Measure PositiveHeight).restrict (heightTail Y)) := by
    have hA' : Integrable A
        (((volume : Measure PositiveHeight).restrict (heightTail Y)).withDensity
          (fun y => (heightDensity y : ℝ≥0∞))) := by
      rwa [← restricted_height_density]
    simpa only [NNReal.smul_def, smul_eq_mul] using
      ((integrable_withDensity_iff_integrable_smul
        heightDensity_continuous.measurable).1 hA')
  have hA_nonneg (y : PositiveHeight) : 0 ≤ A y := by
    exact integral_nonneg (fun x => sq_nonneg (‖F (x, y)‖))
  have hpoint (y : PositiveHeight) (hy : y ∈ heightTail Y) :
      (heightDensity y : ℝ) * A y ≤ C * B y := by
    have hy' : Y ≤ (y : ℝ) := hy
    have hslice := horizontal_slice_poincare w Y hw F D hFcont hDcont
      hderiv hzero y hy'
    have hrec : 1 / (y : ℝ) ≤ 1 / Y :=
      one_div_le_one_div_of_le hY hy'
    have hdensity : (heightDensity y : ℝ) ≤ (1 / Y) ^ 2 := by
      rw [heightDensity_coe]
      exact (sq_le_sq₀ (by positivity) (by positivity)).2 hrec
    have hcpos : 0 < 4 * Real.pi ^ 2 * Y ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hslice
      (show 0 ≤ (4 * Real.pi ^ 2 * Y ^ 2)⁻¹ by positivity)
    calc
      (heightDensity y : ℝ) * A y ≤ (1 / Y) ^ 2 * A y :=
        mul_le_mul_of_nonneg_right hdensity (hA_nonneg y)
      _ = (4 * Real.pi ^ 2 * Y ^ 2)⁻¹ *
            ((4 * Real.pi ^ 2) * A y) := by
          field_simp [ne_of_gt hcpos, ne_of_gt hY]
          ring
      _ ≤ (4 * Real.pi ^ 2 * Y ^ 2)⁻¹ *
            (w ^ 2 * B y) := hmul
      _ = C * B y := by simp only [C, div_eq_mul_inv]; ring
  have hAE : ∀ᵐ y : PositiveHeight ∂((volume : Measure PositiveHeight).restrict
      (heightTail Y)), (heightDensity y : ℝ) * A y ≤ C * B y :=
    (ae_restrict_mem (heightTail_measurable Y)).mono hpoint
  have hle : (∫ y : PositiveHeight, (heightDensity y : ℝ) * A y
      ∂(volume : Measure PositiveHeight).restrict (heightTail Y)) ≤
      ∫ y : PositiveHeight, C * B y
        ∂(volume : Measure PositiveHeight).restrict (heightTail Y) :=
    integral_mono_ae hweighted (hBint.const_mul C) hAE
  have hFfub :
      (∫ z in cylinderTail Y, ‖F z‖ ^ 2 ∂cylinderMeasure) =
        ∫ y : PositiveHeight, A y ∂heightMeasure.restrict (heightTail Y) := by
    rw [← cylinderTail_measure]
    exact integral_prod_symm _ hFprod
  have hDfub :
      (∫ z in cylinderTail Y, ‖D z‖ ^ 2
          ∂((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
            (volume : Measure PositiveHeight))) =
        ∫ y : PositiveHeight, B y
          ∂(volume : Measure PositiveHeight).restrict (heightTail Y) := by
    rw [← rawCylinderTail_measure]
    exact integral_prod_symm _ hDprod
  calc
    (∫ z in cylinderTail Y, ‖F z‖ ^ 2 ∂cylinderMeasure) =
        ∫ y : PositiveHeight, A y ∂heightMeasure.restrict (heightTail Y) := hFfub
    _ = ∫ y : PositiveHeight, (heightDensity y : ℝ) * A y
          ∂(volume : Measure PositiveHeight).restrict (heightTail Y) := by
      rw [restricted_height_density]
      simpa only [NNReal.smul_def, smul_eq_mul] using
        (integral_withDensity_eq_integral_smul
          heightDensity_continuous.measurable A)
    _ ≤ ∫ y : PositiveHeight, C * B y
          ∂(volume : Measure PositiveHeight).restrict (heightTail Y) := hle
    _ = C * ∫ y : PositiveHeight, B y
          ∂(volume : Measure PositiveHeight).restrict (heightTail Y) := by
      rw [integral_const_mul]
    _ = (w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) *
          (∫ z in cylinderTail Y, ‖D z‖ ^ 2
            ∂((AddCircle.haarAddCircle (T := (1 : ℝ))).prod
              (volume : Measure PositiveHeight))) := by
      rw [hDfub]
      rfl

end P3CuspCylinderTailPoincareSourceOnly
