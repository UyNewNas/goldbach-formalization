import ImbalancedChen.Part3ActualCylinderModeEmbeddings
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual native cylinder Fourier coefficients. The literal slice integrals
are proved to belong to height L2 by actual circle Parseval and Bochner
Fubini. They are then identified with the adjoints of the actual mode
embeddings. Vanishing of all these native coefficients forces the actual
cylinder L2 vector to vanish. No unknown Fourier transform is assumed.
-/

namespace ImbalancedChen.Part3.ActualCylinderFourierCoefficients20261026a
noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z ActualCylinderModeEmbeddings20261026a

def sliceCoefficient (n : ℤ) (F : CylinderL2) (y : PositiveHeight) : ℂ :=
  AddCircle.fourierCoeff (fun x : UnitAddCircle => F (x, y)) n

theorem sliceCoefficient_measurable (n : ℤ) (F : CylinderL2) :
    Measurable (sliceCoefficient n F) := by
  have hweighted : StronglyMeasurable (fun z : CuspCylinder =>
      AddCircle.fourier (-n) z.1 * F z) :=
    ((AddCircle.fourier (-n)).continuous.comp continuous_fst).stronglyMeasurable.mul
      (Lp.stronglyMeasurable F)
  exact hweighted.integral_prod_left'.measurable

theorem cylinder_sq_integrable (F : CylinderL2) :
    Integrable (fun z => ‖F z‖ ^ 2) cylinderMeasure :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)

theorem cylinder_slice_memLp (F : CylinderL2) :
    ∀ᵐ y ∂heightMeasure,
      MemLp (fun x : UnitAddCircle => F (x, y)) 2 AddCircle.haarAddCircle := by
  filter_upwards [(cylinder_sq_integrable F).prod_right_ae] with y hy
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable F).comp_measurable measurable_prodMk_right).aestronglyMeasurable).mpr hy

/-- Actual circle Parseval bounds each coefficient on every L2 slice. -/
theorem sliceCoefficient_energy_le (n : ℤ) (F : CylinderL2) :
    ∀ᵐ y ∂heightMeasure, ‖sliceCoefficient n F y‖ ^ 2 ≤
      ∫ x : UnitAddCircle, ‖F (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle := by
  filter_upwards [cylinder_slice_memLp F] with y hy
  let fy : UnitAddCircle → ℂ := fun x => F (x, y)
  have hcoeff (m : ℤ) :
      AddCircle.fourierCoeff (hy.toLp fy) m = sliceCoefficient m F y :=
    congrFun (AddCircle.fourierCoeff_congr_ae hy.coeFn_toLp) m
  have hi : (∫ x : UnitAddCircle, ‖(hy.toLp fy) x‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, ‖F (x, y)‖ ^ 2 ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hy.coeFn_toLp] with x hx
    rw [hx]
  have hparse := AddCircle.hasSum_sq_fourierCoeff (hy.toLp fy)
  have hb := hparse.summable.le_tsum n (fun m _ => sq_nonneg
    (‖AddCircle.fourierCoeff (hy.toLp fy) m‖))
  rwa [hparse.tsum_eq, hcoeff, hi] at hb

theorem sliceCoefficient_memLp (n : ℤ) (F : CylinderL2) :
    MemLp (sliceCoefficient n F) 2 heightMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (sliceCoefficient_measurable n F).aestronglyMeasurable).mpr
  apply (cylinder_sq_integrable F).integral_prod_right.mono'
    (((sliceCoefficient_measurable n F).norm.pow_const 2).aestronglyMeasurable)
  filter_upwards [sliceCoefficient_energy_le n F] with y hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using hy

def literalCoefficientL2 (n : ℤ) (F : CylinderL2) : HeightL2 :=
  (sliceCoefficient_memLp n F).toLp (sliceCoefficient n F)

theorem literalCoefficientL2_ae (n : ℤ) (F : CylinderL2) :
    (literalCoefficientL2 n F : PositiveHeight → ℂ) =ᵐ[heightMeasure]
      sliceCoefficient n F := (sliceCoefficient_memLp n F).coeFn_toLp

/-- The exact Bochner Fubini pairing needed for the native adjoint. -/
theorem mode_inner_eq_literalCoefficient (n : ℤ) (g : HeightL2) (F : CylinderL2) :
    inner ℂ (modeEmbedding n g) F = inner ℂ g (literalCoefficientL2 n F) := by
  have hpoint : (fun z : CuspCylinder => inner ℂ (modeEmbedding n g z) (F z))
      =ᵐ[cylinderMeasure] (fun z => star (g z.2) *
        (AddCircle.fourier (-n) z.1 * F z)) := by
    filter_upwards [modeEmbedding_ae n g] with z hz
    rw [hz]
    simp only [RCLike.inner_apply', map_mul, Complex.star_def, AddCircle.fourier_neg]
    ring
  have hi : Integrable (fun z : CuspCylinder => star (g z.2) *
      (AddCircle.fourier (-n) z.1 * F z)) cylinderMeasure :=
    (L2.integrable_inner (modeEmbedding n g) F).congr hpoint
  calc
    inner ℂ (modeEmbedding n g) F =
        ∫ z : CuspCylinder, star (g z.2) *
          (AddCircle.fourier (-n) z.1 * F z) ∂cylinderMeasure :=
      integral_congr_ae hpoint
    _ = ∫ y : PositiveHeight, ∫ x : UnitAddCircle,
          star (g y) * (AddCircle.fourier (-n) x * F (x, y))
          ∂AddCircle.haarAddCircle ∂heightMeasure := integral_prod_symm _ hi
    _ = ∫ y : PositiveHeight, star (g y) * sliceCoefficient n F y ∂heightMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by
        rw [integral_const_mul]
        rfl)
    _ = inner ℂ g (literalCoefficientL2 n F) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [literalCoefficientL2_ae n F] with y hy
      rw [hy]
      rfl

def cylinderCoefficient (n : ℤ) : CylinderL2 →L[ℂ] HeightL2 :=
  (modeEmbedding n).toContinuousLinearMap.adjoint

theorem cylinderCoefficient_eq_literal (n : ℤ) (F : CylinderL2) :
    cylinderCoefficient n F = literalCoefficientL2 n F := by
  apply ext_inner_left ℂ
  intro g
  rw [cylinderCoefficient, ContinuousLinearMap.adjoint_inner_right]
  exact mode_inner_eq_literalCoefficient n g F

theorem cylinderCoefficient_ae (n : ℤ) (F : CylinderL2) :
    (cylinderCoefficient n F : PositiveHeight → ℂ) =ᵐ[heightMeasure]
      sliceCoefficient n F := by
  rw [cylinderCoefficient_eq_literal]
  exact literalCoefficientL2_ae n F

theorem cylinderCoefficient_inner (n : ℤ) (g : HeightL2) (F : CylinderL2) :
    inner ℂ g (cylinderCoefficient n F) = inner ℂ (modeEmbedding n g) F :=
  (modeEmbedding n).toContinuousLinearMap.adjoint_inner_right g F

theorem cylinderCoefficient_mode (n m : ℤ) (g : HeightL2) :
    cylinderCoefficient n (modeEmbedding m g) = if n = m then g else 0 := by
  apply ext_inner_left ℂ
  intro h
  rw [cylinderCoefficient_inner, modeEmbedding_inner]
  split_ifs <;> simp

/-- All native coefficients determine the actual cylinder L2 element.
The countable intersection of AE identities is essential here. -/
theorem eq_zero_of_all_coefficients_zero (F : CylinderL2)
    (hF : ∀ n : ℤ, cylinderCoefficient n F = 0) : F = 0 := by
  have hzero (n : ℤ) : ∀ᵐ y ∂heightMeasure, sliceCoefficient n F y = 0 := by
    have hn := (cylinderCoefficient_ae n F).symm
    rw [hF n] at hn
    exact hn.trans (Lp.coeFn_zero ℂ 2 heightMeasure)
  have hall : ∀ᵐ y ∂heightMeasure, ∀ n : ℤ, sliceCoefficient n F y = 0 :=
    ae_all_iff.mpr hzero
  have hslice : ∀ᵐ y ∂heightMeasure,
      ∀ᵐ x ∂(AddCircle.haarAddCircle (T := (1 : ℝ))), F (x, y) = 0 := by
    filter_upwards [cylinder_slice_memLp F, hall] with y hy hz
    let fy : UnitAddCircle → ℂ := fun x => F (x, y)
    have hzLp : hy.toLp fy = 0 := by
      apply (AddCircle.fourierBasis (T := (1 : ℝ))).repr.injective
      ext n
      rw [map_zero]
      change (AddCircle.fourierBasis (T := (1 : ℝ))).repr (hy.toLp fy) n = 0
      rw [AddCircle.fourierBasis_repr]
      exact (congrFun (AddCircle.fourierCoeff_congr_ae hy.coeFn_toLp) n).trans (hz n)
    have h := hy.coeFn_toLp.symm
    rw [hzLp] at h
    exact h.trans (Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle)
  have hm : MeasurableSet {z : CuspCylinder | F z = 0} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable F).measurable measurable_const
  have hae : (F : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] 0 :=
    (ae_prod_iff_ae_ae hm).mpr ((ae_ae_comm hm).mpr hslice)
  apply Lp.ext
  exact hae.trans (Lp.coeFn_zero ℂ 2 cylinderMeasure).symm

end
end ImbalancedChen.Part3.ActualCylinderFourierCoefficients20261026a
