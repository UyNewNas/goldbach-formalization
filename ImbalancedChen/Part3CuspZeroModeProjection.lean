import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24; uncompiled.

The horizontal cuspidal condition here is exactly the zero-mean condition
on the genuine Haar L² circle. The zero Fourier mode is removed by the
orthogonal projection onto the complement of the constant Hilbert-basis
vector. No Maass/Eisenstein decomposition is assumed.
-/

noncomputable section

namespace P3CuspZeroModeProjectionSourceOnly

open Set MeasureTheory
open scoped ENNReal NNReal

local instance periodOne_pos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

abbrev CircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

private def B : HilbertBasis ℤ ℂ CircleL2 :=
  AddCircle.fourierBasis (T := (1 : ℝ))

/-- Closed orthogonal complement of the constant Fourier mode. -/
def zeroModeSubspace : Submodule ℂ CircleL2 := (ℂ ∙ B 0)ᗮ

theorem zeroModeSubspace_closed : IsClosed (zeroModeSubspace : Set CircleL2) := by
  exact Submodule.isClosed_orthogonal _

def projectZero : CircleL2 →L[ℂ] CircleL2 :=
  zeroModeSubspace.starProjection

def removeZero (f : CircleL2) : CircleL2 :=
  f - (B.repr f 0) • B 0

private theorem removeZero_repr (f : CircleL2) :
    B.repr (removeZero f) =
      B.repr f - (B.repr f 0) • lp.single 2 0 (1 : ℂ) := by
  simp only [removeZero, map_sub, map_smul, HilbertBasis.repr_self]

theorem removeZero_repr_zero (f : CircleL2) : B.repr (removeZero f) 0 = 0 := by
  rw [removeZero_repr]
  simp [lp.single_apply, Pi.single_apply]

theorem removeZero_repr_ne_zero (f : CircleL2) (n : ℤ) (hn : n ≠ 0) :
    B.repr (removeZero f) n = B.repr f n := by
  rw [removeZero_repr]
  simp [lp.single_apply, Pi.single_apply, hn]

theorem zeroModeSubspace_iff (f : CircleL2) :
    f ∈ zeroModeSubspace ↔ AddCircle.fourierCoeff f 0 = 0 := by
  change f ∈ (ℂ ∙ B 0)ᗮ ↔ AddCircle.fourierCoeff f 0 = 0
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    ← HilbertBasis.repr_apply_apply, AddCircle.fourierBasis_repr]

private theorem removeZero_mem (f : CircleL2) :
    removeZero f ∈ zeroModeSubspace := by
  rw [zeroModeSubspace_iff]
  rw [← AddCircle.fourierBasis_repr]
  exact removeZero_repr_zero f

theorem projectZero_eq_removeZero (f : CircleL2) : projectZero f = removeZero f := by
  change zeroModeSubspace.starProjection f = removeZero f
  apply Submodule.eq_starProjection_of_mem_orthogonal (removeZero_mem f)
  have hspan : f - removeZero f ∈ (ℂ ∙ B 0) := by
    simpa [removeZero] using
      ((ℂ ∙ B 0).smul_mem (B.repr f 0) (Submodule.mem_span_singleton_self (B 0)))
  exact (Submodule.le_orthogonal_orthogonal (ℂ ∙ B 0)) hspan

theorem projectZero_norm_le (f : CircleL2) : ‖projectZero f‖ ≤ ‖f‖ := by
  exact zeroModeSubspace.norm_starProjection_apply_le f

theorem projectZero_mem (f : CircleL2) : projectZero f ∈ zeroModeSubspace := by
  exact zeroModeSubspace.starProjection_apply_mem f

theorem projectZero_coefficient_zero (f : CircleL2) :
    AddCircle.fourierCoeff (projectZero f) 0 = 0 := by
  exact (zeroModeSubspace_iff _).1 (projectZero_mem f)

theorem projectZero_coefficient_ne_zero (f : CircleL2) (n : ℤ) (hn : n ≠ 0) :
    AddCircle.fourierCoeff (projectZero f) n = AddCircle.fourierCoeff f n := by
  rw [projectZero_eq_removeZero, ← AddCircle.fourierBasis_repr,
    ← AddCircle.fourierBasis_repr]
  exact removeZero_repr_ne_zero f n hn

/-- Infinite Parseval after *exactly* deleting the constant coordinate. -/
theorem projectZero_parseval (f : CircleL2) :
    (∑' n : ℤ, if n = 0 then (0 : ℝ)
      else ‖AddCircle.fourierCoeff f n‖ ^ 2) =
      ∫ x : UnitAddCircle, ‖(projectZero f) x‖ ^ 2
        ∂AddCircle.haarAddCircle := by
  have hterms : (fun n : ℤ => if n = 0 then (0 : ℝ)
        else ‖AddCircle.fourierCoeff f n‖ ^ 2) =
      fun n : ℤ => ‖AddCircle.fourierCoeff (projectZero f) n‖ ^ 2 := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [projectZero_coefficient_zero]
    · simp only [if_neg hn, projectZero_coefficient_ne_zero f n hn]
  rw [hterms]
  exact AddCircle.tsum_sq_fourierCoeff (projectZero f)

/- The following literal measure definitions match the independent
   Part3CuspCylinderMeasure source-only file and are local until intake. -/
abbrev PositiveHeight := Ioi (0 : ℝ)
abbrev CuspCylinder := UnitAddCircle × PositiveHeight

def heightDensity (y : PositiveHeight) : ℝ≥0 :=
  (1 / NNReal.mk (y : ℝ) y.property.le) ^ 2

def heightMeasure : Measure PositiveHeight :=
  volume.withDensity (fun y => (heightDensity y : ℝ≥0∞))

def cylinderMeasure : Measure CuspCylinder :=
  (AddCircle.haarAddCircle (T := (1 : ℝ))).prod heightMeasure

local instance positiveHeight_locallyCompact : LocallyCompactSpace PositiveHeight :=
  isOpen_Ioi.locallyCompactSpace

local instance positiveHeightVolume_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) := by
  exact IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

local instance positiveHeightVolume_locallyFinite :
    IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance

local instance heightMeasure_sigmaFinite : SigmaFinite heightMeasure := by
  unfold heightMeasure
  infer_instance

/-- Almost every square-integrable cylinder slice with zero mean has its
entire horizontal L² energy in the nonzero Fourier modes. -/
theorem zeroMean_cylinder_slice_parseval (F : CuspCylinder → ℂ)
    (hF : Measurable F) (hL2 : MemLp F 2 cylinderMeasure)
    (hzero : ∀ᵐ y : PositiveHeight ∂heightMeasure,
      AddCircle.fourierCoeff (fun x : UnitAddCircle => F (x, y)) 0 = 0) :
    ∀ᵐ y : PositiveHeight ∂heightMeasure,
      (∑' n : ℤ, if n = 0 then (0 : ℝ)
        else ‖AddCircle.fourierCoeff
          (fun x : UnitAddCircle => F (x, y)) n‖ ^ 2) =
        ∫ x : UnitAddCircle, ‖F (x, y)‖ ^ 2
          ∂AddCircle.haarAddCircle := by
  have hsq : Integrable (fun p : CuspCylinder => ‖F p‖ ^ 2) cylinderMeasure :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hL2
  have hslice : ∀ᵐ y : PositiveHeight ∂heightMeasure,
      Integrable (fun x : UnitAddCircle => ‖F (x, y)‖ ^ 2)
        AddCircle.haarAddCircle := hsq.prod_right_ae
  filter_upwards [hslice, hzero] with y hy hz
  let fy : UnitAddCircle → ℂ := fun x => F (x, y)
  have hfy_meas : AEStronglyMeasurable fy AddCircle.haarAddCircle :=
    (hF.comp measurable_prodMk_right).aestronglyMeasurable
  have hfy_L2 : MemLp fy 2 AddCircle.haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm hfy_meas).2 hy
  have hcoeff (n : ℤ) :
      AddCircle.fourierCoeff (hfy_L2.toLp fy) n = AddCircle.fourierCoeff fy n := by
    exact congrFun (AddCircle.fourierCoeff_congr_ae hfy_L2.coeFn_toLp) n
  have hint :
      (∫ x : UnitAddCircle, ‖(hfy_L2.toLp fy) x‖ ^ 2
        ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, ‖fy x‖ ^ 2 ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hfy_L2.coeFn_toLp] with x hx
    rw [hx]
  have hparse :
      (∑' n : ℤ, ‖AddCircle.fourierCoeff fy n‖ ^ 2) =
        ∫ x : UnitAddCircle, ‖fy x‖ ^ 2 ∂AddCircle.haarAddCircle := by
    simpa only [hcoeff, hint] using
      (AddCircle.tsum_sq_fourierCoeff (hfy_L2.toLp fy))
  have hterms : (fun n : ℤ => if n = 0 then (0 : ℝ)
        else ‖AddCircle.fourierCoeff fy n‖ ^ 2) =
      (fun n : ℤ => ‖AddCircle.fourierCoeff fy n‖ ^ 2) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [hz]
    · simp [hn]
  rw [hterms]
  exact hparse

end P3CuspZeroModeProjectionSourceOnly
