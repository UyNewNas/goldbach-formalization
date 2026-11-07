import ImbalancedChen.Part3PositiveRectanglePhysicalRellich
import ImbalancedChen.Part3Gamma0FiniteFourierFeatures
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal two-dimensional Fourier box projection, rank at most (2M+1)^2,
and actual affine quantitative error on ANY positive rectangle. The old
unit-square derivative/torus estimate is reused without reproof. The
distinct affine energy factors and the width*height Jacobian give
error² <= (w² E_x+h² E_y)/(4*pi²*M²). Zero finite features therefore
control physical and weighted physical mass, sufficient for a genuine
feature-kernel injection argument. No hRankBound, numerical certificate,
qualitative finite-net count or assumed approximation estimate is used. -/

namespace ImbalancedChen.Part3.QuantitativePositiveRectangleFourier20261026b
noncomputable section
open Set MeasureTheory Module
open scoped BigOperators
open PositiveRectangleAffineNormalization20261026b PositiveRectanglePhysicalRellich20261026b
open CompactRectanglePhysicalRellich20261026a ProductCircleFiniteBoxRellich20261026a
open LocalRectangleFourierTail20261026a Gamma0FiniteFourierFeatures20261026b

def rectangleModeBoxEquiv (M : ℕ) : RectangleMode M ≃ ↥(box M) :=
  Equiv.ofBijective (fun a => ⟨modeFrequency M a,modeFrequency_mem_box M a⟩) (by
    constructor
    · intro a b hab
      exact modeFrequency_injective M (congrArg Subtype.val hab)
    · intro k
      obtain ⟨a,ha⟩ := modeFrequency_covers_box M k k.property
      exact ⟨a,Subtype.ext ha⟩)

def torusFourierProjection (M : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  ∑ a : RectangleMode M,
    (innerSL ℂ (UnitAddTorus.mFourierBasis (modeFrequency M a))).smulRight
      (UnitAddTorus.mFourierBasis (modeFrequency M a))

theorem torusFourierProjection_apply (M : ℕ) (u : TorusL2) :
    torusFourierProjection M u = projection M u := by
  have hcoef (a : RectangleMode M) : inner ℂ (UnitAddTorus.mFourierBasis (modeFrequency M a)) u =
      UnitAddTorus.mFourierCoeff u (modeFrequency M a) := by
    rw [← UnitAddTorus.mFourierBasis_repr,HilbertBasis.repr_apply_apply]
  simp only [torusFourierProjection,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,hcoef]
  rw [projection_eq_synthesis]
  exact (rectangleModeBoxEquiv M).sum_comp (fun k : ↥(box M) =>
    UnitAddTorus.mFourierCoeff u k • UnitAddTorus.mFourierBasis k)

def finiteModeSpan (M : ℕ) : Submodule ℂ TorusL2 :=
  Submodule.span ℂ (range (fun a : RectangleMode M => UnitAddTorus.mFourierBasis (modeFrequency M a)))

theorem torusFourierProjection_range_le (M : ℕ) : (torusFourierProjection M).range ≤ finiteModeSpan M := by
  rintro v ⟨u,rfl⟩
  simp only [torusFourierProjection,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,rfl⟩)

theorem finiteModeSpan_finiteDimensional (M : ℕ) : FiniteDimensional ℂ (finiteModeSpan M) :=
  FiniteDimensional.span_of_finite ℂ (finite_range _)

theorem torusFourierProjection_finiteRange (M : ℕ) : FiniteDimensional ℂ (torusFourierProjection M).range := by
  letI := finiteModeSpan_finiteDimensional M
  exact Submodule.finiteDimensional_of_le (torusFourierProjection_range_le M)

/-- The actual linear projection has an explicit rank, not just an
unspecified finite-dimensional range from qualitative Rellich. -/
theorem torusFourierProjection_rank_bound (M : ℕ) :
    Module.finrank ℂ (torusFourierProjection M).range ≤ (2*M+1)^2 := by
  letI := finiteModeSpan_finiteDimensional M
  have hspan : Module.finrank ℂ (finiteModeSpan M) ≤ Fintype.card (RectangleMode M) :=
    Module.finrank_range_le_card (R := ℂ) (fun a : RectangleMode M =>
      UnitAddTorus.mFourierBasis (modeFrequency M a))
  have hcard : Fintype.card (RectangleMode M) = (2*M+1)^2 := by
    simp only [RectangleMode,Fintype.card_prod,Fintype.card_fin]
    ring
  exact (Submodule.finrank_mono (torusFourierProjection_range_le M)).trans (hspan.trans_eq hcard)

/-- Exact rectangle Jacobian and BOTH actual Euclidean energies. The
left side is the physical-scale norm of the literal Fourier residual. -/
theorem rectangle_fourier_residual_square_le {R : Rectangle} {δ : ℝ} (hδ : 0 < δ)
    (s : RectangleSeed R δ) (M : ℕ) (hM : 0 < M) :
    (R.width*R.height)*‖torusSeed (normalized s)-torusFourierProjection M (torusSeed (normalized s))‖^2 ≤
      tailConstant M*(R.width^2*directionalEnergy s 0+R.height^2*directionalEnergy s 1) := by
  rw [torusFourierProjection_apply]
  have h := physical_seed_torus_error hδ (normalized s) M hM
  rw [normalized_energy] at h
  apply (mul_le_mul_of_nonneg_left h (mul_pos R.width_pos R.height_pos).le).trans_eq
  field_simp [R.width_pos.ne',R.height_pos.ne']
  <;> ring

/-- A true explicit Euclidean error: max(width,height)/(2*pi*M) times
the square root of the actual two-coordinate gradient energy. -/
theorem rectangle_fourier_residual_norm_le {R : Rectangle} {δ : ℝ} (hδ : 0 < δ)
    (s : RectangleSeed R δ) (M : ℕ) (hM : 0 < M) :
    Real.sqrt (R.width*R.height)*
      ‖torusSeed (normalized s)-torusFourierProjection M (torusSeed (normalized s))‖ ≤
        (max R.width R.height/(2*Real.pi*(M : ℝ)))*
          Real.sqrt (directionalEnergy s 0+directionalEnergy s 1) := by
  have hW : 0 < max R.width R.height := R.width_pos.trans_le (le_max_left _ _)
  have hG : 0 ≤ directionalEnergy s 0+directionalEnergy s 1 :=
    add_nonneg (directionalEnergy_nonneg s 0) (directionalEnergy_nonneg s 1)
  have hE := rectangle_fourier_residual_square_le hδ s M hM
  have hw : R.width^2 ≤ (max R.width R.height)^2 :=
    pow_le_pow_left₀ R.width_pos.le (le_max_left _ _) 2
  have hh : R.height^2 ≤ (max R.width R.height)^2 :=
    pow_le_pow_left₀ R.height_pos.le (le_max_right _ _) 2
  have hbound : R.width^2*directionalEnergy s 0+R.height^2*directionalEnergy s 1 ≤
      (max R.width R.height)^2*(directionalEnergy s 0+directionalEnergy s 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hw (directionalEnergy_nonneg s 0),
      mul_le_mul_of_nonneg_right hh (directionalEnergy_nonneg s 1)]
  have hfinal := hE.trans (mul_le_mul_of_nonneg_left hbound (by unfold tailConstant; positivity))
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt (mul_pos R.width_pos R.height_pos).le,Real.sq_sqrt hG]
  have hden : (2*Real.pi*(M : ℝ)) ≠ 0 := by positivity
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  convert hfinal using 1 <;> unfold tailConstant <;> field_simp [hden,Real.pi_ne_zero,hMr] <;> ring

theorem projection_zero_of_box_coefficients_zero (M : ℕ) (u : TorusL2)
    (hz : ∀ k ∈ box M,UnitAddTorus.mFourierCoeff u k=0) : torusFourierProjection M u=0 := by
  rw [torusFourierProjection_apply]
  unfold projection
  apply Finset.sum_eq_zero
  intro k hk
  rw [hz k hk,zero_smul]

/-- Kernel injection needs only zero literal finite Fourier features;
this controls the ACTUAL original physical rectangle norm. -/
theorem rectangle_mass_le_of_box_coefficients_zero {R : Rectangle} {δ : ℝ} (hδ : 0 < δ)
    (s : RectangleSeed R δ) (M : ℕ) (hM : 0 < M)
    (hz : ∀ k ∈ box M,UnitAddTorus.mFourierCoeff (torusSeed (normalized s)) k=0) :
    ‖physical s‖^2 ≤ tailConstant M*(R.width^2*directionalEnergy s 0+R.height^2*directionalEnergy s 1) := by
  have h := rectangle_fourier_residual_square_le hδ s M hM
  rw [projection_zero_of_box_coefficients_zero M _ hz,sub_zero,torusSeed_norm hδ,normalized_square] at h
  have he : (R.width*R.height)*((R.width*R.height)⁻¹*‖physical s‖^2)=‖physical s‖^2 := by
    field_simp [R.width_pos.ne',R.height_pos.ne']
  rwa [he] at h

theorem rectangle_weighted_mass_le_of_box_coefficients_zero {R : Rectangle} {δ : ℝ} (hδ : 0 < δ)
    (s : RectangleSeed R δ) (M : ℕ) (hM : 0 < M)
    (hz : ∀ k ∈ box M,UnitAddTorus.mFourierCoeff (torusSeed (normalized s)) k=0) :
    ‖weightedPhysical s‖^2 ≤ (R.bottom⁻¹)^2*
      (tailConstant M*(R.width^2*directionalEnergy s 0+R.height^2*directionalEnergy s 1)) := by
  have hw := pow_le_pow_left₀ (norm_nonneg _) (weighted_norm_le s) 2
  rw [mul_pow] at hw
  exact hw.trans (mul_le_mul_of_nonneg_left (rectangle_mass_le_of_box_coefficients_zero hδ s M hM hz)
    (sq_nonneg _))

end
end ImbalancedChen.Part3.QuantitativePositiveRectangleFourier20261026b
