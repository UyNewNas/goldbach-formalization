import ImbalancedChen.Part3CuspCylinderMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual mode embeddings into the canonical cylinder L2(dx dy/y^2).
The circle has period one and normalized Haar mass one. Native Lp
representatives are used throughout; all representative changes are AE.
The exact inner-product factorization proves isometry and orthogonality.
This is the whole cylinder, without a truncated-cusp boundary condition.
-/

namespace ImbalancedChen.Part3.ActualCylinderModeEmbeddings20261026a
noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z

abbrev HeightL2 := Lp ℂ 2 heightMeasure
abbrev CylinderL2 := Lp ℂ 2 cylinderMeasure

def modeFunction (n : ℤ) (u : HeightL2) (z : CuspCylinder) : ℂ :=
  AddCircle.fourier n z.1 * u z.2

theorem modeFunction_norm (n : ℤ) (u : HeightL2) (z : CuspCylinder) :
    ‖modeFunction n u z‖ = ‖u z.2‖ := by
  simp [modeFunction, norm_mul, AddCircle.fourier_apply, Circle.norm_coe]

theorem modeFunction_memLp (n : ℤ) (u : HeightL2) :
    MemLp (modeFunction n u) 2 cylinderMeasure := by
  have hu := (Lp.memLp u).comp_snd
    (AddCircle.haarAddCircle (T := (1 : ℝ)))
  apply hu.of_le_mul (c := (1 : ℝ))
  · exact ((AddCircle.fourier n).continuous.comp continuous_fst).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u).comp_snd
  · exact Eventually.of_forall (fun z => by simp only [modeFunction_norm, one_mul, le_refl])

def modeVector (n : ℤ) (u : HeightL2) : CylinderL2 :=
  (modeFunction_memLp n u).toLp (modeFunction n u)

theorem modeVector_ae (n : ℤ) (u : HeightL2) :
    (modeVector n u : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] modeFunction n u :=
  (modeFunction_memLp n u).coeFn_toLp

theorem modeVector_add (n : ℤ) (u v : HeightL2) :
    modeVector n (u + v) = modeVector n u + modeVector n v := by
  apply Lp.ext
  have huv : ∀ᵐ z : CuspCylinder ∂cylinderMeasure, (u + v) z.2 = u z.2 + v z.2 :=
    (quasiMeasurePreserving_snd (μ := AddCircle.haarAddCircle) (ν := heightMeasure)).ae
      (Lp.coeFn_add u v)
  filter_upwards [modeVector_ae n (u + v), modeVector_ae n u, modeVector_ae n v,
    Lp.coeFn_add (modeVector n u) (modeVector n v), huv] with z hz hu hv hs huv
  simp only [Pi.add_apply] at hs
  rw [hz, hs, hu, hv]
  simp [modeFunction, huv, mul_add]

theorem modeVector_smul (n : ℤ) (c : ℂ) (u : HeightL2) :
    modeVector n (c • u) = c • modeVector n u := by
  apply Lp.ext
  have hcu : ∀ᵐ z : CuspCylinder ∂cylinderMeasure, (c • u) z.2 = c • u z.2 :=
    (quasiMeasurePreserving_snd (μ := AddCircle.haarAddCircle) (ν := heightMeasure)).ae
      (Lp.coeFn_smul c u)
  filter_upwards [modeVector_ae n (c • u), modeVector_ae n u,
    Lp.coeFn_smul c (modeVector n u), hcu] with z hz hu hs hcu
  simp only [Pi.smul_apply] at hs
  rw [hz, hs, hu]
  simp only [modeFunction, hcu, smul_eq_mul]
  ring

theorem circle_mode_inner (n m : ℤ) :
    (∫ x : UnitAddCircle,
      star (AddCircle.fourier n x) * AddCircle.fourier m x
      ∂AddCircle.haarAddCircle) = if n = m then (1 : ℂ) else 0 := by
  simp only [Complex.star_def, ← AddCircle.fourier_neg]
  change AddCircle.fourierCoeff (AddCircle.fourier m) n = _
  rw [AddCircle.fourierCoeff_fourier]
  simp [Pi.single_apply, eq_comm]

/-- Exact product-measure inner product, with no omitted circle factor. -/
theorem modeVector_inner (n m : ℤ) (u v : HeightL2) :
    inner ℂ (modeVector n u) (modeVector m v) =
      (if n = m then (1 : ℂ) else 0) * inner ℂ u v := by
  rw [L2.inner_def]
  calc
    (∫ z : CuspCylinder, inner ℂ (modeVector n u z) (modeVector m v z)
        ∂cylinderMeasure) =
        ∫ z : CuspCylinder,
          (star (AddCircle.fourier n z.1) * AddCircle.fourier m z.1) *
          (star (u z.2) * v z.2) ∂cylinderMeasure := by
      apply integral_congr_ae
      filter_upwards [modeVector_ae n u, modeVector_ae m v] with z hu hv
      rw [hu, hv]
      simp only [modeFunction, RCLike.inner_apply', map_mul]
      ring
    _ = (∫ x : UnitAddCircle,
          star (AddCircle.fourier n x) * AddCircle.fourier m x
          ∂AddCircle.haarAddCircle) * inner ℂ u v :=
      integral_prod_mul _ _
    _ = _ := by rw [circle_mode_inner]

theorem modeVector_norm (n : ℤ) (u : HeightL2) : ‖modeVector n u‖ = ‖u‖ := by
  have h := congrArg Complex.re (modeVector_inner n n u u)
  simp only [if_pos rfl, one_mul, inner_self_eq_norm_sq_to_K, Complex.ofReal_re] at h
  nlinarith [norm_nonneg (modeVector n u), norm_nonneg u]

def modeEmbedding (n : ℤ) : HeightL2 →ₗᵢ[ℂ] CylinderL2 where
  toFun := modeVector n
  map_add' := modeVector_add n
  map_smul' := modeVector_smul n
  norm_map' := modeVector_norm n

theorem modeEmbedding_ae (n : ℤ) (u : HeightL2) :
    (modeEmbedding n u : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (fun z => AddCircle.fourier n z.1 * u z.2) := modeVector_ae n u

theorem modeEmbedding_inner (n m : ℤ) (u v : HeightL2) :
    inner ℂ (modeEmbedding n u) (modeEmbedding m v) =
      (if n = m then (1 : ℂ) else 0) * inner ℂ u v := modeVector_inner n m u v

theorem modeEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun _ : ℤ => HeightL2) modeEmbedding := by
  intro n m hnm u v
  rw [modeEmbedding_inner, if_neg hnm, zero_mul]

theorem modeFunction_real_representative (n : ℤ) (u : HeightL2)
    (x : ℝ) (y : PositiveHeight) :
    modeFunction n u ((x : UnitAddCircle), y) =
      Complex.exp (2 * Real.pi * Complex.I * n * x) * u y := by
  simp [modeFunction, AddCircle.fourier_coe_apply]

end
end ImbalancedChen.Part3.ActualCylinderModeEmbeddings20261026a
