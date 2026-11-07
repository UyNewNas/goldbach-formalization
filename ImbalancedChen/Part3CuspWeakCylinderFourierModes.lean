import ImbalancedChen.Part3CuspCompactHeightTestDetection

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual distributional tensor testing on the Haar × dy/y² cylinder forces
the native Fourier coefficient equation at almost every height,
simultaneously for every integer frequency. Integrability and Bochner
Fubini for the character tests are proved before the compact-height
fundamental lemma is invoked. There is no coefficient equation, classical
derivative, graph closure, or pointwise chart differentiability premise.

The two inputs here are native weighted-cylinder L² vectors. The separate
physical mixed-measure application requires putting the raw-dy derivative
in weighted L² on a positive cusp tail; this module makes no assertion of
global weighted integrability near height zero from raw-dy integrability.
-/
namespace ImbalancedChen.Part3.CuspWeakCylinderFourierModes20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open CuspCylinderMeasure20261024z ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open CuspCompactHeightTestDetection20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

def modeFrequency (n : ℤ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)

/-- Ordinary bilinear distributional horizontal differentiation, with
genuine smooth circle tests and real compact smooth height tests. -/
def HasWeakWeightedCylinderDerivative (F G : CylinderL2) : Prop :=
  ∀ φ ψ : C(UnitAddCircle, ℂ),
    ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)) →
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) →
    ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β →
      tsupport β ⊆ Ioi (0 : ℝ) →
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * G z ∂cylinderMeasure) =
        -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * F z ∂cylinderMeasure)

private theorem character_smooth (n : ℤ) :
    ContDiff ℝ ∞ (fun t : ℝ => AddCircle.fourier n (t : UnitAddCircle)) := by
  simp only [AddCircle.fourier_coe_apply, Complex.ofReal_one, div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Actual integrability of the cylinder character test: it is the inner
product of a native mode vector with the given cylinder L² vector. -/
theorem character_tensor_integrable (F : CylinderL2) (n : ℤ)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    Integrable (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) *
      AddCircle.fourier (-n) z.1 * F z) cylinderMeasure := by
  let hB := heightTest_memLp hβ hc hs
  let B : HeightL2 := hB.toLp (fun y : PositiveHeight => (β (y : ℝ) : ℂ))
  have hBa : (fun z : CuspCylinder => B z.2) =ᵐ[cylinderMeasure]
      (fun z => (β (z.2 : ℝ) : ℂ)) :=
    (quasiMeasurePreserving_snd (μ := AddCircle.haarAddCircle)
      (ν := heightMeasure)).ae hB.coeFn_toLp
  apply (L2.integrable_inner (modeEmbedding n B) F).congr
  filter_upwards [modeEmbedding_ae n B, hBa] with z hz hBz
  rw [hz, modeFunction, hBz]
  simp only [RCLike.inner_apply', map_mul, Complex.star_def,
    Complex.conj_ofReal, AddCircle.fourier_neg]
  ring

/-- The genuine Bochner Fubini step from a cylinder tensor integral to the
literal height Fourier coefficient, with absolute integrability above. -/
theorem character_tensor_fubini (F : CylinderL2) (n : ℤ)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) *
      AddCircle.fourier (-n) z.1 * F z ∂cylinderMeasure) =
      ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * sliceCoefficient n F y
        ∂heightMeasure := by
  rw [integral_prod_symm _ (character_tensor_integrable F n hβ hc hs)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    rfl

theorem compact_test_coefficient_equation {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) (n : ℤ)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    (∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * sliceCoefficient n G y ∂heightMeasure) =
      modeFrequency n *
        (∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * sliceCoefficient n F y ∂heightMeasure) := by
  have hd (t : ℝ) : HasDerivAt
      (fun s : ℝ => AddCircle.fourier (-n) (s : UnitAddCircle))
      (((-modeFrequency n) • AddCircle.fourier (-n)) (t : UnitAddCircle)) t := by
    convert AddCircle.hasDerivAt_fourier_neg (1 : ℝ) n t using 1 <;>
      simp [modeFrequency, smul_eq_mul] <;> ring
  have ht := hweak (AddCircle.fourier (-n))
    ((-modeFrequency n) • AddCircle.fourier (-n)) (character_smooth (-n)) hd
    β hβ hc hs
  have hre : (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) *
      (((-modeFrequency n) • AddCircle.fourier (-n)) z.1) * F z ∂cylinderMeasure) =
      (-modeFrequency n) * (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) *
        AddCircle.fourier (-n) z.1 * F z ∂cylinderMeasure) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [smul_eq_mul]; ring
  rw [hre, character_tensor_fubini G n hβ.continuous hc hs,
    character_tensor_fubini F n hβ.continuous hc hs] at ht
  simpa only [neg_mul, neg_neg] using ht

/-- A weak equation determines the native coefficient vector, rather than
requiring any coefficient relation as a hypothesis. -/
theorem weak_cylinder_coefficient {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) (n : ℤ) :
    cylinderCoefficient n G = modeFrequency n • cylinderCoefficient n F := by
  let U : HeightL2 := cylinderCoefficient n G - modeFrequency n • cylinderCoefficient n F
  have hU : U = 0 := by
    apply eq_zero_of_compact_height_tests
    intro β hβ hc hs
    have hB := heightTest_memLp hβ.continuous hc hs
    have hGi := hB.integrable_mul (Lp.memLp (cylinderCoefficient n G))
    have hFi := hB.integrable_mul (Lp.memLp (cylinderCoefficient n F))
    have hGF :
        (∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * cylinderCoefficient n G y ∂heightMeasure) =
        modeFrequency n *
          (∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * cylinderCoefficient n F y ∂heightMeasure) := by
      have hGint : (∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * cylinderCoefficient n G y
          ∂heightMeasure) =
          ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * sliceCoefficient n G y ∂heightMeasure := by
        apply integral_congr_ae
        filter_upwards [cylinderCoefficient_ae n G] with y hy
        rw [hy]
      have hFint : (∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * cylinderCoefficient n F y
          ∂heightMeasure) =
          ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * sliceCoefficient n F y ∂heightMeasure := by
        apply integral_congr_ae
        filter_upwards [cylinderCoefficient_ae n F] with y hy
        rw [hy]
      rw [hGint, hFint]
      exact compact_test_coefficient_equation hweak n hβ hc hs
    calc
      (∫ y : PositiveHeight, β (y : ℝ) • U y ∂heightMeasure) =
          ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * cylinderCoefficient n G y -
            modeFrequency n * ((β (y : ℝ) : ℂ) * cylinderCoefficient n F y)
            ∂heightMeasure := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (cylinderCoefficient n G)
          (modeFrequency n • cylinderCoefficient n F),
          Lp.coeFn_smul (modeFrequency n) (cylinderCoefficient n F)] with y hsub hsmul
        simp only [U, hsub, hsmul, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, Complex.real_smul]
        ring
      _ = (∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * cylinderCoefficient n G y ∂heightMeasure) -
          modeFrequency n * (∫ y : PositiveHeight,
            (β (y : ℝ) : ℂ) * cylinderCoefficient n F y ∂heightMeasure) := by
        rw [integral_sub hGi (hFi.const_mul (modeFrequency n)), integral_const_mul]
      _ = 0 := sub_eq_zero.mpr hGF
  exact sub_eq_zero.mp hU

/-- One countable AE set works for ALL integer modes, including n=0.
This is stronger than choosing a different exceptional set for each n. -/
theorem weak_cylinder_all_modes_ae {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) :
    ∀ᵐ y ∂heightMeasure, ∀ n : ℤ,
      sliceCoefficient n G y = modeFrequency n * sliceCoefficient n F y := by
  apply ae_all_iff.mpr
  intro n
  have hv := cylinderCoefficient_ae n G
  rw [weak_cylinder_coefficient hweak n] at hv
  filter_upwards [hv, Lp.coeFn_smul (modeFrequency n) (cylinderCoefficient n F),
    cylinderCoefficient_ae n F] with y hG hsmul hF
  simpa only [Pi.smul_apply, smul_eq_mul, hsmul, hF] using hG.symm

theorem weak_cylinder_zero_mode_ae {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) :
    ∀ᵐ y ∂heightMeasure, sliceCoefficient 0 G y = 0 := by
  filter_upwards [weak_cylinder_all_modes_ae hweak] with y hy
  simpa [modeFrequency] using hy 0

end
end ImbalancedChen.Part3.CuspWeakCylinderFourierModes20261026b
