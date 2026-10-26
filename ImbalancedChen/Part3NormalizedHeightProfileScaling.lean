import ImbalancedChen.Part3CuspCylinderMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact normalized small-height test scaling for the literal dy/y² measure.
For psi_t(y)=t*phi(y/t), physical squared mass is exactly t times the
original mass, and pairing against y^alpha is exactly t^alpha times the
original pairing. Both Jacobian and reciprocal-square factors are paid.
No quotient norm or small-height growth bound is assumed.
-/

namespace ImbalancedChen.Part3.NormalizedHeightProfileScaling20261026b
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z
attribute [local instance] Measure.Subtype.measureSpace

def heightDilation (t y : PositiveHeight) : PositiveHeight :=
  ⟨(t : ℝ) * y, mul_pos t.property y.property⟩

def heightInverseDilation (t y : PositiveHeight) : PositiveHeight :=
  ⟨(y : ℝ) / t, div_pos y.property t.property⟩

theorem heightInverseDilation_dilation (t y : PositiveHeight) :
    heightInverseDilation t (heightDilation t y) = y := by
  apply Subtype.ext
  change ((t : ℝ) * (y : ℝ)) / (t : ℝ) = (y : ℝ)
  field_simp [t.property.ne'] <;> ring

def heightDilationHomeomorph (t : PositiveHeight) : PositiveHeight ≃ₜ PositiveHeight where
  toFun := heightDilation t
  invFun := heightInverseDilation t
  left_inv := heightInverseDilation_dilation t
  right_inv y := by
    apply Subtype.ext
    change (t : ℝ) * ((y : ℝ) / (t : ℝ)) = (y : ℝ)
    field_simp [t.property.ne'] <;> ring
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.div_const (t : ℝ)).subtype_mk _

private theorem positive_axis_dilation_image (t : PositiveHeight) :
    (fun x : ℝ => (t : ℝ) * x) '' Ioi (0 : ℝ) = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mul_pos t.property hx
  · intro hy
    refine ⟨y / t, div_pos hy t.property, ?_⟩
    field_simp [t.property.ne'] <;> ring

theorem positive_axis_dilation_substitution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (t : PositiveHeight) (F : ℝ → E) :
    (∫ y in Ioi (0 : ℝ), F y) =
      ∫ s in Ioi (0 : ℝ), (t : ℝ) • F ((t : ℝ) * s) := by
  have hi : Set.InjOn (fun x : ℝ => (t : ℝ) * x) (Ioi 0) := by
    intro x hx y hy hxy
    exact mul_left_cancel₀ t.property.ne' hxy
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ => (by simpa using ((hasDerivAt_id x).const_mul (t : ℝ)).hasDerivWithinAt)) hi F
  rw [positive_axis_dilation_image] at h
  simpa only [abs_of_pos t.property] using h

def positiveExtension {E : Type*} [Zero E] (F : PositiveHeight → E) (y : ℝ) : E :=
  if hy : 0 < y then F ⟨y, hy⟩ else 0

theorem positiveHeight_integral_dilation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (t : PositiveHeight) (F : PositiveHeight → E) :
    (∫ y : PositiveHeight, F y) =
      ∫ s : PositiveHeight, (t : ℝ) • F (heightDilation t s) := by
  have h := positive_axis_dilation_substitution t (positiveExtension F)
  have hleft : (∫ y in Ioi (0 : ℝ), positiveExtension F y) = ∫ y : PositiveHeight, F y := by
    rw [← integral_subtype measurableSet_Ioi]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by simp only [positiveExtension, dif_pos y.property]
  have hright : (∫ s in Ioi (0 : ℝ), (t : ℝ) • positiveExtension F ((t : ℝ) * s)) =
      ∫ s : PositiveHeight, (t : ℝ) • F (heightDilation t s) := by
    rw [← integral_subtype measurableSet_Ioi]
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      simp only [positiveExtension, dif_pos (mul_pos t.property s.property), heightDilation]
  rwa [hleft, hright] at h

theorem weightedHeight_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : PositiveHeight → E) :
    (∫ y, F y ∂heightMeasure) =
      ∫ y : PositiveHeight, (1 / (y : ℝ)) ^ 2 • F y := by
  unfold heightMeasure
  rw [integral_withDensity_eq_integral_smul heightDensity_continuous.measurable]
  simp only [NNReal.smul_def, heightDensity_coe]

def normalizedHeightProfile (t : PositiveHeight) (φ : PositiveHeight → ℂ)
    (y : PositiveHeight) : ℂ := (t : ℂ) * φ (heightInverseDilation t y)

theorem normalizedHeightProfile_at_dilation (t : PositiveHeight) (φ : PositiveHeight → ℂ)
    (y : PositiveHeight) :
    normalizedHeightProfile t φ (heightDilation t y) = (t : ℂ) * φ y := by
  rw [normalizedHeightProfile, heightInverseDilation_dilation]

theorem normalizedHeightProfile_continuous (t : PositiveHeight) {φ : PositiveHeight → ℂ}
    (hφ : Continuous φ) : Continuous (normalizedHeightProfile t φ) :=
  continuous_const.mul (hφ.comp (heightDilationHomeomorph t).symm.continuous)

theorem normalizedHeightProfile_compact (t : PositiveHeight) {φ : PositiveHeight → ℂ}
    (hφ : HasCompactSupport φ) : HasCompactSupport (normalizedHeightProfile t φ) :=
  (hφ.comp_homeomorph (heightDilationHomeomorph t).symm).mul_left

def heightSquareMass (φ : PositiveHeight → ℂ) : ℝ :=
  ∫ y, ‖φ y‖ ^ 2 ∂heightMeasure

/-- Exact raw physical square mass, including Jacobian t and density t^-2. -/
theorem normalizedHeightProfile_square_mass (t : PositiveHeight) (φ : PositiveHeight → ℂ) :
    heightSquareMass (normalizedHeightProfile t φ) = (t : ℝ) * heightSquareMass φ := by
  unfold heightSquareMass
  rw [weightedHeight_integral, weightedHeight_integral, positiveHeight_integral_dilation t,
    ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  rw [normalizedHeightProfile_at_dilation]
  simp only [smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos t.property, mul_pow]
  change (t : ℝ) * ((1 / ((t : ℝ) * s)) ^ 2 * ((t : ℝ) ^ 2 * ‖φ s‖ ^ 2)) =
    (t : ℝ) * ((1 / (s : ℝ)) ^ 2 * ‖φ s‖ ^ 2)
  field_simp [t.property.ne', s.property.ne'] <;> ring

def heightPower (α : ℝ) (y : PositiveHeight) : ℂ := ((y : ℝ) ^ α : ℝ)

theorem heightPower_at_dilation (t : PositiveHeight) (α : ℝ) (s : PositiveHeight) :
    heightPower α (heightDilation t s) = (((t : ℝ) ^ α : ℝ) : ℂ) * heightPower α s := by
  unfold heightPower
  change ((((t : ℝ) * (s : ℝ)) ^ α : ℝ) : ℂ) =
    (((t : ℝ) ^ α : ℝ) : ℂ) * (((s : ℝ) ^ α : ℝ) : ℂ)
  rw [Real.mul_rpow t.property.le s.property.le, Complex.ofReal_mul]

def heightPowerPairing (α : ℝ) (φ : PositiveHeight → ℂ) : ℂ :=
  ∫ y, star (φ y) * heightPower α y ∂heightMeasure

/-- Exact normalized-profile pairing against a genuine physical Euler
power. This supplies a scalar test identity, not quotient admissibility. -/
theorem normalizedHeightProfile_power_pairing (t : PositiveHeight)
    (α : ℝ) (φ : PositiveHeight → ℂ) :
    heightPowerPairing α (normalizedHeightProfile t φ) =
      (((t : ℝ) ^ α : ℝ) : ℂ) * heightPowerPairing α φ := by
  unfold heightPowerPairing
  rw [weightedHeight_integral, weightedHeight_integral, positiveHeight_integral_dilation t,
    ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  rw [normalizedHeightProfile_at_dilation, heightPower_at_dilation]
  simp only [Complex.real_smul, star_mul, Complex.star_def, Complex.conj_ofReal,
    heightDilation, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul]
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast t.property.ne'
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast s.property.ne'
  field_simp [ht, hs] <;> ring

/-- A fixed original support [1,2] becomes the actual small band [t,2t]. -/
theorem normalizedHeightProfile_support_band (t : PositiveHeight) (φ : PositiveHeight → ℂ)
    (hφ : support φ ⊆ {y : PositiveHeight | 1 ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2}) :
    support (normalizedHeightProfile t φ) ⊆
      {y : PositiveHeight | (t : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * (t : ℝ)} := by
  intro y hy
  have hnonzero : φ (heightInverseDilation t y) ≠ 0 := by
    intro hz
    exact hy (by simp only [normalizedHeightProfile, hz, mul_zero])
  have hb := hφ hnonzero
  change 1 ≤ (y : ℝ) / t ∧ (y : ℝ) / t ≤ 2 at hb
  exact ⟨by simpa only [one_mul] using (le_div_iff₀ t.property).mp hb.1,
    (div_le_iff₀ t.property).mp hb.2⟩

end
end ImbalancedChen.Part3.NormalizedHeightProfileScaling20261026b

