import Mathlib
import ImbalancedChen.Part3TwoLongNaturalP1

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A fixed explicit Fourier-decay constant for the actual compact Schwartz
long profiles. The N2 on the right is the original integral of the actual
function and its actual ordinary second derivative. No Fourier-decay or
P2 contract is supplied by the caller. The Mellin-twisted transition
profile N2 budget and the complete P2 assembly remain separate obligations.
-/
namespace ImbalancedChen.Part3.TwoLongN2FourierDecay
noncomputable section
open Classical MeasureTheory
open scoped SchwartzMap FourierTransform
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongActualDoublePeriodization
open ImbalancedChen.Part3.TwoLongQuantitativeTransitionProfiles

def secondSchwartz (F : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.derivCLM ℝ ℂ (SchwartzMap.derivCLM ℝ ℂ F)

@[simp] theorem secondSchwartz_apply (F : 𝓢(ℝ, ℂ)) (x : ℝ) :
    secondSchwartz F x = deriv (deriv (F : ℝ → ℂ)) x := rfl

def inverseTwoPiSq : ℝ := ((2*Real.pi)^2)⁻¹

theorem inverseTwoPiSq_nonneg : 0 ≤ inverseTwoPiSq := by
  unfold inverseTwoPiSq
  positivity

def normalizedSecond (F : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  F - inverseTwoPiSq • secondSchwartz F

/-- Two genuine ordinary integrations by parts, via Mathlib's exact
Fourier derivative theorem and the actual Schwartz derivatives. -/
theorem fourier_secondSchwartz (F : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (𝓕 (secondSchwartz F)) t = (-(2*Real.pi)^2*t^2 : ℝ) • (𝓕 F) t := by
  let D : 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℝ ℂ F
  have hF : 𝓕 (deriv (F : ℝ → ℂ)) =
      fun x : ℝ => (2*Real.pi*Complex.I*x) • 𝓕 (F : ℝ → ℂ) x :=
    Real.fourier_deriv F.integrable F.differentiable D.integrable
  have hD : 𝓕 (deriv (D : ℝ → ℂ)) =
      fun x : ℝ => (2*Real.pi*Complex.I*x) • 𝓕 (D : ℝ → ℂ) x :=
    Real.fourier_deriv D.integrable D.differentiable (secondSchwartz F).integrable
  rw [SchwartzMap.fourier_coe]
  change 𝓕 (deriv (D : ℝ → ℂ)) t = _
  rw [hD]
  change (2*Real.pi*Complex.I*t) • 𝓕 (deriv (F : ℝ → ℂ)) t = _
  rw [hF,SchwartzMap.fourier_coe]
  simp only [smul_eq_mul]
  push_cast
  calc
    _ = (Complex.I^2)*((2*(Real.pi : ℂ))^2*(t : ℂ)^2) *
        𝓕 (F : ℝ → ℂ) t := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem fourier_normalizedSecond (F : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (𝓕 (normalizedSecond F)) t = (1+t^2 : ℝ) • (𝓕 F) t := by
  have hlin : 𝓕 (normalizedSecond F) =
      𝓕 F - inverseTwoPiSq • 𝓕 (secondSchwartz F) := by
    simp only [normalizedSecond,sub_eq_add_neg,FourierTransform.fourier_add,
      FourierTransform.fourier_neg,FourierTransform.fourier_smul]
  rw [hlin]
  change (𝓕 F) t - inverseTwoPiSq • (𝓕 (secondSchwartz F)) t = _
  rw [fourier_secondSchwartz,smul_smul]
  have hp : (2*Real.pi)^2 ≠ 0 := by positivity
  have he : inverseTwoPiSq*(-(2*Real.pi)^2*t^2)= -t^2 := by
    unfold inverseTwoPiSq
    field_simp [hp]
    ring
  rw [he,neg_smul,sub_neg_eq_add,add_smul,one_smul]

theorem normalizedSecond_integral_norm_le (F : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, ‖normalizedSecond F x‖) ≤
      (1+inverseTwoPiSq)*N2 (F : ℝ → ℂ) := by
  have h0 : 0 ≤ ∫ x : ℝ, ‖F x‖ := integral_nonneg (fun _ => norm_nonneg _)
  have h2 : 0 ≤ ∫ x : ℝ, ‖secondSchwartz F x‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hi : Integrable (fun x : ℝ => ‖F x‖+inverseTwoPiSq*‖secondSchwartz F x‖) :=
    F.integrable.norm.add ((secondSchwartz F).integrable.norm.const_mul _)
  calc
    _ ≤ ∫ x : ℝ, ‖F x‖+inverseTwoPiSq*‖secondSchwartz F x‖ := by
      apply integral_mono (normalizedSecond F).integrable.norm hi
      intro x
      simpa only [normalizedSecond,sub_apply,smul_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg inverseTwoPiSq_nonneg] using
        (norm_sub_le (F x) (inverseTwoPiSq • secondSchwartz F x))
    _ = (∫ x : ℝ, ‖F x‖)+inverseTwoPiSq*(∫ x : ℝ, ‖secondSchwartz F x‖) := by
      rw [integral_add F.integrable.norm ((secondSchwartz F).integrable.norm.const_mul _),
        integral_const_mul]
    _ ≤ _ := by
      unfold N2
      simp only [secondSchwartz_apply] at h2 ⊢
      nlinarith [mul_nonneg inverseTwoPiSq_nonneg h0]

/-- The entire constant is fixed, independent of q,U,V,delta,Mellin
frequencies, and of the particular actual long profile. -/
def fourierDecayConstant : ℝ := 2*(1+inverseTwoPiSq)

theorem fourierDecayConstant_pos : 0 < fourierDecayConstant := by
  have hc := inverseTwoPiSq_nonneg
  unfold fourierDecayConstant
  positivity

theorem norm_fourier_le_N2 (F : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖(𝓕 F) t‖ ≤ fourierDecayConstant*N2 (F : ℝ → ℂ)/(1+|t|)^2 := by
  have hL1 : ‖(𝓕 (normalizedSecond F)) t‖ ≤ ∫ x : ℝ, ‖normalizedSecond F x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ ℝ) (normalizedSecond F : ℝ → ℂ) t
  rw [fourier_normalizedSecond,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1+t^2)] at hL1
  have hmass := hL1.trans (normalizedSecond_integral_norm_le F)
  have hratio : (1+|t|)^2 ≤ 2*(1+t^2) := by
    nlinarith [sq_nonneg (|t|-1),sq_abs t]
  apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^2)).2
  calc
    ‖(𝓕 F) t‖*(1+|t|)^2 ≤ ‖(𝓕 F) t‖*(2*(1+t^2)) :=
      mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
    _ ≤ fourierDecayConstant*N2 (F : ℝ → ℂ) := by
      unfold fourierDecayConstant
      nlinarith

/-- This bound immediately applies to the actual transition upper
profile with the previously proved uniform delta^-2 cost. -/
theorem actualUpper_fourier_decay {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (t : ℝ) :
    ‖(𝓕 (actualUpperSchwartz hd hs)) t‖ ≤
      fourierDecayConstant*(upperCost/delta^2)/(1+|t|)^2 := by
  apply (norm_fourier_le_N2 (actualUpperSchwartz hd hs) t).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (upper_N2 hd hs) fourierDecayConstant_pos.le

theorem actualGap_fourier_decay {delta : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (t : ℝ) :
    ‖(𝓕 (actualGapSchwartz hd hs)) t‖ ≤
      fourierDecayConstant*(gapCost/delta^2)/(1+|t|)^2 := by
  apply (norm_fourier_le_N2 (actualGapSchwartz hd hs) t).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (gap_N2 hd hs) fourierDecayConstant_pos.le

/-- The actual selected Mellin mode of batch A, promoted to Schwartz
using its proved global smoothness across zero and actual support. -/
def literalMellinSchwartz (t : ℝ) : 𝓢(ℝ, ℂ) :=
  (twist_compact t).toSchwartzMap (twist_smooth t)

@[simp] theorem literalMellinSchwartz_apply (t x : ℝ) :
    literalMellinSchwartz t x = twist t x := rfl

theorem literalMellin_fourier_decay_cube {H t : ℝ} (hH : 0 ≤ H) (ht : |t| ≤ H)
    (s : ℝ) :
    ‖(𝓕 (literalMellinSchwartz t)) s‖ ≤
      fourierDecayConstant*modeConstant*(1+H)^2/(1+|s|)^2 := by
  apply (norm_fourier_le_N2 (literalMellinSchwartz t) s).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ fourierDecayConstant*(modeConstant*(1+H)^2) :=
      mul_le_mul_of_nonneg_left (twist_N2_le_cube hH ht) fourierDecayConstant_pos.le
    _ = _ := by ring

end
end ImbalancedChen.Part3.TwoLongN2FourierDecay
