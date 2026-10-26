import ImbalancedChen.Part3ShiftOneEulerTailSelection
import ImbalancedChen.Part3NormalizedHeightProfileScaling

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The exact scalar input supplied by normalized geometric test estimates.
The actual compact height-profile pairing is genuinely integrable for a
continuous positive-height solution. For the tail-selected ACTUAL Euler
solution B*y^alphaMinus, the proved normalized scaling psi_t=t*phi(y/t)
gives the exact coefficient pairing. An upper bound C*t^(-1/2) therefore
implies ||B||*||moment||<=C*t^beta, beta=-1/2-alphaMinus>0.

The geometric normalized-test bound and a nonzero weighted moment are
explicit required inputs. No pointwise small-y growth or global mean L2
is inferred or assumed to follow automatically.
-/

namespace ImbalancedChen.Part3.ShiftOneEulerNormalizedTestEstimate20261026b
noncomputable section
open Set MeasureTheory
open CuspCylinderMeasure20261024z
open ShiftOneEulerClassification20261026b ShiftOneEulerTailSelection20261026b
open NormalizedHeightProfileScaling20261026b

def heightProfilePairing (φ : PositiveHeight → ℂ) (f : ℝ → ℂ) : ℂ :=
  ∫ y : PositiveHeight, star (φ y) * f (y : ℝ) ∂heightMeasure

theorem heightProfilePairing_integrable {φ : PositiveHeight → ℂ} (hφ : Continuous φ)
    (hcompact : HasCompactSupport φ) {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi (0 : ℝ))) :
    Integrable (fun y : PositiveHeight => star (φ y) * f (y : ℝ)) heightMeasure := by
  have hfc : Continuous (fun y : PositiveHeight => f (y : ℝ)) :=
    hf.comp_continuous continuous_subtype_val (fun y => y.property)
  exact (hφ.star.mul hfc).integrable_of_hasCompactSupport hcompact.star.mul_right

theorem normalizedHeightProfilePairing_integrable (t : PositiveHeight)
    {φ : PositiveHeight → ℂ} (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi (0 : ℝ))) :
    Integrable (fun y : PositiveHeight => star (normalizedHeightProfile t φ y) * f (y : ℝ))
      heightMeasure :=
  heightProfilePairing_integrable (normalizedHeightProfile_continuous t hφ)
    (normalizedHeightProfile_compact t hcompact) hf

theorem heightProfilePairing_decayingEuler (t : PositiveHeight) (φ : PositiveHeight → ℂ)
    {f : ℝ → ℂ} {B : ℂ}
    (hclass : ∀ y : ℝ, 0 < y → f y = B * eulerPower alphaMinus y) :
    heightProfilePairing (normalizedHeightProfile t φ) f =
      B * (((t : ℝ) ^ alphaMinus : ℝ) : ℂ) * heightPowerPairing alphaMinus φ := by
  calc
    _ = ∫ y : PositiveHeight, B *
        (star (normalizedHeightProfile t φ y) * heightPower alphaMinus y) ∂heightMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        rw [hclass y y.property, eulerPower_eq_rpow alphaMinus y.property]
        change star (normalizedHeightProfile t φ y) * (B * ((y : ℝ) ^ alphaMinus : ℝ)) = _
        unfold heightPower
        ring
    _ = B * heightPowerPairing alphaMinus (normalizedHeightProfile t φ) := by
      rw [integral_const_mul]
      rfl
    _ = _ := by rw [normalizedHeightProfile_power_pairing]; ring

def NormalizedEulerTestBound (C : ℝ) (φ : PositiveHeight → ℂ) (f : ℝ → ℂ) : Prop :=
  ∀ t : PositiveHeight, (t : ℝ) ≤ 1 →
    ‖heightProfilePairing (normalizedHeightProfile t φ) f‖ ≤ C * (t : ℝ) ^ (-(1 / 2 : ℝ))

def normalizedDecayGap : ℝ := -(1 / 2 : ℝ) - alphaMinus

theorem normalizedDecayGap_pos : 0 < normalizedDecayGap := by
  unfold normalizedDecayGap
  linarith [alphaMinus_lt_negHalf]

/-- The actual normalized test bound forces a vanishing positive-power
budget for the remaining Euler coefficient, without a pointwise bound. -/
theorem normalizedTest_coefficient_budget {C : ℝ} {φ : PositiveHeight → ℂ}
    {f : ℝ → ℂ} {B : ℂ}
    (hclass : ∀ y : ℝ, 0 < y → f y = B * eulerPower alphaMinus y)
    (hbound : NormalizedEulerTestBound C φ f) (t : PositiveHeight) (ht : (t : ℝ) ≤ 1) :
    ‖B‖ * ‖heightPowerPairing alphaMinus φ‖ ≤ C * (t : ℝ) ^ normalizedDecayGap := by
  have h := hbound t ht
  rw [heightProfilePairing_decayingEuler t φ hclass, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos t.property alphaMinus)] at h
  have hpow : 0 < (t : ℝ) ^ alphaMinus := Real.rpow_pos_of_pos t.property alphaMinus
  have hmul : (‖B‖ * ‖heightPowerPairing alphaMinus φ‖) * (t : ℝ) ^ alphaMinus ≤
      C * (t : ℝ) ^ (-(1 / 2 : ℝ)) := by
    convert h using 1 <;> ring
  calc
    _ ≤ (C * (t : ℝ) ^ (-(1 / 2 : ℝ))) / (t : ℝ) ^ alphaMinus :=
      (le_div_iff₀ hpow).mpr hmul
    _ = C * (t : ℝ) ^ normalizedDecayGap := by
      unfold normalizedDecayGap
      rw [Real.rpow_sub t.property]
      ring

end
end ImbalancedChen.Part3.ShiftOneEulerNormalizedTestEstimate20261026b
