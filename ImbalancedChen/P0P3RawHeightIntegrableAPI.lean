import ImbalancedChen.P0P3AllHeightAPI
import ImbalancedChen.P0P3HeightShellIntegralAPI
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / 20261024z-P0. No acceptance credit.
The integrals in this file use ordinary unweighted Lebesgue dt on R.
They are not a spectral measure, Kuznetsov identity or Plancherel assertion.
-/

namespace ImbalancedChen.Part3.P0P3RawHeightIntegrableAPISourceOnly
noncomputable section

open MeasureTheory Set
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open P0P3AllHeightAPISourceOnly
open P0P3HeightShellIntegralAPISourceOnly

variable {ι : Type*}

/-- A regularized quadratic budget also dominates the square energy by an
integrable reciprocal quadratic. Concrete actual-K uses are below. -/
lemma energy_le_reciprocal_quadratic {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t, ‖f t‖ ≤ C/(1+t^2)) (t : ℝ) :
    ‖f t‖^2 ≤ C^2*(1+t^2)⁻¹ := by
  have hd : (0 : ℝ) < 1+t^2 := by positivity
  have hr0 : 0 ≤ (1+t^2)⁻¹ := inv_nonneg.mpr hd.le
  have hr1 : (1+t^2)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hd).mpr (by nlinarith [sq_nonneg t])
  have hr2 : ((1+t^2)⁻¹)^2 ≤ (1+t^2)⁻¹ := by nlinarith
  have h := hbound t
  rw [div_eq_mul_inv] at h
  have hp : 0 ≤ C*(1+t^2)⁻¹ := mul_nonneg hC hr0
  calc
    ‖f t‖^2 ≤ (C*(1+t^2)⁻¹)^2 := by nlinarith [norm_nonneg (f t)]
    _ = C^2*((1+t^2)⁻¹)^2 := mul_pow _ _ _
    _ ≤ C^2*(1+t^2)⁻¹ := mul_le_mul_of_nonneg_left hr2 (sq_nonneg C)

/-- Full raw-height integrability follows from proved continuity and an
explicit reciprocal-quadratic budget; no integrability premise is hidden. -/
lemma raw_height_integrability_budget {f : ℝ → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t, ‖f t‖ ≤ C/(1+t^2)) :
    Integrable f ∧ Integrable (fun t => ‖f t‖^2) ∧
      (∫ t : ℝ, ‖f t‖) ≤ C*Real.pi ∧
      (∫ t : ℝ, ‖f t‖^2) ≤ C^2*Real.pi := by
  have hmajor : Integrable (fun t : ℝ => C*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  have hfint : Integrable f := hmajor.mono' hf.aestronglyMeasurable (by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [div_eq_mul_inv] using hbound t)
  have henergymajor : Integrable (fun t : ℝ => C^2*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (C^2)
  have he : Integrable (fun t : ℝ => ‖f t‖^2) :=
    henergymajor.mono' (hf.norm.pow 2).aestronglyMeasurable (by
      apply Filter.Eventually.of_forall
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact energy_le_reciprocal_quadratic hC hbound t)
  refine ⟨hfint, he, ?_, ?_⟩
  · calc
      (∫ t : ℝ, ‖f t‖) ≤ ∫ t : ℝ, C*(1+t^2)⁻¹ :=
        integral_mono hfint.norm hmajor
          (fun t => by simpa only [div_eq_mul_inv] using hbound t)
      _ = C*Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  · calc
      (∫ t : ℝ, ‖f t‖^2) ≤ ∫ t : ℝ, C^2*(1+t^2)⁻¹ :=
        integral_mono he henergymajor (energy_le_reciprocal_quadratic hC hbound)
      _ = C^2*Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- Actual K-test transform, including its entire real height axis. -/
theorem kTestTransform_raw_height_integrability (P : PacketData ι) (k : D4 → ℤ) :
    Integrable (kTestTransform P k) ∧
      Integrable (fun t => ‖kTestTransform P k t‖^2) ∧
      (∫ t : ℝ, ‖kTestTransform P k t‖) ≤ (48960/P.Y0)*Real.pi ∧
      (∫ t : ℝ, ‖kTestTransform P k t‖^2) ≤ (48960/P.Y0)^2*Real.pi := by
  apply raw_height_integrability_budget (kTestTransform_continuous P k)
    (by have hY := P.Y0_pos; positivity)
  intro t
  simpa only [div_div] using kTestTransform_norm_le_allHeight P k t

/-- Frozen completed packet factors remain explicit in both raw-height masses. -/
theorem common_modeIntegral_raw_height_integrability (P : PacketData ι)
    (k : D4 → ℤ) :
    Integrable (fun t : ℝ => ∫ q : ℝ, kModeFunction P (commonHeight t) k q) ∧
      Integrable (fun t : ℝ =>
        ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ∧
      (∫ t : ℝ, ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖) ≤
        ((48960/P.Y0)*‖completedPacketSum P k‖)*Real.pi ∧
      (∫ t : ℝ, ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ≤
        ((48960/P.Y0)*‖completedPacketSum P k‖)^2*Real.pi := by
  apply raw_height_integrability_budget (common_height_modeIntegral_continuous P k)
    (by have hY := P.Y0_pos; positivity)
  intro t
  have h := common_height_modeIntegral_norm_le_allHeight P k t
  have he : (48960/(P.Y0*(1+t^2)))*‖completedPacketSum P k‖ =
      ((48960/P.Y0)*‖completedPacketSum P k‖)/(1+t^2) := by
    field_simp [P.Y0_pos.ne', ne_of_gt (by positivity : (0 : ℝ) < 1+t^2)]
    <;> ring
  simpa only [he] using h

end
end ImbalancedChen.Part3.P0P3RawHeightIntegrableAPISourceOnly
