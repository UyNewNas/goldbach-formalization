import ImbalancedChen.P0P3HeightShellIntegralAPI
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / 20261024z-P0. No acceptance credit.
Explicit positive raw-height energy tails use ordinary unweighted Lebesgue dt.
No automorphic measure, Kuznetsov or Plancherel identity is claimed.
-/

namespace ImbalancedChen.Part3.P0P3RawHeightTailSourceOnly
noncomputable section

open Set MeasureTheory Filter
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open P0HeightPublicAPISourceOnly
open P0P3HeightShellIntegralAPISourceOnly

variable {ι : Type*}

lemma inv_fourth_integrableOn {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => (t^4)⁻¹) (Ioi T) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-4 : ℝ)) (by norm_num) hT
  simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast] using h

lemma inv_fourth_integral {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ in Ioi T, (t^4)⁻¹) = 1/(3*T^3) := by
  have h : (∫ t : ℝ in Ioi T, t ^ (-4 : ℝ)) = -T ^ (-3 : ℝ)/(-3) := by
    convert integral_Ioi_rpow_of_lt (a := (-4 : ℝ)) (by norm_num) hT using 1
    <;> norm_num
  calc
    (∫ t : ℝ in Ioi T, (t^4)⁻¹) = -(T^3)⁻¹/(-3) := by
      simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast] using h
    _ = 1/(3*T^3) := by field_simp [hT.ne']; ring

/-- Ordinary positive-tail energy from a proved quadratic-height norm bound. -/
lemma quadratic_energy_tail {f : ℝ → ℂ} (hf : Continuous f)
    {C T : ℝ} (hC : 0 ≤ C) (hT : 0 < T)
    (hbound : ∀ t ∈ Ioi T, ‖f t‖ ≤ C/t^2) :
    IntegrableOn (fun t => ‖f t‖^2) (Ioi T) ∧
      0 ≤ (∫ t in Ioi T, ‖f t‖^2) ∧
      (∫ t in Ioi T, ‖f t‖^2) ≤ C^2/(3*T^3) := by
  have hmajor : IntegrableOn (fun t : ℝ => C^2*(t^4)⁻¹) (Ioi T) :=
    (inv_fourth_integrableOn hT).const_mul (C^2)
  have henergy (t : ℝ) (ht : t ∈ Ioi T) : ‖f t‖^2 ≤ C^2*(t^4)⁻¹ := by
    have htp : 0 < t := hT.trans ht
    have h := hbound t ht
    have hp : 0 ≤ C/t^2 := by positivity
    calc
      ‖f t‖^2 ≤ (C/t^2)^2 := by nlinarith [norm_nonneg (f t)]
      _ = C^2*(t^4)⁻¹ := by field_simp [htp.ne']; ring
  have hint : IntegrableOn (fun t => ‖f t‖^2) (Ioi T) :=
    hmajor.mono' (hf.norm.pow 2).aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact henergy t ht)
  refine ⟨hint, integral_nonneg (fun t => sq_nonneg _), ?_⟩
  calc
    (∫ t in Ioi T, ‖f t‖^2) ≤ ∫ t in Ioi T, C^2*(t^4)⁻¹ := by
      apply integral_mono_ae hint hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact henergy t ht
    _ = C^2/(3*T^3) := by
      rw [integral_const_mul, inv_fourth_integral hT]
      ring

/-- The actual K-test transform has an explicit T^-3 positive energy tail. -/
theorem kTestTransform_positive_energy_tail (P : PacketData ι) (k : D4 → ℤ)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t => ‖kTestTransform P k t‖^2) (Ioi T) ∧
      0 ≤ (∫ t in Ioi T, ‖kTestTransform P k t‖^2) ∧
      (∫ t in Ioi T, ‖kTestTransform P k t‖^2) ≤
        (40800/P.Y0)^2/(3*T^3) := by
  apply quadratic_energy_tail (kTestTransform_continuous P k)
    (by have hY := P.Y0_pos; positivity) hT
  intro t ht
  have htp : 0 < t := hT.trans ht
  simpa only [div_div] using kTestTransform_norm_le_quadratic_simplified P k htp.ne'

/-- Exact common-height mode integral, retaining its full frozen packet energy. -/
theorem common_modeIntegral_positive_energy_tail (P : PacketData ι) (k : D4 → ℤ)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ =>
      ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) (Ioi T) ∧
      0 ≤ (∫ t in Ioi T, ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ∧
      (∫ t in Ioi T, ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ≤
        ((40800/P.Y0)*‖completedPacketSum P k‖)^2/(3*T^3) := by
  apply quadratic_energy_tail (common_height_modeIntegral_continuous P k)
    (by have hY := P.Y0_pos; positivity) hT
  intro t ht
  have htp : 0 < t := hT.trans ht
  have h := common_height_modeIntegral_norm_le_quadratic P k htp.ne'
  have he : (40800/(P.Y0*t^2))*‖completedPacketSum P k‖ =
      ((40800/P.Y0)*‖completedPacketSum P k‖)/t^2 := by
    field_simp [P.Y0_pos.ne', htp.ne']
    <;> ring
  simpa only [he] using h

end
end ImbalancedChen.Part3.P0P3RawHeightTailSourceOnly

