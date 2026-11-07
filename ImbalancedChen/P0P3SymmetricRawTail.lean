import ImbalancedChen.P0P3RawHeightTail
import ImbalancedChen.P0P3RawHeightIntegrableAPI
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / 20261024z-P0. No acceptance credit.
Actual evenness and the two ordinary raw-Lebesgue energy tails. The closed
negative endpoint convention matches Mathlib's reflection theorem; endpoints
carry zero Lebesgue mass. No automorphic normalization is identified.
-/

namespace ImbalancedChen.Part3.P0P3SymmetricRawTailSourceOnly
noncomputable section

open Set MeasureTheory Filter
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImaginaryOrderKBesselSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open P0P3RawHeightTailSourceOnly
open P0P3RawHeightIntegrableAPISourceOnly

variable {ι : Type*}

/-- The actual test and completed packet are independent of spectral height. -/
theorem kTestTransform_neg (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k (-t) = kTestTransform P k t := by
  unfold kTestTransform
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by rw [imaginaryOrderK_neg])

theorem common_modeIntegral_neg (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction P (commonHeight (-t)) k q) =
      ∫ q : ℝ, kModeFunction P (commonHeight t) k q := by
  rw [actual_common_height_modeIntegral, actual_common_height_modeIntegral,
    kTestTransform_neg]

/-- Reflection is an exact change of variables in ordinary Lebesgue measure. -/
lemma negative_energy_tail_eq_positive {f : ℝ → ℂ} (heven : ∀ t, f (-t) = f t)
    (T : ℝ) :
    (∫ t in Iic (-T), ‖f t‖^2) = ∫ t in Ioi T, ‖f t‖^2 := by
  rw [← integral_comp_neg_Ioi T (fun t : ℝ => ‖f t‖^2)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by rw [heven t])

/-- Global actual energy integrability certifies both reflected tail domains. -/
theorem kTestTransform_two_tail_integrable (P : PacketData ι) (k : D4 → ℤ) (T : ℝ) :
    IntegrableOn (fun t => ‖kTestTransform P k t‖^2) (Iic (-T)) ∧
      IntegrableOn (fun t => ‖kTestTransform P k t‖^2) (Ioi T) := by
  have h := (kTestTransform_raw_height_integrability P k).2.1
  exact ⟨h.integrableOn, h.integrableOn⟩

theorem common_modeIntegral_two_tail_integrable (P : PacketData ι)
    (k : D4 → ℤ) (T : ℝ) :
    IntegrableOn (fun t : ℝ =>
      ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) (Iic (-T)) ∧
      IntegrableOn (fun t : ℝ =>
        ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) (Ioi T) := by
  have h := (common_modeIntegral_raw_height_integrability P k).2.1
  exact ⟨h.integrableOn, h.integrableOn⟩
/-- Explicit two-tail budget for the actual K-test transform. -/
theorem kTestTransform_two_tail_energy (P : PacketData ι) (k : D4 → ℤ)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in Iic (-T), ‖kTestTransform P k t‖^2) +
      (∫ t in Ioi T, ‖kTestTransform P k t‖^2) ≤
        2*((40800/P.Y0)^2/(3*T^3)) := by
  rw [negative_energy_tail_eq_positive (kTestTransform_neg P k) T]
  have h := (kTestTransform_positive_energy_tail P k hT).2.2
  linarith

/-- The same two-tail bound retains the actual frozen packet's energy. -/
theorem common_modeIntegral_two_tail_energy (P : PacketData ι) (k : D4 → ℤ)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in Iic (-T), ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) +
      (∫ t in Ioi T, ‖∫ q : ℝ, kModeFunction P (commonHeight t) k q‖^2) ≤
        2*(((40800/P.Y0)*‖completedPacketSum P k‖)^2/(3*T^3)) := by
  rw [negative_energy_tail_eq_positive (common_modeIntegral_neg P k) T]
  have h := (common_modeIntegral_positive_energy_tail P k hT).2.2
  linarith

end
end ImbalancedChen.Part3.P0P3SymmetricRawTailSourceOnly

