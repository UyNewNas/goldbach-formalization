import ImbalancedChen.Part3ActualCommonMask
import ImbalancedChen.Part3ActualFullPacketRawHeightEnergy
import ImbalancedChen.Part3ActualKPacketAdapter
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.

A finite Lebesgue-height longslot bound for the entire original physical
PacketData after one common m mask. The phase, rows, signed n coefficients,
coprime gates, normalized test, q region and imaginary-order K kernel remain
inside the left-hand side. The right-hand side is the *actual* finite
coefficient mass of the same masked record, times the already derived
physical q-kernel and region budgets. This is an absolute bound, with no
spectral saving or automorphic measure assertion.
-/

namespace ImbalancedChen.Part3.ActualCommonMaskLongslotEnergySourceOnly
noncomputable section

open Classical Set MeasureTheory
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open ActualKPacketAdapterSourceOnly
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.ActualFullPacketRawHeightEnergySourceOnly

variable {ι : Type*}

/-- The complete finite mass on one shared physical m interval. The
`signedCoefficient` still contains the original coprime gate and cusp phase. -/
def commonMaskCoefficientMass (P : PacketData ι) (a b : ℕ) : ℝ :=
  ∑ j ∈ P.rows, ∑ _m ∈ Finset.Ico a b ∩ P.mCarrier,
    ∑ n ∈ P.nCarrier j, ‖signedCoefficient P.negativeCusp (P.packet j) n‖

theorem commonMaskCoefficientMass_eq_actual (P : PacketData ι) (a b : ℕ) :
    commonMaskCoefficientMass P a b = coefficientMass (restrictM P a b) := by
  unfold commonMaskCoefficientMass coefficientMass
  rw [restrictM_mCarrier]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  exact norm_signedCoefficient P.negativeCusp (P.packet j) n

theorem commonMaskCoefficientMass_nonneg (P : PacketData ι) (a b : ℕ) :
    0 ≤ commonMaskCoefficientMass P a b := by
  rw [commonMaskCoefficientMass_eq_actual]
  exact coefficientMass_nonneg (restrictM P a b)

/-- Actual physical q integral at common raw height, with one m interval. -/
def maskedPhysicalHeight (P : PacketData ι) (a b : ℕ) (t : ℝ) : ℂ :=
  ∫ q : ℝ, kPhysical (restrictM P a b) (commonHeight t) q

theorem maskedPhysicalHeight_eq_full (P : PacketData ι) (a b : ℕ) :
    maskedPhysicalHeight P a b = fullPhysicalHeight (restrictM P a b) := rfl

theorem maskedPhysicalHeight_continuous (P : PacketData ι) (a b : ℕ) :
    Continuous (maskedPhysicalHeight P a b) := by
  rw [maskedPhysicalHeight_eq_full]
  exact fullPhysicalHeight_continuous (restrictM P a b)

theorem maskedPhysicalHeight_norm_sq_integrable (P : PacketData ι) (a b : ℕ) :
    Integrable (fun t : ℝ => ‖maskedPhysicalHeight P a b t‖ ^ 2) := by
  simp only [maskedPhysicalHeight_eq_full]
  exact fullPhysicalHeight_norm_sq_integrable (restrictM P a b)

/-- The existing physical q-kernel estimate applied to precisely the masked
PacketData, at every height. The constant is independent of the slot. -/
theorem maskedPhysicalHeight_norm_le (P : PacketData ι) (a b : ℕ)
    (J0 : ℕ) (t : ℝ) :
    ‖maskedPhysicalHeight P a b t‖ ≤
      actualW P.rho P.sigma J0 * commonMaskCoefficientMass P a b *
        (512 / P.Y0^2) * ((255/16 : ℝ) * P.Y0) := by
  have h := k_norm_fullIntegral_le (restrictM P a b) (commonHeight t) J0
  simpa only [maskedPhysicalHeight, commonMaskCoefficientMass_eq_actual,
    restrictM] using h

/-- The finite longslot has a certified L² energy bound. Its location is
arbitrary: only its length and the genuine common-mask coefficient mass occur
on the right. In particular no row-dependent mask or spectral hypothesis is
introduced. -/
theorem maskedPhysicalHeight_longslot_energy_le (P : PacketData ι)
    (a b J0 : ℕ) (A B : ℝ) (hAB : A ≤ B) :
    (∫ t in A..B, ‖maskedPhysicalHeight P a b t‖ ^ 2) ≤
      (B - A) *
        (actualW P.rho P.sigma J0 * commonMaskCoefficientMass P a b *
          (512 / P.Y0^2) * ((255/16 : ℝ) * P.Y0)) ^ 2 := by
  have hc : Continuous (fun t : ℝ => ‖maskedPhysicalHeight P a b t‖ ^ 2) :=
    (maskedPhysicalHeight_continuous P a b).norm.pow 2
  have hint : IntervalIntegrable
      (fun t : ℝ => ‖maskedPhysicalHeight P a b t‖ ^ 2) volume A B :=
    hc.intervalIntegrable A B
  have hconst : IntervalIntegrable
      (fun _ : ℝ =>
        (actualW P.rho P.sigma J0 * commonMaskCoefficientMass P a b *
          (512 / P.Y0^2) * ((255/16 : ℝ) * P.Y0)) ^ 2) volume A B :=
    continuous_const.intervalIntegrable A B
  have hpoint (t : ℝ) : ‖maskedPhysicalHeight P a b t‖ ^ 2 ≤
      (actualW P.rho P.sigma J0 * commonMaskCoefficientMass P a b *
        (512 / P.Y0^2) * ((255/16 : ℝ) * P.Y0)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (maskedPhysicalHeight_norm_le P a b J0 t) 2
  have h := intervalIntegral.integral_mono_on hAB hint hconst
    (fun t _ht => hpoint t)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

/-- Uniform over a translated slot of prescribed length H, including high
longslots: the bound has no dependence on its starting height. -/
theorem maskedPhysicalHeight_longslot_length_le (P : PacketData ι)
    (a b J0 : ℕ) (A B H : ℝ) (hAB : A ≤ B) (hlength : B - A ≤ H) :
    (∫ t in A..B, ‖maskedPhysicalHeight P a b t‖ ^ 2) ≤
      H *
        (actualW P.rho P.sigma J0 * commonMaskCoefficientMass P a b *
          (512 / P.Y0^2) * ((255/16 : ℝ) * P.Y0)) ^ 2 := by
  exact (maskedPhysicalHeight_longslot_energy_le P a b J0 A B hAB).trans
    (mul_le_mul_of_nonneg_right hlength (sq_nonneg _))

end
end ImbalancedChen.Part3.ActualCommonMaskLongslotEnergySourceOnly
