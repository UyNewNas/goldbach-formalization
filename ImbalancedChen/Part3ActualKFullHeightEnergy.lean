import ImbalancedChen.Part3ActualKTransformFourier
import ImbalancedChen.Part3FourierL1L2Plancherel
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED (2026-10-24).  This is the full, unweighted
Lebesgue-height L² energy of the physical K integral.  Its equality comes
from the genuine full-line Fourier Plancherel theorem and the separately
proved pointwise q-Laplace/Fourier identity; it is not a Kuznetsov or GL₂
spectral Plancherel assertion.
-/

namespace ImbalancedChen.Part3.ActualKFullHeightEnergy20261024z
noncomputable section

open Classical Set MeasureTheory
open scoped FourierTransform
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform)
open ActualKTransformFourier20261024z
open FourierL1L2PlancherelSourceOnly

variable {ι : Type*}

/-- The generic K transform of a continuous amplitude supported in the
physical q interval. -/
def amplitudeK (P : PacketData ι) (a : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ q : ℝ, a q * (imaginaryOrderK t q : ℂ)

/-- The Fourier profile meets the exact Mathlib `MemLp` premise, proved from
its norm-square integrability rather than supplied as a field. -/
theorem qLaplaceProfile_memLp_two (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) : MemLp (qLaplaceProfile P a) 2 := by
  exact (memLp_two_iff_integrable_sq_norm
    (qLaplaceProfile_continuous P a ha).aestronglyMeasurable).2
    (qLaplaceProfile_norm_sq_integrable P a ha)

/-- Genuine full-height energy with the exact Mathlib Fourier normalization.
No finite height cutoff or spectral measure occurs in this statement. -/
theorem amplitudeK_full_height_energy (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    (∫ t : ℝ, ‖amplitudeK P a t‖ ^ 2) =
      (Real.pi / 4) * ∫ u : ℝ, ‖qLaplaceProfile P a u‖ ^ 2 := by
  have h₁ := qLaplaceProfile_integrable P a ha
  have h₂ := qLaplaceProfile_memLp_two P a ha
  have henergy := integral_norm_sq_half_rescaled_fourier h₁ h₂
  have he (t : ℝ) : amplitudeK P a t =
      (1 / 2 : ℂ) * 𝓕 (qLaplaceProfile P a) (t / Real.pi) :=
    amplitudeK_half_fourier P a ha t
  simpa only [he] using henergy

/-- The full-height norm-square is integrable; this is stronger than merely
having an equality between Bochner integrals, whose default values could
otherwise conceal a divergent side. -/
theorem amplitudeK_norm_sq_integrable (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    Integrable (fun t : ℝ => ‖amplitudeK P a t‖ ^ 2) := by
  have h₁ := qLaplaceProfile_integrable P a ha
  have h₂ := qLaplaceProfile_memLp_two P a ha
  have hF := integrable_norm_sq_half_rescaled_fourier h₁ h₂
  refine hF.congr (Filter.Eventually.of_forall fun t => ?_)
  rw [amplitudeK_half_fourier P a ha t]

/-- A mode-independent operator bound.  Only the physical lower endpoint
enters the constant, so packets can sum amplitudes using their actual q-L¹
coefficient bounds. -/
theorem amplitudeK_full_height_energy_le (P : PacketData ι) (a : ℝ → ℂ)
    (ha : PhysicalAmplitude P a) :
    (∫ t : ℝ, ‖amplitudeK P a t‖ ^ 2) ≤
      ((Real.pi / 4) *
        ∫ u : ℝ, Real.exp (-(P.Y0 / 16) * |u|)) *
          (∫ q : ℝ, ‖a q‖) ^ 2 := by
  have hY : 0 < P.Y0 / 16 := by
    have := P.Y0_pos
    positivity
  have hprof : Integrable (fun u : ℝ => ‖qLaplaceProfile P a u‖ ^ 2) :=
    qLaplaceProfile_norm_sq_integrable P a ha
  have hmaj : Integrable (fun u : ℝ =>
      (∫ q : ℝ, ‖a q‖) ^ 2 * Real.exp (-(P.Y0 / 16) * |u|)) :=
    (exp_neg_abs_integrable hY).const_mul _
  have hle : (∫ u : ℝ, ‖qLaplaceProfile P a u‖ ^ 2) ≤
      (∫ q : ℝ, ‖a q‖) ^ 2 *
        ∫ u : ℝ, Real.exp (-(P.Y0 / 16) * |u|) := by
    rw [← integral_const_mul]
    apply integral_mono hprof hmaj
    intro u
    have h := qLaplaceProfile_norm_le P a ha u
    have hp := pow_le_pow_left₀ (norm_nonneg _) h 2
    calc
      ‖qLaplaceProfile P a u‖ ^ 2 ≤
          ((∫ q : ℝ, ‖a q‖) * Real.exp (-(P.Y0 / 32) * |u|)) ^ 2 := hp
      _ = (∫ q : ℝ, ‖a q‖) ^ 2 *
          Real.exp (-(P.Y0 / 16) * |u|) := by
        rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
        congr 1
        ring
  have hπ : 0 ≤ Real.pi / 4 := by positivity
  calc
    (∫ t : ℝ, ‖amplitudeK P a t‖ ^ 2) =
        (Real.pi / 4) * ∫ u : ℝ, ‖qLaplaceProfile P a u‖ ^ 2 :=
      amplitudeK_full_height_energy P a ha
    _ ≤ (Real.pi / 4) *
        ((∫ q : ℝ, ‖a q‖) ^ 2 *
          ∫ u : ℝ, Real.exp (-(P.Y0 / 16) * |u|)) :=
      mul_le_mul_of_nonneg_left hle hπ
    _ = _ := by ring

/-- On the actual test, the max denominator is invisible: `spectralTest` is
exactly zero off the physical q interval and max(q,Y0/32)=q on it. -/
theorem kTestTransform_eq_amplitudeK (P : PacketData ι) (k : D4 → ℤ)
    (t : ℝ) :
    kTestTransform P k t = amplitudeK P (actualKAmplitude P k) t := by
  unfold kTestTransform amplitudeK
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  rw [actualKAmplitude_eq]
  ring

theorem kTestTransform_full_height_energy (P : PacketData ι) (k : D4 → ℤ) :
    (∫ t : ℝ, ‖kTestTransform P k t‖ ^ 2) =
      (Real.pi / 4) * ∫ u : ℝ, ‖actualKLaplaceProfile P k u‖ ^ 2 := by
  have h := amplitudeK_full_height_energy P (actualKAmplitude P k)
    (actualKAmplitude_physical P k)
  simpa only [← kTestTransform_eq_amplitudeK,
    ← actualKLaplaceProfile_eq_generic] using h

theorem kTestTransform_norm_sq_integrable (P : PacketData ι) (k : D4 → ℤ) :
    Integrable (fun t : ℝ => ‖kTestTransform P k t‖ ^ 2) := by
  have h := amplitudeK_norm_sq_integrable P (actualKAmplitude P k)
    (actualKAmplitude_physical P k)
  simpa only [← kTestTransform_eq_amplitudeK] using h

theorem kTestTransform_full_height_energy_le (P : PacketData ι) (k : D4 → ℤ) :
    (∫ t : ℝ, ‖kTestTransform P k t‖ ^ 2) ≤
      ((Real.pi / 4) *
        ∫ u : ℝ, Real.exp (-(P.Y0 / 16) * |u|)) *
          (∫ q : ℝ, ‖actualKAmplitude P k q‖) ^ 2 := by
  simpa only [← kTestTransform_eq_amplitudeK] using
    amplitudeK_full_height_energy_le P (actualKAmplitude P k)
      (actualKAmplitude_physical P k)

end
end ImbalancedChen.Part3.ActualKFullHeightEnergy20261024z
