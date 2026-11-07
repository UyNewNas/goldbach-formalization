import ImbalancedChen.Part3ActualFullPacketFourierBridge
import ImbalancedChen.Part3FourierL1L2Plancherel
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.  Raw spectral height below is
Lebesgue dt, and the q integral is the original full kPhysical packet.
The exact energy identity consumes the actual full-packet Fourier theorem
and Mathlib's L² Fourier isometry through the staged L¹∩L² bridge.  It is
not an automorphic or Kuznetsov Plancherel statement.
-/

namespace ImbalancedChen.Part3.ActualFullPacketRawHeightEnergySourceOnly
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace
open P3ActualLiteralPacketIntegralSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualFullPacketFourierBridgeSourceOnly
open ActualKTransformFourier20261024z
open FourierL1L2PlancherelSourceOnly

variable {ι : Type*}

/-- The full actual physical K packet, integrated in q at one raw height. -/
def fullPhysicalHeight (P : PacketData ι) (t : ℝ) : ℂ :=
  ∫ q : ℝ, kPhysical P (commonHeight t) q

theorem fullPhysicalHeight_eq_half_fourier (P : PacketData ι) (t : ℝ) :
    fullPhysicalHeight P t =
      (1/2 : ℂ) * 𝓕 (physicalEvenProfile P) (t/Real.pi) :=
  fullPhysicalIntegral_eq_half_fourier P t

theorem physicalEvenProfile_continuous (P : PacketData ι) :
    Continuous (physicalEvenProfile P) := by
  rw [physicalEvenProfile_eq_generic]
  exact qLaplaceProfile_continuous P (physicalAmplitudeRaw P)
    (physicalAmplitudeRaw_isPhysical P)

theorem physicalEvenProfile_memLp_two (P : PacketData ι) :
    MemLp (physicalEvenProfile P) 2 := by
  exact (memLp_two_iff_integrable_sq_norm
    (physicalEvenProfile_continuous P).aestronglyMeasurable).2
      (physicalEvenProfile_norm_sq_integrable P)

theorem fullPhysicalHeight_continuous (P : PacketData ι) :
    Continuous (fullPhysicalHeight P) := by
  have hF : Continuous (𝓕 (physicalEvenProfile P)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (physicalEvenProfile_integrable P)
  have hscaled : Continuous (fun t : ℝ =>
      (1/2 : ℂ) * 𝓕 (physicalEvenProfile P) (t/Real.pi)) :=
    continuous_const.mul (hF.comp (continuous_id.div_const Real.pi))
  have heq : fullPhysicalHeight P = fun t : ℝ =>
      (1/2 : ℂ) * 𝓕 (physicalEvenProfile P) (t/Real.pi) :=
    funext (fullPhysicalHeight_eq_half_fourier P)
  rw [heq]
  exact hscaled

/-- The full physical packet belongs to L² of raw Lebesgue height dt. -/
theorem fullPhysicalHeight_norm_sq_integrable (P : PacketData ι) :
    Integrable (fun t : ℝ => ‖fullPhysicalHeight P t‖ ^ 2) := by
  have h := integrable_norm_sq_half_rescaled_fourier
    (physicalEvenProfile_integrable P) (physicalEvenProfile_memLp_two P)
  simpa only [fullPhysicalHeight_eq_half_fourier] using h

theorem fullPhysicalHeight_memLp_two (P : PacketData ι) :
    MemLp (fullPhysicalHeight P) 2 := by
  exact (memLp_two_iff_integrable_sq_norm
    (fullPhysicalHeight_continuous P).aestronglyMeasurable).2
      (fullPhysicalHeight_norm_sq_integrable P)

/-- Exact full raw-height energy, with the π/4 factor dictated by the
commonHeight and Fourier frequency t/π normalization. -/
theorem fullPhysicalHeight_energy (P : PacketData ι) :
    (∫ t : ℝ, ‖fullPhysicalHeight P t‖ ^ 2) =
      (Real.pi/4) * ∫ u : ℝ, ‖physicalEvenProfile P u‖ ^ 2 := by
  have h := integral_norm_sq_half_rescaled_fourier
    (physicalEvenProfile_integrable P) (physicalEvenProfile_memLp_two P)
  simpa only [fullPhysicalHeight_eq_half_fourier] using h

end
end ImbalancedChen.Part3.ActualFullPacketRawHeightEnergySourceOnly
