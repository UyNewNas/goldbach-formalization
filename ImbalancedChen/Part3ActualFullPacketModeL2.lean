import ImbalancedChen.Part3ActualFullPacketRawHeightEnergy
import ImbalancedChen.Part3ActualKHeightFourierTail
import ImbalancedChen.Part3ActualKFullHeightEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.  Every mode below is one of the
original `actualCoeff * kModeFunction` terms. Its height L² statement follows
from the actual q-Laplace profile and ordinary Fourier Plancherel.
-/

namespace ImbalancedChen.Part3.ActualFullPacketModeL2SourceOnly
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualKTransformFourier20261024z
open ActualKHeightFourierTail20261024z
open ActualKFullHeightEnergy20261024z
open FourierL1L2PlancherelSourceOnly

variable {ι : Type*}

/-- Uniform in the Fourier mode: only the original finite transformed
coefficient mass remains after taking norms of the completed phases. -/
theorem completedPacketSum_norm_le_coefficientMass (P : PacketData ι)
    (k : D4 → ℤ) :
    ‖completedPacketSum P k‖ ≤ coefficientMass P := by
  have htri :
      ‖completedPacketSum P k‖ ≤
        ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
          ‖(P.completed k).weight m *
            signedCoefficient P.negativeCusp
              (modePacket (P.packet j) k P.U P.Z) n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _hj
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro m _hm
    exact norm_sum_le _ _
  apply htri.trans
  apply Finset.sum_le_sum
  intro j _hj
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro n _hn
  rw [norm_mul, P.completed_weight_norm_mem k m hm,
    norm_signedCoefficient_modePacket, one_mul]
  rfl

theorem heightFourierTerm_eq_packet_const_mul_K (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    heightFourierTerm P t k =
      (actualCoeff P.rho P.sigma k * completedPacketSum P k) *
        kTestTransform P k t := by
  unfold heightFourierTerm
  rw [actual_common_height_modeIntegral]
  ring

theorem heightFourierTerm_norm_sq_integrable (P : PacketData ι)
    (k : D4 → ℤ) :
    Integrable (fun t : ℝ => ‖heightFourierTerm P t k‖ ^ 2) := by
  have h := (kTestTransform_norm_sq_integrable P k).const_mul
    (‖actualCoeff P.rho P.sigma k * completedPacketSum P k‖ ^ 2)
  have heq : (fun t : ℝ => ‖heightFourierTerm P t k‖ ^ 2) =
      fun t : ℝ => ‖actualCoeff P.rho P.sigma k * completedPacketSum P k‖ ^ 2 *
        ‖kTestTransform P k t‖ ^ 2 := by
    funext t
    rw [heightFourierTerm_eq_packet_const_mul_K, norm_mul, mul_pow]
  rw [heq]
  exact h

theorem heightFourierTerm_raw_height_energy (P : PacketData ι)
    (k : D4 → ℤ) :
    (∫ t : ℝ, ‖heightFourierTerm P t k‖ ^ 2) =
      ‖actualCoeff P.rho P.sigma k * completedPacketSum P k‖ ^ 2 *
        ((Real.pi/4) * ∫ u : ℝ, ‖actualKLaplaceProfile P k u‖ ^ 2) := by
  have hpoint (t : ℝ) :
      ‖heightFourierTerm P t k‖ ^ 2 =
        ‖actualCoeff P.rho P.sigma k * completedPacketSum P k‖ ^ 2 *
          ‖kTestTransform P k t‖ ^ 2 := by
    rw [heightFourierTerm_eq_packet_const_mul_K, norm_mul, mul_pow]
  simp_rw [hpoint]
  rw [integral_const_mul, kTestTransform_full_height_energy]

end
end ImbalancedChen.Part3.ActualFullPacketModeL2SourceOnly
