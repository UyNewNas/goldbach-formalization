import ImbalancedChen.Part3ActualCommonMask
import ImbalancedChen.Part3PhysicalQScaling
import ImbalancedChen.Part3ActualFullPacketRawHeightEnergy

/-!
SOURCE_ONLY / UNCOMPILED, 2026-10-24.

This boundary instantiates the physical packet Fourier identity on one actual
common m interval. The q test is the original `spectralTest k P.Y0`; the
mask changes only the m carrier. The height integral and energy below use
Lebesgue dt, without an automorphic spectral interpretation.
-/

namespace ImbalancedChen.Part3.ActualPacketCommonMaskPhysicalBoundarySourceOnly

noncomputable section

open Classical Set MeasureTheory
open scoped BigOperators FourierTransform
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (point4 spectralMode spectralTest)
open ImbalancedChen.Part3.ActualNormalizedSmoothF (normalizedF)
open ImaginaryOrderKBesselSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.PhysicalQScalingSourceOnly
open ImbalancedChen.Part3.ActualFullPacketFourierBridgeSourceOnly
open ImbalancedChen.Part3.ActualFullPacketRawHeightEnergySourceOnly

variable {ι : Type*}

/-- The numerator of the *literal* physical packet has exactly one common
mask in every original row. The signed n coefficient and normalized test
remain in their original positions. -/
theorem restricted_physicalNumerator (P : PacketData ι) (a b : ℕ) (q : ℝ) :
    physicalNumerator (restrictM P a b) q =
      ∑ j ∈ P.rows, ∑ m ∈ Finset.Ico a b ∩ P.mCarrier, ∑ n ∈ P.nCarrier j,
        signedCoefficient P.negativeCusp (P.packet j) n *
          normalizedF P.rho P.sigma
            (point4 (q/P.Y0) ((m : ℝ)/P.V)
              ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
              (((P.packet j).level : ℝ)/P.Z)) := by
  change (∑ j ∈ P.rows, ∑ m ∈ (restrictM P a b).mCarrier, ∑ n ∈ P.nCarrier j,
      signedCoefficient P.negativeCusp (P.packet j) n *
        normalizedF P.rho P.sigma
          (point4 (q/P.Y0) ((m : ℝ)/P.V)
            ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
            (((P.packet j).level : ℝ)/P.Z))) = _
  rw [restrictM_mCarrier]

/-- The K/q packet is restricted on that same m interval, without altering
the q kernel, row labels, signed n coefficients, or normalized test. -/
theorem restricted_kPhysical (P : PacketData ι) (a b : ℕ) (t q : ℝ) :
    kPhysical (restrictM P a b) (commonHeight t) q =
      ∑ j ∈ P.rows, ∑ m ∈ Finset.Ico a b ∩ P.mCarrier, ∑ n ∈ P.nCarrier j,
        signedCoefficient P.negativeCusp (P.packet j) n *
          ((imaginaryOrderK t q : ℂ)/(q : ℂ)) *
          normalizedF P.rho P.sigma
            (point4 (q/P.Y0) ((m : ℝ)/P.V)
              ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
              (((P.packet j).level : ℝ)/P.Z)) := by
  change (∑ j ∈ P.rows, ∑ m ∈ (restrictM P a b).mCarrier, ∑ n ∈ P.nCarrier j,
      signedCoefficient P.negativeCusp (P.packet j) n *
        ((imaginaryOrderK t q : ℂ)/(q : ℂ)) *
        normalizedF P.rho P.sigma
          (point4 (q/P.Y0) ((m : ℝ)/P.V)
            ((((P.packet j).multiplier*n : ℕ) : ℝ)/P.U)
            (((P.packet j).level : ℝ)/P.Z))) = _
  rw [restrictM_mCarrier]

/-- The mode test retains the original physical scale and the exact dq/q
change of variables after the common m restriction. -/
theorem restricted_kTestTransform_physical_scale (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform (restrictM P a b) k t =
      ∫ y in Icc (1/16 : ℝ) 16, spectralMode k y *
        ((imaginaryOrderK t (P.Y0*y) : ℂ)/(y : ℂ)) := by
  rw [restrictM_kTestTransform]
  exact kTestTransform_physical_scale_setIntegral P k t

/-- Raw Fourier representation of precisely that masked literal packet. -/
theorem restricted_fullPhysicalHeight_eq_half_fourier (P : PacketData ι)
    (a b : ℕ) (t : ℝ) :
    (∫ q : ℝ, kPhysical (restrictM P a b) (commonHeight t) q) =
      (1/2 : ℂ) * 𝓕 (physicalEvenProfile (restrictM P a b))
        (t/Real.pi) :=
  fullPhysicalIntegral_eq_half_fourier (restrictM P a b) t

/-- This is an identity for unweighted Lebesgue height dt only. -/
theorem restricted_fullPhysicalHeight_raw_energy (P : PacketData ι)
    (a b : ℕ) :
    (∫ t : ℝ, ‖fullPhysicalHeight (restrictM P a b) t‖ ^ 2) =
      (Real.pi/4) *
        ∫ u : ℝ, ‖physicalEvenProfile (restrictM P a b) u‖ ^ 2 :=
  fullPhysicalHeight_energy (restrictM P a b)

end

end ImbalancedChen.Part3.ActualPacketCommonMaskPhysicalBoundarySourceOnly
