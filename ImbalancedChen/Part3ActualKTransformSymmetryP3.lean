import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED. CODE_ONLY, 2026-10-24.
This file concerns the actual real chi times exponential test and the actual
integral realization K_{2it}(q) dq/q. It asserts no reality or Hermitian
symmetry for normalizedF, actualCoeff, or the frozen packet coefficients.
No Lean/lake/checker, numerical replay, audit, Git or external CI was run.
-/

namespace ImbalancedChen.Part3.ActualKTransformSymmetryP3SourceOnly
noncomputable section

open Set MeasureTheory
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e chi spectralMode spectralTest)
open P3ActualLiteralPacketIntegralSourceOnly
open ImaginaryOrderKBesselSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly

variable {ι : Type*}

/-- Conjugation of the actual exponential, with its exact 2*pi normalization. -/
theorem actual_e_neg (s : ℝ) : e (-s) = star (e s) := by
  unfold e
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  ring

/-- Only the actual spectral coordinate k 0 enters this test. -/
theorem spectralTest_eq_of_first_coordinate_eq (k l : D4 → ℤ)
    (hkl : k 0 = l 0) (Y0 q : ℝ) :
    spectralTest k Y0 q = spectralTest l Y0 q := by
  simp only [spectralTest, spectralMode, hkl]

/-- chi is real by its actual definition; the Fourier phase is conjugated. -/
theorem spectralMode_neg_frequency (k : D4 → ℤ) (s : ℝ) :
    spectralMode (-k) s = star (spectralMode k s) := by
  have hphase : ((-k) 0 : ℝ) / 64 * s = -((k 0 : ℝ) / 64 * s) := by
    change ((-(k 0) : ℤ) : ℝ) / 64 * s = -((k 0 : ℝ) / 64 * s)
    rw [Int.cast_neg]
    ring
  change (chi s : ℂ) * e (((-k) 0 : ℝ) / 64 * s) =
    star ((chi s : ℂ) * e ((k 0 : ℝ) / 64 * s))
  rw [hphase, actual_e_neg, star_mul']
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem spectralTest_neg_frequency (k : D4 → ℤ) (Y0 q : ℝ) :
    spectralTest (-k) Y0 q = star (spectralTest k Y0 q) := by
  exact spectralMode_neg_frequency k (q / Y0)

/-- Zero first coordinate is enough; the other three coordinates may be nonzero. -/
theorem spectralTest_eq_real_of_first_coordinate_zero (k : D4 → ℤ)
    (hk : k 0 = 0) (Y0 q : ℝ) :
    spectralTest k Y0 q = (chi (q / Y0) : ℂ) := by
  simp only [spectralTest, spectralMode, hk, Int.cast_zero, zero_div, zero_mul,
    e, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

theorem spectralTest_zero_frequency (Y0 q : ℝ) :
    spectralTest (0 : D4 → ℤ) Y0 q = (chi (q / Y0) : ℂ) := by
  exact spectralTest_eq_real_of_first_coordinate_zero 0 rfl Y0 q

theorem actual_K_quotient_star (t q : ℝ) :
    star ((imaginaryOrderK t q : ℂ) / (q : ℂ)) =
      (imaginaryOrderK t q : ℂ) / (q : ℂ) := by
  simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]

/-- Evenness holds for every frequency and all real height parameters. -/
theorem kTestTransform_neg_height (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k (-t) = kTestTransform P k t := by
  unfold kTestTransform
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by rw [imaginaryOrderK_neg])

/-- Actual frequency reflection conjugates the transform, not the packet sum. -/
theorem kTestTransform_neg_frequency (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P (-k) t = star (kTestTransform P k t) := by
  unfold kTestTransform
  calc
    (∫ q : ℝ, spectralTest (-k) P.Y0 q *
        ((imaginaryOrderK t q : ℂ) / (q : ℂ))) =
        ∫ q : ℝ, star (spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ) / (q : ℂ))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by
        rw [spectralTest_neg_frequency, star_mul', actual_K_quotient_star])
    _ = star (∫ q : ℝ, spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ) / (q : ℂ))) := by
      simpa only [Complex.star_def] using
        (integral_conj (f := fun q : ℝ => spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ) / (q : ℂ))))

/-- Exact real integral formula; no property of normalizedF is used. -/
theorem kTestTransform_zero_frequency_real_integral (P : PacketData ι) (t : ℝ) :
    kTestTransform P (0 : D4 → ℤ) t =
      ((∫ q : ℝ, chi (q / P.Y0) * (imaginaryOrderK t q / q) : ℝ) : ℂ) := by
  unfold kTestTransform
  calc
    (∫ q : ℝ, spectralTest (0 : D4 → ℤ) P.Y0 q *
        ((imaginaryOrderK t q : ℂ) / (q : ℂ))) =
        ∫ q : ℝ, ((chi (q / P.Y0) * (imaginaryOrderK t q / q) : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by
        rw [spectralTest_zero_frequency]
        simp only [Complex.ofReal_mul, Complex.ofReal_div])
    _ = _ := integral_complex_ofReal

theorem kTestTransform_zero_frequency_im (P : PacketData ι) (t : ℝ) :
    (kTestTransform P (0 : D4 → ℤ) t).im = 0 := by
  rw [kTestTransform_zero_frequency_real_integral]
  exact Complex.ofReal_im _

theorem kTestTransform_zero_frequency_star (P : PacketData ι) (t : ℝ) :
    star (kTestTransform P (0 : D4 → ℤ) t) =
      kTestTransform P (0 : D4 → ℤ) t := by
  rw [kTestTransform_zero_frequency_real_integral]
  simp only [Complex.star_def, Complex.conj_ofReal]

/-- The original physical support removes the singular quotient off the axis. -/
theorem kTestIntegrand_zero_off (P : PacketData ι) (k : D4 → ℤ)
    (t q : ℝ) (hq : q ∉ P.region) :
    spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ) / (q : ℂ)) = 0 := by
  simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
    Complex.ofReal_zero, zero_mul]

/-- The dq/q transform equals its exact integral on [Y0/16,16*Y0]. -/
theorem kTestTransform_eq_physical_setIntegral (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      ∫ q in P.region,
        spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ) / (q : ℂ)) := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun q hq => kTestIntegrand_zero_off P k t q hq)).symm

/-- Integrability on the physical region is supplied by the actual kernel. -/
theorem kTestIntegrand_integrableOn_physical_region (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    IntegrableOn (fun q : ℝ => spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ) / (q : ℂ))) P.region := by
  exact (kTestTransform_integrable P k t).integrableOn

/-- Exact common-height mode integral with the physical dq/q set integral. -/
theorem actual_common_height_modeIntegral_physical_region (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction P (commonHeight t) k q) =
      (∫ q in P.region, spectralTest k P.Y0 q *
        ((imaginaryOrderK t q : ℂ) / (q : ℂ))) * completedPacketSum P k := by
  rw [actual_common_height_modeIntegral, kTestTransform_eq_physical_setIntegral]

/-- The entire actual mode integral is even in its one common height. -/
theorem actual_common_height_modeIntegral_neg_height (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction P (commonHeight (-t)) k q) =
      ∫ q : ℝ, kModeFunction P (commonHeight t) k q := by
  rw [actual_common_height_modeIntegral, actual_common_height_modeIntegral,
    kTestTransform_neg_height]

/-- Reflection changes the packet frequency too; its coefficient is retained. -/
theorem actual_common_height_modeIntegral_neg_frequency (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction P (commonHeight t) (-k) q) =
      star (kTestTransform P k t) * completedPacketSum P (-k) := by
  rw [actual_common_height_modeIntegral, kTestTransform_neg_frequency]

/-- A complete reflected identity valid for arbitrary complex packet data.
No unproved conjugation law for the signed coprime coefficients is needed. -/
theorem actual_common_height_modeIntegral_reflected_cross_product
    (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, kModeFunction P (commonHeight t) (-k) q) *
        star (completedPacketSum P k) =
      star (∫ q : ℝ, kModeFunction P (commonHeight t) k q) *
        completedPacketSum P (-k) := by
  rw [actual_common_height_modeIntegral_neg_frequency,
    actual_common_height_modeIntegral, star_mul']
  ring

/-- Zero frequency makes the analytic factor real; the packet may be complex. -/
theorem actual_common_height_modeIntegral_zero_frequency (P : PacketData ι)
    (t : ℝ) :
    (∫ q : ℝ, kModeFunction P (commonHeight t) (0 : D4 → ℤ) q) =
      ((∫ q : ℝ, chi (q / P.Y0) * (imaginaryOrderK t q / q) : ℝ) : ℂ) *
        completedPacketSum P (0 : D4 → ℤ) := by
  rw [actual_common_height_modeIntegral, kTestTransform_zero_frequency_real_integral]

/-- The record-updated literal packet's actual modeFunction has the same formula. -/
theorem withKKernel_common_height_modeIntegral (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∫ q : ℝ, (withKKernel P (commonHeight t)).modeFunction k q) =
      kTestTransform P k t * completedPacketSum P k := by
  rw [withKKernel_modeFunction]
  exact actual_common_height_modeIntegral P k t

end
end ImbalancedChen.Part3.ActualKTransformSymmetryP3SourceOnly

/-!
OPEN: this gives exact symmetry and physical support formulae only. It does not
identify a Kuznetsov normalization, construct an automorphic Plancherel measure,
prove a height-decay estimate, or establish any conjugation identity for
normalizedF / actualCoeff / completedPacketSum. The 7/32 and large-sieve inputs
are unaffected. This source is not a compiled or accepted proof artifact.
-/
