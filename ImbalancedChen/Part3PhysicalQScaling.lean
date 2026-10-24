import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram

/-!
SOURCEONLY / UNCOMPILED. This source derives the positive physical-height
substitution q = Y0*y for the existing actual K transform. The factor Y0
from Lebesgue measure cancels the q in dq/q exactly. No spectral identity or
decay estimate is asserted.
-/

namespace ImbalancedChen.Part3.PhysicalQScalingSourceOnly

noncomputable section

open Classical Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralMode spectralTest)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform kTestTransform_integrable)

variable {ι : Type*}

/-- Lebesgue substitution by a positive real scale, with its Jacobian
kept explicitly inside the new integrand. -/
private theorem integral_positive_scale (Y : ℝ) (hY : 0 < Y) (f : ℝ → ℂ) :
    (∫ q : ℝ, f q) = ∫ y : ℝ, Y • f (Y*y) := by
  have hcomp := Measure.integral_comp_div (fun y : ℝ => f (Y*y)) Y
  have hcancel (q : ℝ) : Y * (q / Y) = q := by
    field_simp [hY.ne'] <;> ring
  simp only [hcancel, abs_of_pos hY] at hcomp
  exact hcomp.trans (integral_smul Y (fun y : ℝ => f (Y*y))).symm

/-- The pointwise cancellation also holds at y=0, using Lean's total division. -/
private theorem physical_K_pointwise (P : PacketData ι)
    (k : D4 → ℤ) (t y : ℝ) :
    P.Y0 • (spectralTest k P.Y0 (P.Y0*y) *
      ((imaginaryOrderK t (P.Y0*y) : ℂ)/((P.Y0*y : ℝ) : ℂ))) =
      spectralMode k y *
        ((imaginaryOrderK t (P.Y0*y) : ℂ)/(y : ℂ)) := by
  have hY : P.Y0 ≠ 0 := P.Y0_pos.ne'
  have hYc : (P.Y0 : ℂ) ≠ 0 := by exact_mod_cast hY
  have hdiv : P.Y0*y/P.Y0 = y := by
    field_simp [hY] <;> ring
  rw [spectralTest, hdiv]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  by_cases hy : y = 0
  · subst y
    simp
  · have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    field_simp [hYc, hyc] <;> ring

/-- The normalized y-integrand is genuinely integrable by transporting the
already proved integrability of the actual physical q-integrand. -/
theorem physical_K_normalized_integrable (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    Integrable (fun y : ℝ => spectralMode k y *
      ((imaginaryOrderK t (P.Y0*y) : ℂ)/(y : ℂ))) := by
  have hq := kTestTransform_integrable P k t
  have hscaled := hq.comp_mul_left' P.Y0_pos.ne'
  have hscaled' := Integrable.smul P.Y0 hscaled
  convert hscaled' using 1
  funext y
  exact (physical_K_pointwise P k t y).symm

/-- Exact normalization of the existing kTestTransform. In particular the
physical dq/q Jacobian leaves no extra Y0 factor. -/
theorem kTestTransform_physical_scale (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      ∫ y : ℝ, spectralMode k y *
        ((imaginaryOrderK t (P.Y0*y) : ℂ)/(y : ℂ)) := by
  unfold kTestTransform
  rw [integral_positive_scale P.Y0 P.Y0_pos
    (fun q : ℝ => spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ)/(q : ℂ)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (physical_K_pointwise P k t)

/-- The y interval is precisely the pullback of the actual physical region. -/
theorem normalized_mem_iff_physical_region (P : PacketData ι) (y : ℝ) :
    y ∈ Icc (1/16 : ℝ) 16 ↔ P.Y0*y ∈ P.region := by
  change ((1/16 : ℝ) ≤ y ∧ y ≤ 16) ↔
    P.Y0/16 ≤ P.Y0*y ∧ P.Y0*y ≤ 16*P.Y0
  constructor
  · intro h
    have hl := mul_le_mul_of_nonneg_left h.1 P.Y0_pos.le
    have hu := mul_le_mul_of_nonneg_left h.2 P.Y0_pos.le
    constructor <;> nlinarith
  · intro h
    constructor
    · by_contra hn
      have hlt : y < (1/16 : ℝ) := lt_of_not_ge hn
      have hmul := mul_lt_mul_of_pos_left hlt P.Y0_pos
      nlinarith [h.1]
    · by_contra hn
      have hlt : (16 : ℝ) < y := lt_of_not_ge hn
      have hmul := mul_lt_mul_of_pos_left hlt P.Y0_pos
      nlinarith [h.2]

/-- The compact set-integral version of the same exact transformation. -/
theorem kTestTransform_physical_scale_setIntegral (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      ∫ y in Icc (1/16 : ℝ) 16, spectralMode k y *
        ((imaginaryOrderK t (P.Y0*y) : ℂ)/(y : ℂ)) := by
  rw [kTestTransform_physical_scale]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hs : spectralMode k y = 0 := by
    by_contra hn
    have hm := P3Period64NativeReconstructionSourceOnly.spectralMode_support_subset
      k (show y ∈ Function.support (spectralMode k) from hn)
    exact hy ⟨hm.1.le, hm.2.le⟩
  simp only [hs, zero_mul]

end

end ImbalancedChen.Part3.PhysicalQScalingSourceOnly
