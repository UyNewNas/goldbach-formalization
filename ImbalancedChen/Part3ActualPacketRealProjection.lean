import ImbalancedChen.Part3ActualConjugatedPacket
import ImbalancedChen.Part3RealComponentReduction
import Mathlib.Tactic

/-!
PURE NEW CONTINUATION FRAGMENT / SOURCE_WRITTEN / UNCOMPILED.
Assembly prerequisite: the unchanged Part3ActualConjugatedPacket.lean.txt
candidate and actual import ImbalancedChen.Part3RealComponentReduction.
The standalone bundle is Part3ActualPacketRealProjection.lean.txt.
It supersedes the conjugated-packet bundle for assembly; do not load both
copies of the prerequisite declarations into one Lean environment.
-/

namespace ImbalancedChen.Part3.ActualPacketRealProjectionP3SourceOnly
noncomputable section

open Classical Set MeasureTheory
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3ActualLiteralPacketIntegralSourceOnly
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualConjugatedPacketP3SourceOnly

variable {ι : Type*}

/-- The original actual packet, including its original complex beta. -/
def actualModeIntegral (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℂ :=
  ∫ q : ℝ, kModeFunction P (commonHeight t) k q

/-- A genuine second signed-cusp/frequency packet, not a formal star variable. -/
def reflectedModeIntegral (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℂ :=
  actualModeIntegral (conjugatedPacketData P) (-k) t

/-- false selects Re, true selects Im, as in the existing real-component API. -/
def modeRealProjection (b : Bool) (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℝ :=
  if b then (actualModeIntegral P k t).im else (actualModeIntegral P k t).re

/-- Plus gives Re, minus gives i*Im. Both retain the original and reflected modes. -/
def signedHalfSum (minus : Bool) (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℂ :=
  (actualModeIntegral P k t +
    (if minus then (-1 : ℂ) else 1) * reflectedModeIntegral P k t) / 2

theorem reflectedModeIntegral_eq_star (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    reflectedModeIntegral P k t = star (actualModeIntegral P k t) := by
  exact actual_common_height_modeIntegral_conjugated P k t

/-- Reuse the actual existing complexRealComponent API. -/
theorem modeRealProjection_coe_eq_component (b : Bool) (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (modeRealProjection b P k t : ℂ) =
      complexRealComponent b (actualModeIntegral P k t) := by
  cases b <;> rfl

theorem actual_modeIntegral_re_half_sum (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ((actualModeIntegral P k t).re : ℂ) =
      (actualModeIntegral P k t + reflectedModeIntegral P k t) / 2 := by
  rw [reflectedModeIntegral_eq_star, Complex.star_def]
  exact Complex.re_eq_add_conj _

theorem actual_modeIntegral_im_half_difference (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ((actualModeIntegral P k t).im : ℂ) =
      (actualModeIntegral P k t - reflectedModeIntegral P k t) / (2 * Complex.I) := by
  rw [reflectedModeIntegral_eq_star, Complex.star_def]
  exact Complex.im_eq_sub_conj _

/-- The real branch is a genuine signed half-sum of two actual mode integrals. -/
theorem signedHalfSum_false (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    signedHalfSum false P k t = ((actualModeIntegral P k t).re : ℂ) := by
  change (actualModeIntegral P k t + (1 : ℂ) * reflectedModeIntegral P k t) / 2 = _
  rw [one_mul]
  exact (actual_modeIntegral_re_half_sum P k t).symm

/-- The minus branch is i times the imaginary projection, not a real-valued claim. -/
theorem signedHalfSum_true (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    signedHalfSum true P k t = ((actualModeIntegral P k t).im : ℂ) * Complex.I := by
  change (actualModeIntegral P k t + (-1 : ℂ) * reflectedModeIntegral P k t) / 2 = _
  rw [neg_one_mul, ← sub_eq_add_neg, reflectedModeIntegral_eq_star,
    Complex.star_def, Complex.sub_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- One Bool statement supplies both signed real-projection formulae. -/
theorem modeRealProjection_signed_formula (b : Bool) (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (modeRealProjection b P k t : ℂ) =
      (actualModeIntegral P k t +
        (if b then (-1 : ℂ) else 1) * reflectedModeIntegral P k t) /
          (if b then 2 * Complex.I else 2) := by
  cases b
  · change ((actualModeIntegral P k t).re : ℂ) =
      (actualModeIntegral P k t + (1 : ℂ) * reflectedModeIntegral P k t) / 2
    rw [one_mul]
    exact actual_modeIntegral_re_half_sum P k t
  · change ((actualModeIntegral P k t).im : ℂ) =
      (actualModeIntegral P k t + (-1 : ℂ) * reflectedModeIntegral P k t) /
        (2 * Complex.I)
    rw [neg_one_mul, ← sub_eq_add_neg]
    exact actual_modeIntegral_im_half_difference P k t

/-- Both half-sum branches reconstruct the original complex packet exactly. -/
theorem signedHalfSum_reconstruct (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    signedHalfSum false P k t + signedHalfSum true P k t = actualModeIntegral P k t := by
  rw [signedHalfSum_false, signedHalfSum_true]
  exact Complex.re_add_im _

/-- The two real projections reconstruct using the existing component phases. -/
theorem actual_modeIntegral_realComponents_reconstruct (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    (∑ b : Bool, complexRealComponentPhase b * (modeRealProjection b P k t : ℂ)) =
      actualModeIntegral P k t := by
  simp only [modeRealProjection_coe_eq_component]
  exact complexRealComponent_reconstruct _

/-- Each real projection is controlled by the norm, with no analytic assumption. -/
theorem modeRealProjection_abs_le_norm (b : Bool) (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    |modeRealProjection b P k t| ≤ ‖actualModeIntegral P k t‖ := by
  have h := complexRealComponent_norm_le b (actualModeIntegral P k t)
  rw [← modeRealProjection_coe_eq_component b P k t] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

theorem actual_modeIntegral_abs_re_le_norm (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    |(actualModeIntegral P k t).re| ≤ ‖actualModeIntegral P k t‖ := by
  exact modeRealProjection_abs_le_norm false P k t

theorem actual_modeIntegral_abs_im_le_norm (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    |(actualModeIntegral P k t).im| ≤ ‖actualModeIntegral P k t‖ := by
  exact modeRealProjection_abs_le_norm true P k t

/-- Either real sign is a half-sum with that same sign on both actual packets. -/
theorem actual_modeIntegral_signed_re_half_sum (negative : Bool)
    (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    (((if negative then (-1 : ℝ) else 1) * (actualModeIntegral P k t).re : ℝ) : ℂ) =
      ((if negative then (-1 : ℂ) else 1) * actualModeIntegral P k t +
        (if negative then (-1 : ℂ) else 1) * reflectedModeIntegral P k t) / 2 := by
  have hs : ((if negative then (-1 : ℝ) else 1 : ℝ) : ℂ) =
      (if negative then (-1 : ℂ) else 1) := by
    cases negative <;> norm_num
  rw [Complex.ofReal_mul, hs, actual_modeIntegral_re_half_sum]
  ring

theorem actual_modeIntegral_signed_re_abs_le_norm (negative : Bool)
    (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    |(if negative then (-1 : ℝ) else 1) * (actualModeIntegral P k t).re| ≤
      ‖actualModeIntegral P k t‖ := by
  cases negative
  · change |(1 : ℝ) * (actualModeIntegral P k t).re| ≤ _
    rw [one_mul]
    exact actual_modeIntegral_abs_re_le_norm P k t
  · change |(-1 : ℝ) * (actualModeIntegral P k t).re| ≤ _
    rw [neg_one_mul, abs_neg]
    exact actual_modeIntegral_abs_re_le_norm P k t

/-- Exact two-real-projection energy, not an inequality dropping a cross term. -/
theorem actual_modeIntegral_norm_sq_real_projections (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖actualModeIntegral P k t‖ ^ 2 =
      (modeRealProjection false P k t) ^ 2 + (modeRealProjection true P k t) ^ 2 := by
  change ‖actualModeIntegral P k t‖ ^ 2 =
    (actualModeIntegral P k t).re ^ 2 + (actualModeIntegral P k t).im ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- A branch has exactly the absolute value of the corresponding real projection. -/
theorem signedHalfSum_norm (b : Bool) (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖signedHalfSum b P k t‖ = |modeRealProjection b P k t| := by
  cases b
  · rw [signedHalfSum_false]
    change ‖((actualModeIntegral P k t).re : ℂ)‖ = |(actualModeIntegral P k t).re|
    rw [Complex.norm_real, Real.norm_eq_abs]
  · rw [signedHalfSum_true, norm_mul, Complex.norm_I, mul_one]
    change ‖((actualModeIntegral P k t).im : ℂ)‖ = |(actualModeIntegral P k t).im|
    rw [Complex.norm_real, Real.norm_eq_abs]

theorem signedHalfSum_norm_le (b : Bool) (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖signedHalfSum b P k t‖ ≤ ‖actualModeIntegral P k t‖ := by
  rw [signedHalfSum_norm]
  exact modeRealProjection_abs_le_norm b P k t

theorem actual_modeIntegral_norm_sq_signedHalfSums (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖actualModeIntegral P k t‖ ^ 2 =
      ‖signedHalfSum false P k t‖ ^ 2 + ‖signedHalfSum true P k t‖ ^ 2 := by
  rw [signedHalfSum_norm, signedHalfSum_norm, sq_abs, sq_abs]
  exact actual_modeIntegral_norm_sq_real_projections P k t

/-- Exact unnormalized plus branch. -/
theorem actual_modeIntegral_add_reflected (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    actualModeIntegral P k t + reflectedModeIntegral P k t =
      (2 : ℂ) * ((actualModeIntegral P k t).re : ℂ) := by
  rw [reflectedModeIntegral_eq_star, Complex.star_def]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.add_conj (actualModeIntegral P k t)

/-- Exact unnormalized minus branch. -/
theorem actual_modeIntegral_sub_reflected (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    actualModeIntegral P k t - reflectedModeIntegral P k t =
      (2 : ℂ) * ((actualModeIntegral P k t).im : ℂ) * Complex.I := by
  rw [reflectedModeIntegral_eq_star, Complex.star_def]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.sub_conj (actualModeIntegral P k t)

/-- Plus-branch cross term retained explicitly as Re(z*z). -/
theorem actual_modeIntegral_plus_energy_cross_term (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖actualModeIntegral P k t + reflectedModeIntegral P k t‖ ^ 2 =
      2 * ‖actualModeIntegral P k t‖ ^ 2 +
        2 * (actualModeIntegral P k t * actualModeIntegral P k t).re := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [actual_modeIntegral_add_reflected]
  simp only [norm_mul, h2, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]
  ring

/-- Minus-branch cross term has the opposite sign, and is not omitted. -/
theorem actual_modeIntegral_minus_energy_cross_term (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖actualModeIntegral P k t - reflectedModeIntegral P k t‖ ^ 2 =
      2 * ‖actualModeIntegral P k t‖ ^ 2 -
        2 * (actualModeIntegral P k t * actualModeIntegral P k t).re := by
  have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [actual_modeIntegral_sub_reflected]
  simp only [norm_mul, h2, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re]
  ring

/-- Exact polarization of the two actual signed-cusp/frequency packets. -/
theorem actual_modeIntegral_polarization (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖actualModeIntegral P k t + reflectedModeIntegral P k t‖ ^ 2 +
      ‖actualModeIntegral P k t - reflectedModeIntegral P k t‖ ^ 2 =
        4 * ‖actualModeIntegral P k t‖ ^ 2 := by
  rw [actual_modeIntegral_plus_energy_cross_term,
    actual_modeIntegral_minus_energy_cross_term]
  ring

/-- The same exact identity with the original norm square isolated. -/
theorem actual_modeIntegral_norm_sq_polarization (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    ‖actualModeIntegral P k t‖ ^ 2 =
      (‖actualModeIntegral P k t + reflectedModeIntegral P k t‖ ^ 2 +
        ‖actualModeIntegral P k t - reflectedModeIntegral P k t‖ ^ 2) / 4 := by
  rw [actual_modeIntegral_polarization]
  ring

end
end ImbalancedChen.Part3.ActualPacketRealProjectionP3SourceOnly

/-!
The original P and beta occur in actualModeIntegral throughout. The second
modeIntegral is the concrete conjugated-beta, opposite-cusp, opposite-mode
packet from the prerequisite. This algebra does not assert normalizedF is
real or actualCoeff is Hermitian, does not assume a spectral estimate, and
does not perform a finite Gram or Parseval expansion. The explicit plus/minus
energy formulae retain the cross term until exact cancellation is justified.
No actual .lean source or manuscript is modified; no compilation is claimed.
-/
