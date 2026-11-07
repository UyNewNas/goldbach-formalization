import ImbalancedChen.Part3ActualExceptionalJLargeKernel
import ImbalancedChen.Part3ActualExceptionalJPacketAdapter
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED. Actual positive-sign J transform on Y>1/16.

Two integrations by parts are combined into one exact flux derivative.
For f(q)=chi(q/Y)e(k0*q/(64Y)), the transferred numerator is
  (alpha^2-4)f + 3q f' - q^2 f''.
Both boundary jets vanish at the ORIGINAL support endpoints Y/16,16Y.
The kernel ODE, not a transform estimate, supplies the cancellation.
The actual phase derivatives cost (1+|k0|)^2. All constants are selected
before Y, alpha, k and the arithmetic packet.
-/

namespace ImbalancedChen.Part3.ActualExceptionalJLargeTransform20261102

noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly
open ActualExceptionalJSmallKernel20261102 ActualExceptionalJPacketAdapter20261102
open ActualExceptionalJLargeKernel20261102

variable {ι : Type*}

def modeSize (k : D4 → ℤ) : ℝ := 1 + |(k 0 : ℝ)|
def modeFrequency (k : D4 → ℤ) : ℂ :=
  (2 * Real.pi * I) * (((k 0 : ℝ) / 64 : ℝ) : ℂ)

theorem modeSize_ge_one (k : D4 → ℤ) : 1 ≤ modeSize k := by
  unfold modeSize
  linarith [abs_nonneg (k 0 : ℝ)]

theorem chi_first_contDiff : ContDiff ℝ ∞ (deriv chi) := chi_contDiff.deriv'
theorem chi_second_contDiff : ContDiff ℝ ∞ (deriv (deriv chi)) := chi_first_contDiff.deriv'

def modeFirst (k : D4 → ℤ) (t : ℝ) : ℂ :=
  ((deriv chi t : ℂ) + modeFrequency k * (chi t : ℂ)) * e ((k 0 : ℝ)/64*t)

def modeSecond (k : D4 → ℤ) (t : ℝ) : ℂ :=
  ((deriv (deriv chi) t : ℂ) + 2 * modeFrequency k * (deriv chi t : ℂ) +
    modeFrequency k ^ 2 * (chi t : ℂ)) * e ((k 0 : ℝ)/64*t)

theorem phase_hasDerivAt (k : D4 → ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => e ((k 0 : ℝ)/64*s))
      (modeFrequency k * e ((k 0 : ℝ)/64*t)) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.const_mul (modeFrequency k)).cexp
  have he (s : ℝ) : e ((k 0 : ℝ)/64*s) =
      Complex.exp (modeFrequency k * (s : ℂ)) := by
    unfold e modeFrequency
    congr 1
    push_cast
    ring
  convert h using 1
  · funext s; exact he s
  · rw [he t]
    ring

theorem spectralMode_hasDerivAt (k : D4 → ℤ) (t : ℝ) :
    HasDerivAt (spectralMode k) (modeFirst k t) t := by
  have h := ((chi_contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp).mul
    (phase_hasDerivAt k t)
  convert h using 1 <;> unfold spectralMode modeFirst <;> ring

theorem modeFirst_hasDerivAt (k : D4 → ℤ) (t : ℝ) :
    HasDerivAt (modeFirst k) (modeSecond k t) t := by
  have h0 := (chi_contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp
  have h1 := (chi_first_contDiff.differentiable (by simp) t).hasDerivAt.ofReal_comp
  have h := (h1.add (h0.const_mul (modeFrequency k))).mul (phase_hasDerivAt k t)
  convert h using 1 <;> unfold modeFirst modeSecond <;> ring

def testFirst (k : D4 → ℤ) (Y q : ℝ) : ℂ := modeFirst k (q/Y) / (Y : ℂ)
def testSecond (k : D4 → ℤ) (Y q : ℝ) : ℂ := modeSecond k (q/Y) / (Y : ℂ)^2

theorem spectralTest_hasDerivAt (k : D4 → ℤ) (Y q : ℝ) :
    HasDerivAt (spectralTest k Y) (testFirst k Y q) q := by
  have h := (spectralMode_hasDerivAt k (q/Y)).scomp q
    ((hasDerivAt_id q).div_const Y)
  simpa only [spectralTest, testFirst, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, one_div, div_eq_mul_inv, mul_comm] using h

theorem testFirst_hasDerivAt (k : D4 → ℤ) (Y q : ℝ) :
    HasDerivAt (testFirst k Y) (testSecond k Y q) q := by
  have h := ((modeFirst_hasDerivAt k (q/Y)).scomp q
    ((hasDerivAt_id q).div_const Y)).div_const (Y : ℂ)
  convert h using 1
  · rfl
  · simp only [testSecond, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    ring

theorem testSecond_continuous (k : D4 → ℤ) (Y : ℝ) : Continuous (testSecond k Y) := by
  have h0 := chi_contDiff.continuous
  have h1 := chi_first_contDiff.continuous
  have h2 := chi_second_contDiff.continuous
  unfold testSecond modeSecond e
  fun_prop

/-- Only a fixed compact cutoff has to be bounded; no physical or Bessel
quantity occurs in this choice of a constant. -/
theorem exists_chi_jet_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc (1/16 : ℝ) 16,
      |chi t| ≤ B ∧ |deriv chi t| ≤ B ∧ |deriv (deriv chi) t| ≤ B := by
  obtain ⟨B0, h0⟩ := (isCompact_Icc : IsCompact (Icc (1/16 : ℝ) 16))
    .exists_bound_of_continuousOn chi_contDiff.continuous.continuousOn
  obtain ⟨B1, h1⟩ := (isCompact_Icc : IsCompact (Icc (1/16 : ℝ) 16))
    .exists_bound_of_continuousOn chi_first_contDiff.continuous.continuousOn
  obtain ⟨B2, h2⟩ := (isCompact_Icc : IsCompact (Icc (1/16 : ℝ) 16))
    .exists_bound_of_continuousOn chi_second_contDiff.continuous.continuousOn
  refine ⟨|B0|+|B1|+|B2|+1, by positivity, ?_⟩
  intro t ht
  have h0' := h0 t ht
  have h1' := h1 t ht
  have h2' := h2 t ht
  simp only [Real.norm_eq_abs] at h0' h1' h2'
  constructor
  · linarith [le_abs_self B0, abs_nonneg B1, abs_nonneg B2]
  constructor
  · linarith [le_abs_self B1, abs_nonneg B0, abs_nonneg B2]
  · linarith [le_abs_self B2, abs_nonneg B0, abs_nonneg B1]

def chiJetBound : ℝ := exists_chi_jet_bound.choose
theorem chiJetBound_pos : 0 < chiJetBound := exists_chi_jet_bound.choose_spec.1

def modeJetConstant : ℝ := chiJetBound * (1 + 2 * Real.pi)^2
theorem modeJetConstant_pos : 0 < modeJetConstant := by
  have h := chiJetBound_pos
  unfold modeJetConstant
  positivity

theorem modeFrequency_norm_le (k : D4 → ℤ) :
    ‖modeFrequency k‖ ≤ 2 * Real.pi * |(k 0 : ℝ)| := by
  simp only [modeFrequency, norm_mul, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
    abs_div, abs_ofNat]
  have hp := Real.pi_pos
  nlinarith [abs_nonneg (k 0 : ℝ)]

theorem mode_jets_bound (k : D4 → ℤ) {t : ℝ} (ht : t ∈ Icc (1/16 : ℝ) 16) :
    ‖spectralMode k t‖ ≤ modeJetConstant * modeSize k^2 ∧
    ‖modeFirst k t‖ ≤ modeJetConstant * modeSize k^2 ∧
    ‖modeSecond k t‖ ≤ modeJetConstant * modeSize k^2 := by
  obtain ⟨h0, h1, h2⟩ := exists_chi_jet_bound.choose_spec.2 t ht
  have hB := chiJetBound_pos
  have hfreq := modeFrequency_norm_le k
  have hfn := norm_nonneg (modeFrequency k)
  have hm : 1 + ‖modeFrequency k‖ ≤ (1+2*Real.pi)*modeSize k := by
    unfold modeSize
    nlinarith [Real.pi_pos, abs_nonneg (k 0 : ℝ)]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖modeFrequency k‖) hm 2
  have hbig : chiJetBound * (1 + ‖modeFrequency k‖)^2 ≤
      modeJetConstant * modeSize k^2 := by
    simpa only [modeJetConstant, mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_left hs hB.le
  have hzero : ‖spectralMode k t‖ ≤ chiJetBound := by
    simpa only [spectralMode, norm_mul, norm_e, mul_one, Complex.norm_real,
      Real.norm_eq_abs] using h0
  have hone : ‖modeFirst k t‖ ≤ chiJetBound * (1 + ‖modeFrequency k‖) := by
    rw [modeFirst, norm_mul, norm_e, mul_one]
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_left h0 hfn
    nlinarith
  have htwo : ‖modeSecond k t‖ ≤ chiJetBound * (1 + ‖modeFrequency k‖)^2 := by
    rw [modeSecond, norm_mul, norm_e, mul_one]
    apply ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
    simp only [norm_mul, norm_pow, norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    have hh1 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2*‖modeFrequency k‖)
    have hh0 := mul_le_mul_of_nonneg_left h0 (sq_nonneg ‖modeFrequency k‖)
    nlinarith
  have hb0 : chiJetBound ≤ chiJetBound * (1 + ‖modeFrequency k‖)^2 := by
    nlinarith [mul_nonneg hB.le (sq_nonneg ‖modeFrequency k‖)]
  have hb1 : chiJetBound * (1 + ‖modeFrequency k‖) ≤
      chiJetBound * (1 + ‖modeFrequency k‖)^2 := by
    nlinarith [mul_nonneg hB.le (sq_nonneg ‖modeFrequency k‖)]
  exact ⟨hzero.trans (hb0.trans hbig), hone.trans (hb1.trans hbig), htwo.trans hbig⟩

theorem physical_test_jets_bound (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : q ∈ P.region) :
    ‖spectralTest k P.Y0 q‖ ≤ modeJetConstant * modeSize k^2 ∧
    ‖testFirst k P.Y0 q‖ ≤ modeJetConstant * modeSize k^2 / P.Y0 ∧
    ‖testSecond k P.Y0 q‖ ≤ modeJetConstant * modeSize k^2 / P.Y0^2 := by
  have ht : q/P.Y0 ∈ Icc (1/16 : ℝ) 16 := by
    constructor
    · apply (le_div_iff₀ P.Y0_pos).mpr
      have hlo : P.Y0/16 ≤ q := hq.1
      linarith
    · apply (div_le_iff₀ P.Y0_pos).mpr
      exact hq.2
  obtain ⟨h0, h1, h2⟩ := mode_jets_bound k ht
  refine ⟨h0, ?_, ?_⟩
  · simpa only [testFirst, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos P.Y0_pos] using div_le_div_of_nonneg_right h1 P.Y0_pos.le
  · simpa only [testSecond, norm_div, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos P.Y0_pos] using
      div_le_div_of_nonneg_right h2 (sq_nonneg P.Y0)

private theorem chi_endpoint_jets {t : ℝ} (ht : t = 1/16 ∨ t = 16) :
    chi t = 0 ∧ deriv chi t = 0 := by
  have hn : t ∉ tsupport chi := by
    intro hh
    have h := chi_tsupport_subset hh
    rcases ht with rfl | rfl <;> norm_num at h
  refine ⟨?_, deriv_of_notMem_tsupport hn⟩
  by_contra hz
  exact hn (subset_closure hz)

theorem physical_test_endpoint_jets (P : PacketData ι) (k : D4 → ℤ) :
    spectralTest k P.Y0 (P.Y0/16) = 0 ∧ testFirst k P.Y0 (P.Y0/16) = 0 ∧
    spectralTest k P.Y0 (16*P.Y0) = 0 ∧ testFirst k P.Y0 (16*P.Y0) = 0 := by
  have hlo := chi_endpoint_jets (t := 1/16) (Or.inl rfl)
  have hhi := chi_endpoint_jets (t := 16) (Or.inr rfl)
  have he0 : P.Y0/16/P.Y0 = 1/16 := by field_simp [P.Y0_pos.ne']
  have he1 : 16*P.Y0/P.Y0 = 16 := by field_simp [P.Y0_pos.ne']
  simp only [spectralTest, spectralMode, testFirst, modeFirst, he0, he1,
    hlo.1, hlo.2, hhi.1, hhi.2, Complex.ofReal_zero, mul_zero, zero_add,
    zero_mul, zero_div, and_self]

def adjointNumerator (alpha : ℝ) (k : D4 → ℤ) (Y q : ℝ) : ℂ :=
  ((alpha : ℂ)^2 - 4) * spectralTest k Y q +
    3 * (q : ℂ) * testFirst k Y q - (q : ℂ)^2 * testSecond k Y q

def transferredIntegrand (alpha : ℝ) (k : D4 → ℤ) (Y q : ℝ) : ℂ :=
  adjointNumerator alpha k Y q * positiveSignKernel alpha q / (q : ℂ)^3

def besselFlux (alpha : ℝ) (k : D4 → ℤ) (Y q : ℝ) : ℂ :=
  spectralTest k Y q * positiveSignFirst alpha q / (q : ℂ) -
    testFirst k Y q * positiveSignKernel alpha q / (q : ℂ) +
      2 * spectralTest k Y q * positiveSignKernel alpha q / (q : ℂ)^2

theorem besselFlux_hasDerivAt {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q)
    (k : D4 → ℤ) (Y : ℝ) :
    HasDerivAt (besselFlux alpha k Y)
      (transferredIntegrand alpha k Y q -
        spectralTest k Y q * (positiveSignKernel alpha q / (q : ℂ))) q := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hid := (hasDerivAt_id q).ofReal_comp
  have hf := spectralTest_hasDerivAt k Y q
  have hf1 := testFirst_hasDerivAt k Y q
  have hK := positiveSignKernel_hasDerivAt ha0 ha hq
  have hK1 := positiveSignFirst_hasDerivAt ha0 ha hq
  have h := (((hf.mul hK1).div hid hqC).sub
    ((hf1.mul hK).div hid hqC)).add
      (((hf.const_mul 2).mul hK).div (hid.pow 2) (pow_ne_zero 2 hqC))
  convert h using 1
  · rfl
  · rw [positiveSignSecond_eq ha0 ha hq]
    unfold transferredIntegrand adjointNumerator
    field_simp [hqC] <;> ring

/-- Exact two-IBP identity for the true spectral test. The endpoints and
all derivative data are proved from the original cutoff and native J. -/
theorem positive_transform_eq_transferred (P : PacketData ι) (k : D4 → ℤ)
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    positiveSignTestTransform P k alpha =
      ∫ q in (P.Y0/16)..(16*P.Y0), transferredIntegrand alpha k P.Y0 q := by
  have hab : P.Y0/16 ≤ 16*P.Y0 := by linarith [P.Y0_pos]
  have hqpos (q : ℝ) (hq : q ∈ uIcc (P.Y0/16) (16*P.Y0)) : 0 < q := by
    rw [uIcc_of_le hab] at hq
    linarith [hq.1, P.Y0_pos]
  have hcK : ContinuousOn (positiveSignKernel alpha)
      (uIcc (P.Y0/16) (16*P.Y0)) := fun q hq =>
    (positiveSignKernel_continuousAt ha0 ha (hqpos q hq)).continuousWithinAt
  have hc0 := (spectralTest_contDiff k P.Y0).continuous.continuousOn
  have hc1 : ContinuousOn (testFirst k P.Y0) (uIcc (P.Y0/16) (16*P.Y0)) :=
    fun q _ => (testFirst_hasDerivAt k P.Y0 q).continuousAt.continuousWithinAt
  have hc2 := (testSecond_continuous k P.Y0).continuousOn
  have hcq : ContinuousOn (fun q : ℝ => (q : ℂ))
      (uIcc (P.Y0/16) (16*P.Y0)) := Complex.continuous_ofReal.continuousOn
  have hn (q : ℝ) (hq : q ∈ uIcc (P.Y0/16) (16*P.Y0)) : (q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hqpos q hq).ne'
  have hG : ContinuousOn (transferredIntegrand alpha k P.Y0)
      (uIcc (P.Y0/16) (16*P.Y0)) := by
    exact ((((continuousOn_const.mul hc0).add ((continuousOn_const.mul hcq).mul hc1)).sub
      ((hcq.pow 2).mul hc2)).mul hcK).div (hcq.pow 3) (fun q hq => pow_ne_zero 3 (hn q hq))
  have hF : ContinuousOn (fun q => spectralTest k P.Y0 q *
      (positiveSignKernel alpha q / (q : ℂ)))
      (uIcc (P.Y0/16) (16*P.Y0)) := hc0.mul (hcK.div hcq hn)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun q hq => besselFlux_hasDerivAt ha0 ha (hqpos q hq) k P.Y0)
      (hG.sub hF).intervalIntegrable
  obtain ⟨hfa, hf1a, hfb, hf1b⟩ := physical_test_endpoint_jets P k
  simp only [besselFlux, hfa, hf1a, hfb, hf1b, zero_mul, mul_zero,
    zero_div, sub_zero, add_zero] at hFTC
  rw [intervalIntegral.integral_sub hG.intervalIntegrable hF.intervalIntegrable] at hFTC
  have he : (∫ q in (P.Y0/16)..(16*P.Y0), spectralTest k P.Y0 q *
      (positiveSignKernel alpha q / (q : ℂ))) = positiveSignTestTransform P k alpha := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro q hq
    have ht : spectralMode k (q/P.Y0) ≠ 0 := by
      intro hz
      exact hq (by simp only [spectralTest, hz, zero_mul])
    have ht' := spectralMode_support_subset k ht
    constructor
    · have hh := (lt_div_iff₀ P.Y0_pos).mp ht'.1
      linarith
    · exact ((div_lt_iff₀ P.Y0_pos).mp ht'.2).le
  rw [he] at hFTC
  exact (sub_eq_zero.mp hFTC).symm

theorem adjointNumerator_bound (P : PacketData ι) (k : D4 → ℤ)
    {alpha q : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : q ∈ P.region) :
    ‖adjointNumerator alpha k P.Y0 q‖ ≤
      309 * (modeJetConstant * modeSize k^2) := by
  obtain ⟨h0, h1, h2⟩ := physical_test_jets_bound P k hq
  let M : ℝ := modeJetConstant * modeSize k^2
  have hM : 0 ≤ M := by have h := modeJetConstant_pos; dsimp [M]; positivity
  have hq0 : 0 < q := by linarith [hq.1, P.Y0_pos]
  have hqY : q ≤ 16*P.Y0 := hq.2
  have ha1 : alpha ≤ 1 := ha.trans (by norm_num [exceptionalCap])
  have hco : ‖(alpha : ℂ)^2 - 4‖ ≤ 5 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg alpha]
  have hqfirst : q * ‖testFirst k P.Y0 q‖ ≤ 16*M := by
    have h := mul_le_mul_of_nonneg_left h1 hq0.le
    have h' : q * (M/P.Y0) ≤ 16*M := by
      apply (mul_le_mul_of_nonneg_right hqY (div_nonneg hM P.Y0_pos.le)).trans_eq
      field_simp [P.Y0_pos.ne']
    exact h.trans h'
  have hqsecond : q^2 * ‖testSecond k P.Y0 q‖ ≤ 256*M := by
    have h := mul_le_mul_of_nonneg_left h2 (sq_nonneg q)
    have hs := pow_le_pow_left₀ hq0.le hqY 2
    have h' : q^2 * (M/P.Y0^2) ≤ 256*M := by
      apply (mul_le_mul_of_nonneg_right hs (div_nonneg hM (sq_nonneg P.Y0))).trans_eq
      field_simp [P.Y0_pos.ne'] <;> ring
    exact h.trans h'
  unfold adjointNumerator
  apply ((norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
  simp only [norm_mul, norm_pow, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hq0]
  have hh0 := mul_le_mul hco h0 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)
  change _ ≤ 309*M
  nlinarith [hh0, hqfirst, hqsecond]

def largeTransformCoefficient : ℝ :=
  255 * 309 * 4096 * largeKernelConstant * modeJetConstant

theorem largeTransformCoefficient_pos : 0 < largeTransformCoefficient := by
  have hK := largeKernelConstant_pos
  have hM := modeJetConstant_pos
  unfold largeTransformCoefficient
  positivity

/-- Actual oscillatory cancellation, integrated against the unchanged
smooth test. It is uniform at alpha=0 and costs exactly two mode powers. -/
theorem positive_transform_large_inverse_square (P : PacketData ι) (k : D4 → ℤ)
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap)
    (hlarge : 1/16 < P.Y0) :
    ‖positiveSignTestTransform P k alpha‖ ≤
      largeTransformCoefficient * modeSize k^2 / P.Y0^2 := by
  rw [positive_transform_eq_transferred P k ha0 ha]
  have hab : P.Y0/16 ≤ 16*P.Y0 := by linarith [P.Y0_pos]
  let B : ℝ := 309 * (modeJetConstant * modeSize k^2) *
    (16 * largeKernelConstant) / (P.Y0/16)^3
  have hpoint (q : ℝ) (hq : q ∈ Ι (P.Y0/16) (16*P.Y0)) :
      ‖transferredIntegrand alpha k P.Y0 q‖ ≤ B := by
    rw [uIoc_of_le hab] at hq
    have hqr : q ∈ P.region := ⟨hq.1.le, hq.2⟩
    have hq0 : 0 < q := by linarith [P.Y0_pos, hq.1]
    have hqa : initialPoint ≤ q := by
      unfold initialPoint
      linarith [hq.1]
    have hN := adjointNumerator_bound P k ha0 ha hqr
    have hK := positiveSignKernel_transition_bound ha0 ha hqa
    have hK0 := largeKernelConstant_pos
    have hM0 := modeJetConstant_pos
    rw [transferredIntegrand, norm_div, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul hN hK (norm_nonneg _) (by positivity)) (by positivity : 0 ≤ q^3)).trans
    dsimp [B]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) hq.1.le 3
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  apply h.trans_eq
  rw [abs_of_nonneg (by linarith : 0 ≤ 16*P.Y0-P.Y0/16)]
  dsimp [B, largeTransformCoefficient]
  field_simp [P.Y0_pos.ne'] <;> ring

def largeTransformConstant : ℝ := 272 * largeTransformCoefficient
theorem largeTransformConstant_pos : 0 < largeTransformConstant := by
  have h := largeTransformCoefficient_pos
  unfold largeTransformConstant
  positivity

theorem positive_transform_large (P : PacketData ι) (k : D4 → ℤ)
    {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap)
    (hlarge : 1/16 < P.Y0) :
    ‖positiveSignTestTransform P k alpha‖ ≤
      largeTransformConstant / (1+P.Y0) * modeSize k^2 := by
  apply (positive_transform_large_inverse_square P k ha0 ha hlarge).trans
  have hy := P.Y0_pos
  have hc := largeTransformCoefficient_pos
  have hs : 1+P.Y0 ≤ 272*P.Y0^2 := by
    nlinarith [sq_nonneg (P.Y0-1/16)]
  have h := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ largeTransformCoefficient * modeSize k^2 by positivity)
  calc
    largeTransformCoefficient * modeSize k^2 / P.Y0^2 ≤
        (272 * largeTransformCoefficient * modeSize k^2) / (1+P.Y0) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hy) (by positivity : 0 < 1+P.Y0)).mpr
      nlinarith only [h]
    _ = _ := by unfold largeTransformConstant; ring

end
end ImbalancedChen.Part3.ActualExceptionalJLargeTransform20261102
