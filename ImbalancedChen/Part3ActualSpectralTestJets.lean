import ImbalancedChen.Part3NativePeriod64Reconstruction
import ImbalancedChen.Part3ActualWeightedSpectralBudget
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivative bounds for the actual period-64 spectral tests

Selected declarations from the November 2 phase and test-jet suppliers are
reused in their original namespaces. The historical modules as a whole lie
outside the scope of this extract.
-/

noncomputable section
open scoped BigOperators ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)

namespace ImbalancedChen.Part3.ActualExceptionalJLargeTransform20261102
open Complex

def modeFrequency (k : D4 → ℤ) : ℂ :=
  (2 * Real.pi * I) * (((k 0 : ℝ) / 64 : ℝ) : ℂ)

theorem phase_hasDerivAt (k : D4 → ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P3Period64NativeReconstructionSourceOnly.e ((k 0 : ℝ)/64*s))
      (modeFrequency k * P3Period64NativeReconstructionSourceOnly.e ((k 0 : ℝ)/64*t)) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.const_mul (modeFrequency k)).cexp
  have he (s : ℝ) : P3Period64NativeReconstructionSourceOnly.e ((k 0 : ℝ)/64*s) =
      Complex.exp (modeFrequency k * (s : ℂ)) := by
    unfold P3Period64NativeReconstructionSourceOnly.e modeFrequency
    congr 1
    push_cast
    ring
  convert h using 1
  · funext s; exact he s
  · rw [he t]
    simp only [id_eq, Complex.ofReal_one, mul_one]
    exact mul_comm _ _

theorem modeFrequency_norm_le (k : D4 → ℤ) :
    ‖modeFrequency k‖ ≤ 2 * Real.pi * |(k 0 : ℝ)| := by
  simp only [modeFrequency, norm_mul, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 64)]
  have hp := Real.pi_pos
  nlinarith [abs_nonneg (k 0 : ℝ)]

end ImbalancedChen.Part3.ActualExceptionalJLargeTransform20261102

namespace ImbalancedChen.Part3.OriginalFullModulusTestJets20261102
open Classical Set MeasureTheory
open P3Period64NativeReconstructionSourceOnly
  (spectralTest spectralMode chi chi_contDiff chi_tsupport_subset spectralMode_contDiff norm_e)
open ImbalancedChen.Part3.ActualExceptionalJLargeTransform20261102
  (modeFrequency modeFrequency_norm_le phase_hasDerivAt)

attribute [local instance] Classical.propDecidable

private theorem iteratedDeriv_tsupport_subset (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using (Subset.rfl : tsupport f ⊆ tsupport f)
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

def complexChi (t : ℝ) : ℂ := (chi t : ℂ)
def nativePhase (ell : D4 → ℤ) (t : ℝ) : ℂ := P3Period64NativeReconstructionSourceOnly.e ((ell 0 : ℝ) / 64 * t)

theorem complexChi_contDiff : ContDiff ℝ ∞ complexChi :=
  Complex.ofRealCLM.contDiff.comp chi_contDiff

theorem nativePhase_contDiff (ell : D4 → ℤ) : ContDiff ℝ ∞ (nativePhase ell) := by
  unfold nativePhase P3Period64NativeReconstructionSourceOnly.e
  have hr : ContDiff ℝ ∞ (fun t : ℝ => (ell 0 : ℝ) / 64 * t) :=
    contDiff_const.mul contDiff_id
  exact ((contDiff_const : ContDiff ℝ ∞
    (fun _ : ℝ => (2 * Real.pi * Complex.I : ℂ))).mul
      (Complex.ofRealCLM.contDiff.comp hr)).cexp

theorem nativePhase_iteratedDeriv (ell : D4 → ℤ) (n : ℕ) :
    iteratedDeriv n (nativePhase ell) =
      fun t => modeFrequency ell ^ n * nativePhase ell t := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd := ((phase_hasDerivAt ell t).const_mul (modeFrequency ell ^ n)).deriv
    change deriv (fun t => modeFrequency ell ^ n * nativePhase ell t) t =
      modeFrequency ell ^ (n + 1) * nativePhase ell t
    rw [show deriv (fun t => modeFrequency ell ^ n * nativePhase ell t) t =
      modeFrequency ell ^ n * (modeFrequency ell * nativePhase ell t) from hd]
    rw [pow_succ]
    ring

/-- Exact all-order derivative formula. Its degree in ell_0 is at
most n; no frequency-dependent derivative cost is suppressed. -/
theorem spectralMode_iteratedDeriv (ell : D4 → ℤ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (spectralMode ell) t =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i complexChi t *
          (modeFrequency ell ^ (n - i) * nativePhase ell t) := by
  have hc : ContDiffAt ℝ n complexChi t :=
    (complexChi_contDiff.of_le (show (n : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hp : ContDiffAt ℝ n (nativePhase ell) t :=
    ((nativePhase_contDiff ell).of_le
      (show (n : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
  change iteratedDeriv n (complexChi * nativePhase ell) t = _
  rw [iteratedDeriv_mul hc hp]
  simp only [nativePhase_iteratedDeriv]

theorem spectralTest_iteratedDeriv (ell : D4 → ℤ) (Y : ℝ) (n : ℕ) (q : ℝ) :
    iteratedDeriv n (spectralTest ell Y) q =
      ((Y⁻¹ ^ n : ℝ) : ℂ) * iteratedDeriv n (spectralMode ell) (q / Y) := by
  have hs : ContDiff ℝ n (spectralMode ell) :=
    (spectralMode_contDiff ell).of_le
      (show (n : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have heq : spectralTest ell Y = (fun q : ℝ => spectralMode ell (Y⁻¹ * q)) := by
    funext q
    simp only [spectralTest, div_eq_mul_inv, mul_comm]
  rw [heq, iteratedDeriv_comp_const_smul hs]
  simp only [Complex.real_smul, div_eq_mul_inv, mul_comm]

private theorem complexChi_tsupport : tsupport complexChi ⊆ tsupport chi := by
  apply closure_minimal _ isClosed_closure
  intro t ht
  apply subset_closure
  intro hz
  exact ht (by simp only [complexChi, hz, Complex.ofReal_zero])

/-- Each constant is selected using ONLY the fixed cutoff and its
derivative order, before Y, ell, rho or any arithmetic source. -/
theorem exists_cutoffJetBound (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, ‖iteratedDeriv n complexChi t‖ ≤ B := by
  have hc := complexChi_contDiff.continuous_iteratedDeriv n
    (show (n : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hcompact : IsCompact (Icc (1 / 16 : ℝ) 16) := isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro t
  by_cases ht : t ∈ Icc (1 / 16 : ℝ) 16
  · exact (hB t ht).trans (by linarith [le_abs_self B])
  · have hz : iteratedDeriv n complexChi t = 0 := by
      by_contra hne
      have hs := chi_tsupport_subset (complexChi_tsupport
        (iteratedDeriv_tsupport_subset complexChi n (subset_closure hne)))
      exact ht ⟨hs.1.le, hs.2.le⟩
    rw [hz, norm_zero]
    positivity

def cutoffJetBound (n : ℕ) : ℝ := (exists_cutoffJetBound n).choose

theorem cutoffJetBound_pos (n : ℕ) : 0 < cutoffJetBound n :=
  (exists_cutoffJetBound n).choose_spec.1

theorem cutoffJetBound_bound (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n complexChi t‖ ≤ cutoffJetBound n :=
  (exists_cutoffJetBound n).choose_spec.2 t

def testJetConstant (n : ℕ) : ℝ :=
  (1 + 2 * Real.pi) ^ n *
    (1 + ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * cutoffJetBound i)

theorem testJetConstant_pos (n : ℕ) : 0 < testJetConstant n := by
  have hs : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * cutoffJetBound i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (cutoffJetBound_pos i).le)
  unfold testJetConstant
  positivity

/-- Explicit polynomial cost for every fixed derivative order. The
constant precedes ALL Fourier and physical parameters. -/
theorem spectralMode_jet_bound (n : ℕ) (ell : D4 → ℤ) (t : ℝ) :
    ‖iteratedDeriv n (spectralMode ell) t‖ ≤
      testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n := by
  let B : ℝ := 1 + 2 * Real.pi
  let W : ℝ := 1 + |(ell 0 : ℝ)|
  have hB : 1 ≤ B := by dsimp [B]; linarith [Real.pi_pos]
  have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg (ell 0 : ℝ)]
  have hBW : 1 ≤ B * W := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hW)]
  have hfreq : ‖modeFrequency ell‖ ≤ B * W := by
    have hf := modeFrequency_norm_le ell
    dsimp [B, W]
    nlinarith [Real.pi_pos, abs_nonneg (ell 0 : ℝ)]
  have hphase (i : ℕ) :
      ‖modeFrequency ell ^ (n - i) * nativePhase ell t‖ ≤ (B * W) ^ n := by
    simp only [norm_mul, norm_pow, nativePhase, norm_e, mul_one]
    exact (pow_le_pow_left₀ (norm_nonneg _) hfreq (n - i)).trans
      (pow_le_pow_right₀ hBW (Nat.sub_le n i))
  have hs : ‖iteratedDeriv n (spectralMode ell) t‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) * cutoffJetBound i) * (B * W) ^ n := by
    rw [spectralMode_iteratedDeriv]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (cutoffJetBound_bound i t) (Nat.cast_nonneg _))
      (hphase i) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (cutoffJetBound_pos i).le)
  calc
    ‖iteratedDeriv n (spectralMode ell) t‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℝ) * cutoffJetBound i) * (B * W) ^ n := hs
    _ = (B ^ n * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * cutoffJetBound i) * W ^ n := by
      rw [← Finset.sum_mul, mul_pow]
      ring
    _ ≤ testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ W) n)
      change B ^ n * _ ≤ B ^ n * (1 + _)
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) n)

theorem spectralTest_jet_bound (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y)
    (q : ℝ) :
    ‖iteratedDeriv n (spectralTest ell Y) q‖ ≤
      testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n / Y ^ n := by
  rw [spectralTest_iteratedDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hY.le) n)]
  calc
    Y⁻¹ ^ n * ‖iteratedDeriv n (spectralMode ell) (q / Y)‖ ≤
        Y⁻¹ ^ n * (testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n) :=
      mul_le_mul_of_nonneg_left (spectralMode_jet_bound n ell (q / Y))
        (pow_nonneg (inv_nonneg.mpr hY.le) n)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring

end ImbalancedChen.Part3.OriginalFullModulusTestJets20261102
end
