import ImbalancedChen.Part3OriginalFullModulusSupport
import ImbalancedChen.Part3ActualExceptionalJLargeTransform
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual chi(q/Y)*e(ell_0*q/(64Y)), with no PacketData construction.
The fixed cutoff, phase derivative and norm estimate are reused from M.
All endpoint jets vanish; arbitrary fixed derivative order has its
explicit polynomial mode cost, summable against the SAME actualCoeff.
No Bessel transform estimate or automorphic trace is claimed here.
-/

noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (actualCoeff spectralTest spectralMode chi chi_contDiff chi_tsupport_subset
    spectralMode_contDiff spectralTest_contDiff e norm_e)
open ImbalancedChen.Part3.ActualExceptionalJLargeTransform20261102
  (modeFrequency modeFrequency_norm_le phase_hasDerivAt)
open ImbalancedChen.Part3.OriginalFullModulusSupport20261102

namespace ImbalancedChen.Part3.OriginalFullModulusTestJets20261102

attribute [local instance] Classical.propDecidable

/-- Strict support follows from the ACTUAL bump's topological support,
not just by closing the coarser open support interval. -/
theorem spectralTest_tsupport_strict (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    tsupport (spectralTest ell Y) ⊆ Ioo (Y / 16) (16 * Y) := by
  have hs : tsupport (spectralTest ell Y) ⊆
      (fun q : ℝ => q / Y) ⁻¹' tsupport chi := by
    apply closure_minimal _ (isClosed_closure.preimage (continuous_id.div_const Y))
    intro q hq
    apply subset_closure
    intro hz
    exact hq (by simp only [spectralTest, spectralMode, hz, Complex.ofReal_zero, zero_mul])
  intro q hq
  have ht := chi_tsupport_subset (hs hq)
  exact ⟨by have := (lt_div_iff₀ hY).mp ht.1; linarith,
    (div_lt_iff₀ hY).mp ht.2⟩

private theorem iteratedDeriv_tsupport_subset (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using (Subset.rfl : tsupport f ⊆ tsupport f)
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- Every endpoint jet vanishes, at q=0 as well as at both advertised
support endpoints. The statement includes order zero and all fixed n. -/
theorem spectralTest_all_endpoint_jets (ell : D4 → ℤ) {Y q : ℝ} (hY : 0 < Y)
    (hq : q ≤ Y / 16 ∨ 16 * Y ≤ q) (n : ℕ) :
    iteratedDeriv n (spectralTest ell Y) q = 0 := by
  by_contra hne
  have ht := spectralTest_tsupport_strict ell hY
    (iteratedDeriv_tsupport_subset (spectralTest ell Y) n (subset_closure hne))
  rcases hq with hq | hq <;> linarith [ht.1, ht.2]

theorem spectralTest_integrable (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    Integrable (spectralTest ell Y) :=
  (spectralTest_contDiff ell Y).continuous.integrable_of_hasCompactSupport
    (spectralTest_compact ell hY)

/-- The dq/q measure in each native Bessel transform is harmless at
the zero endpoint because the actual test has a whole zero collar. -/
theorem spectralTest_div_q_integrable (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun q : ℝ => spectralTest ell Y q / (q : ℂ)) := by
  let F : ℝ → ℂ := fun q => spectralTest ell Y q / ((max (Y / 32) q : ℝ) : ℂ)
  have hden (q : ℝ) : (0 : ℝ) < max (Y / 32) q :=
    (by positivity : (0 : ℝ) < Y / 32).trans_le (le_max_left _ _)
  have hcont : Continuous F := by
    apply (spectralTest_contDiff ell Y).continuous.div
      (Complex.continuous_ofReal.comp (continuous_const.max continuous_id))
    intro q
    exact_mod_cast (hden q).ne'
  have hsupport : HasCompactSupport F := by
    apply (isCompact_Icc : IsCompact (Icc (Y / 16) (16 * Y)))
      .of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_Icc
    intro q hq
    have hn : spectralTest ell Y q ≠ 0 := by
      intro hz
      exact hq (by dsimp [F]; rw [hz, zero_div])
    exact ⟨(spectralTest_support ell hY hn).1.le, (spectralTest_support ell hY hn).2.le⟩
  have heq : (fun q : ℝ => spectralTest ell Y q / (q : ℂ)) = F := by
    funext q
    by_cases hn : spectralTest ell Y q = 0
    · simp only [F, hn, zero_div]
    · have hq := (spectralTest_support ell hY hn).1
      have hmax : max (Y / 32) q = q := max_eq_right (by linarith)
      simp only [F, hmax]
  rw [heq]
  exact hcont.integrable_of_hasCompactSupport hsupport

def complexChi (t : ℝ) : ℂ := (chi t : ℂ)
def nativePhase (ell : D4 → ℤ) (t : ℝ) : ℂ := e ((ell 0 : ℝ) / 64 * t)

theorem complexChi_contDiff : ContDiff ℝ ∞ complexChi :=
  Complex.ofRealCLM.contDiff.comp chi_contDiff

theorem nativePhase_contDiff (ell : D4 → ℤ) : ContDiff ℝ ∞ (nativePhase ell) := by
  unfold nativePhase e
  fun_prop

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
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (1 / 16 : ℝ) 16))
    .exists_bound_of_continuousOn hc.continuousOn
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

/-- Absolute Fourier summability retains the derivative loss explicitly.
The summable majorant is the previously proved native order-n weight,
multiplied by the displayed fixed-cutoff/Y factor. -/
theorem actual_weighted_test_jets_summable (rho sigma : ℝ) (n : ℕ)
    {Y : ℝ} (hY : 0 < Y) (q : ℝ) :
    Summable (fun ell : D4 → ℤ => ‖actualCoeff rho sigma ell‖ *
      ‖iteratedDeriv n (spectralTest ell Y) q‖) := by
  apply ((actual_mode_weight_summable rho sigma n).mul_left
    (testJetConstant n / Y ^ n)).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro ell
  calc
    ‖actualCoeff rho sigma ell‖ * ‖iteratedDeriv n (spectralTest ell Y) q‖ ≤
        ‖actualCoeff rho sigma ell‖ *
          (testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n / Y ^ n) :=
      mul_le_mul_of_nonneg_left (spectralTest_jet_bound n ell hY q) (norm_nonneg _)
    _ = _ := by ring

/-- The full derivative mass is charged to the exact pre-existing W_n,
so the caller sees both Y^{-n} and the native polynomial mode weight. -/
theorem actual_weighted_test_jets_budget (rho sigma : ℝ) (n : ℕ)
    {Y : ℝ} (hY : 0 < Y) (q : ℝ) :
    (∑' ell : D4 → ℤ, ‖actualCoeff rho sigma ell‖ *
      ‖iteratedDeriv n (spectralTest ell Y) q‖) ≤
        (testJetConstant n / Y ^ n) *
          P3ActualWeightedSpectralBudgetSourceOnly.actualW rho sigma n := by
  have hs := actual_mode_weight_summable rho sigma n
  have hmajor := hs.mul_left (testJetConstant n / Y ^ n)
  have hpoint (ell : D4 → ℤ) :
      ‖actualCoeff rho sigma ell‖ * ‖iteratedDeriv n (spectralTest ell Y) q‖ ≤
        (testJetConstant n / Y ^ n) *
          (‖actualCoeff rho sigma ell‖ * (1 + |(ell 0 : ℝ)|) ^ n) := by
    calc
      _ ≤ ‖actualCoeff rho sigma ell‖ *
          (testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n / Y ^ n) :=
        mul_le_mul_of_nonneg_left (spectralTest_jet_bound n ell hY q) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑' ell : D4 → ℤ, (testJetConstant n / Y ^ n) *
        (‖actualCoeff rho sigma ell‖ * (1 + |(ell 0 : ℝ)|) ^ n) :=
      (actual_weighted_test_jets_summable rho sigma n hY q).tsum_le_tsum hpoint hmajor
    _ = _ := by
      rw [hs.tsum_mul_left]
      rfl

/-- All constants precede rho,sigma,Y,q; order n is fixed first. This
consumes the existing uniform derivative-mass/Fourier-lattice supplier,
and adds no new power beyond its already stated 4*(n+3) rho cost. -/
theorem actual_uniform_test_jets_budget (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
      ∀ Y : ℝ, 0 < Y → ∀ q : ℝ,
      (∑' ell : D4 → ℤ, ‖actualCoeff rho sigma ell‖ *
        ‖iteratedDeriv n (spectralTest ell Y) q‖) ≤
          C * (1 + rho) ^ (4 * (n + 3)) / Y ^ n := by
  obtain ⟨A, hA, hbudget⟩ :=
    P3ActualWeightedSpectralBudgetSourceOnly.actual_uniform_weighted_l1 n
  refine ⟨testJetConstant n * A, mul_pos (testJetConstant_pos n) hA, ?_⟩
  intro rho hrho sigma hsigma Y hY q
  calc
    _ ≤ (testJetConstant n / Y ^ n) *
        P3ActualWeightedSpectralBudgetSourceOnly.actualW rho sigma n :=
      actual_weighted_test_jets_budget rho sigma n hY q
    _ ≤ (testJetConstant n / Y ^ n) * (A * (1 + rho) ^ (4 * (n + 3))) :=
      mul_le_mul_of_nonneg_left (hbudget rho hrho sigma hsigma).2
        (div_nonneg (testJetConstant_pos n).le (pow_nonneg hY.le n))
    _ = _ := by ring

end ImbalancedChen.Part3.OriginalFullModulusTestJets20261102
end
