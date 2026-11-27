import ImbalancedChen.Part3ActualSpectralTestSeminorm

/-!
# A uniformly normalized family of the actual Fourier tests

The manuscript-cited Drappeau Lemma 4.4 requires only derivatives through
order four. This module proves that the actual period-64 tests, divided by
a positive mode-dependent cost, belong to its fixed-support unit test class.
The cost is independent of the moving scale and is paid by the already
proved actual Fourier weighted budget. No Bessel estimate is a premise or
a conclusion of this module.
-/

noncomputable section

open Set Finset
open scoped BigOperators ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (actualCoeff spectralTest spectralMode spectralMode_support_subset spectralTest_contDiff)
open P3ActualWeightedSpectralBudgetSourceOnly (actual_uniform_weighted_l1 actualW)
open ImbalancedChen.Part3.ActualSpectralTestSeminorm
  (normalizedJetSup normalizedJetSup_nonneg le_normalizedJetSup testSeminorm testSeminorm_le)
open ImbalancedChen.Part3.OriginalUniformTestCutoffBudget20261102
  (finiteTestJetConstant finiteTestJetConstant_pos)

namespace ImbalancedChen.Part3.ActualSpectralTestNormalization

/-- The external unit class uses one fixed support ratio for all scales.
Smoothness is global, as required by the compactly supported test convention. -/
def UnitTest (d : ℕ) (Y : ℝ) (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ Icc (Y / 16) (16 * Y) ∧
    ∀ n : ℕ, n ≤ d → ∀ q : ℝ, Y ^ n * ‖iteratedDeriv n φ q‖ ≤ 1

/-- Chosen before the scale Y; strictly positive also at the zero mode. -/
def normalization (d : ℕ) (ell : D4 → ℤ) : ℝ :=
  finiteTestJetConstant d * (1 + |(ell 0 : ℝ)|) ^ d

theorem normalization_pos (d : ℕ) (ell : D4 → ℤ) : 0 < normalization d ell := by
  unfold normalization
  exact mul_pos (finiteTestJetConstant_pos d) (pow_pos (by positivity) d)

def normalizedTest (d : ℕ) (ell : D4 → ℤ) (Y q : ℝ) : ℂ :=
  Complex.ofReal ((normalization d ell)⁻¹) * spectralTest ell Y q

theorem normalizedTest_contDiff (d : ℕ) (ell : D4 → ℤ) (Y : ℝ) :
    ContDiff ℝ ∞ (normalizedTest d ell Y) :=
  contDiff_const.mul (spectralTest_contDiff ell Y)

/-- Multiplication by the positive normalization returns the same actual test. -/
theorem normalizedTest_reconstruct (d : ℕ) (ell : D4 → ℤ) (Y q : ℝ) :
    (normalization d ell : ℂ) * normalizedTest d ell Y q = spectralTest ell Y q := by
  unfold normalizedTest
  rw [← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (normalization_pos d ell).ne', Complex.ofReal_one, one_mul]

theorem normalizedTest_support_subset (d : ℕ) (ell : D4 → ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    Function.support (normalizedTest d ell Y) ⊆ Ioo (Y / 16) (16 * Y) := by
  intro q hq
  have hmode : spectralMode ell (q / Y) ≠ 0 := by
    intro hz
    exact hq (by simp only [normalizedTest, spectralTest, hz, mul_zero])
  have hs := spectralMode_support_subset ell hmode
  constructor
  · have hh := (lt_div_iff₀ hY).mp hs.1
    nlinarith
  · exact (div_lt_iff₀ hY).mp hs.2

theorem normalizedTest_tsupport_subset (d : ℕ) (ell : D4 → ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    tsupport (normalizedTest d ell Y) ⊆ Icc (Y / 16) (16 * Y) := by
  apply closure_minimal _ isClosed_Icc
  intro q hq
  exact ⟨(normalizedTest_support_subset d ell hY hq).1.le,
    (normalizedTest_support_subset d ell hY hq).2.le⟩

theorem normalizedTest_hasCompactSupport (d : ℕ) (ell : D4 → ℤ)
    {Y : ℝ} (hY : 0 < Y) : HasCompactSupport (normalizedTest d ell Y) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (normalizedTest_tsupport_subset d ell hY)

/-- Every normalized derivative is bounded before the mode or scale is chosen. -/
theorem normalizedTest_jet_le_one (d : ℕ) (ell : D4 → ℤ)
    {Y : ℝ} (hY : 0 < Y) (n : ℕ) (hn : n ≤ d) (q : ℝ) :
    Y ^ n * ‖iteratedDeriv n (normalizedTest d ell Y) q‖ ≤ 1 := by
  have hsingle : normalizedJetSup n ell Y ≤ testSeminorm d ell Y := by
    exact Finset.single_le_sum (fun i _ => normalizedJetSup_nonneg i ell hY)
      (Finset.mem_range.mpr (by omega))
  have hbound : Y ^ n * ‖iteratedDeriv n (spectralTest ell Y) q‖ ≤ normalization d ell :=
    (le_normalizedJetSup n ell hY q).trans (hsingle.trans (testSeminorm_le d ell hY))
  have hnorm : ‖Complex.ofReal ((normalization d ell)⁻¹)‖ = (normalization d ell)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (normalization_pos d ell))]
  change Y ^ n * ‖iteratedDeriv n
    (fun q => Complex.ofReal ((normalization d ell)⁻¹) * spectralTest ell Y q) q‖ ≤ 1
  rw [iteratedDeriv_const_mul_field, norm_mul, hnorm]
  calc
    Y ^ n * ((normalization d ell)⁻¹ * ‖iteratedDeriv n (spectralTest ell Y) q‖) =
        (normalization d ell)⁻¹ * (Y ^ n * ‖iteratedDeriv n (spectralTest ell Y) q‖) := by ring
    _ ≤ (normalization d ell)⁻¹ * normalization d ell :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (normalization_pos d ell).le)
    _ = 1 := inv_mul_cancel₀ (normalization_pos d ell).ne'

theorem normalizedTest_mem_unitTest (d : ℕ) (ell : D4 → ℤ)
    {Y : ℝ} (hY : 0 < Y) : UnitTest d Y (normalizedTest d ell Y) :=
  ⟨normalizedTest_contDiff d ell Y, normalizedTest_tsupport_subset d ell hY,
    normalizedTest_jet_le_one d ell hY⟩

/-- The exact normalization, rather than a modewise unspecified constant,
has a summable actual Fourier cost uniform in the moving physical parameters. -/
theorem actual_uniform_normalization_budget (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
      Summable (fun ell : D4 → ℤ => ‖actualCoeff rho sigma ell‖ * normalization d ell) ∧
        (∑' ell : D4 → ℤ, ‖actualCoeff rho sigma ell‖ * normalization d ell) ≤
          C * (1 + rho) ^ (4 * (d + 3)) := by
  obtain ⟨A, hA, hbudget⟩ := actual_uniform_weighted_l1 d
  refine ⟨finiteTestJetConstant d * A, mul_pos (finiteTestJetConstant_pos d) hA, ?_⟩
  intro rho hrho sigma hsigma
  obtain ⟨hs, hb⟩ := hbudget rho hrho sigma hsigma
  change Summable (fun ell : D4 → ℤ =>
    ‖actualCoeff rho sigma ell‖ * (1 + |(ell 0 : ℝ)|) ^ d) at hs
  have heq (ell : D4 → ℤ) : ‖actualCoeff rho sigma ell‖ * normalization d ell =
      finiteTestJetConstant d * (‖actualCoeff rho sigma ell‖ * (1 + |(ell 0 : ℝ)|) ^ d) := by
    unfold normalization
    ring
  refine ⟨(hs.mul_left (finiteTestJetConstant d)).congr (fun ell => (heq ell).symm), ?_⟩
  calc
    _ = finiteTestJetConstant d * actualW rho sigma d := by
      simp_rw [heq]
      rw [tsum_mul_left]
      rfl
    _ ≤ finiteTestJetConstant d * (A * (1 + rho) ^ (4 * (d + 3))) :=
      mul_le_mul_of_nonneg_left hb (finiteTestJetConstant_pos d).le
    _ = _ := by ring

/-- The sufficient order is supplied by Drappeau Lemma 4.4. This corollary
only instantiates the proved actual Fourier cost; it does not assert the
external Bessel estimate. -/
theorem actual_uniform_C4_normalization_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
      Summable (fun ell : D4 → ℤ => ‖actualCoeff rho sigma ell‖ * normalization 4 ell) ∧
        (∑' ell : D4 → ℤ, ‖actualCoeff rho sigma ell‖ * normalization 4 ell) ≤
          C * (1 + rho) ^ 28 := by
  simpa only [show 4 * (4 + 3) = 28 from rfl] using actual_uniform_normalization_budget 4

end ImbalancedChen.Part3.ActualSpectralTestNormalization
end
