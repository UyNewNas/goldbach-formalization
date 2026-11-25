import ImbalancedChen.Part3ActualSpectralTestJets

/-!
# Fourier cost of the actual per-mode test seminorm

For each Fourier mode and derivative order the supremum is over the whole
real test variable. The cutoff constant is selected declaration reuse from
the historical finite test budget. Only that constant and its positivity
proof are retained here.
-/

noncomputable section
open Finset
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff spectralTest)
open P3ActualWeightedSpectralBudgetSourceOnly (actual_uniform_weighted_l1 actualW)
open ImbalancedChen.Part3.OriginalFullModulusTestJets20261102
  (spectralTest_jet_bound testJetConstant testJetConstant_pos)

namespace ImbalancedChen.Part3.OriginalUniformTestCutoffBudget20261102

def finiteTestJetConstant (d : ℕ) : ℝ :=
  1 + ∑ n ∈ range (d + 1), testJetConstant n

theorem finiteTestJetConstant_pos (d : ℕ) : 0 < finiteTestJetConstant d := by
  have hs : 0 ≤ ∑ n ∈ range (d + 1), testJetConstant n :=
    sum_nonneg (fun n _ => (testJetConstant_pos n).le)
  unfold finiteTestJetConstant
  linarith

end ImbalancedChen.Part3.OriginalUniformTestCutoffBudget20261102

namespace ImbalancedChen.Part3.ActualSpectralTestSeminorm
open ImbalancedChen.Part3.OriginalUniformTestCutoffBudget20261102
  (finiteTestJetConstant finiteTestJetConstant_pos)

def normalizedJetSup (n : ℕ) (ell : D4 → ℤ) (Y : ℝ) : ℝ :=
  sSup (Set.range (fun q : ℝ => Y ^ n * ‖iteratedDeriv n (spectralTest ell Y) q‖))

theorem normalizedJetRange_nonempty (n : ℕ) (ell : D4 → ℤ) (Y : ℝ) :
    (Set.range (fun q : ℝ => Y ^ n * ‖iteratedDeriv n (spectralTest ell Y) q‖)).Nonempty :=
  ⟨_, 0, rfl⟩

private theorem normalizedJet_le (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (q : ℝ) :
    Y ^ n * ‖iteratedDeriv n (spectralTest ell Y) q‖ ≤
      testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n := by
  simpa only [mul_comm (Y ^ n)] using
    (le_div_iff₀ (pow_pos hY n)).mp (spectralTest_jet_bound n ell hY q)

theorem normalizedJetRange_bddAbove (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    BddAbove (Set.range (fun q : ℝ => Y ^ n * ‖iteratedDeriv n (spectralTest ell Y) q‖)) := by
  refine ⟨testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact normalizedJet_le n ell hY q

theorem le_normalizedJetSup (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (q : ℝ) :
    Y ^ n * ‖iteratedDeriv n (spectralTest ell Y) q‖ ≤ normalizedJetSup n ell Y :=
  le_csSup (normalizedJetRange_bddAbove n ell hY) ⟨q, rfl⟩

theorem normalizedJetSup_nonneg (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    0 ≤ normalizedJetSup n ell Y :=
  (mul_nonneg (pow_nonneg hY.le n) (norm_nonneg _)).trans (le_normalizedJetSup n ell hY 0)

theorem normalizedJetSup_le (n : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    normalizedJetSup n ell Y ≤ testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ n := by
  apply csSup_le (normalizedJetRange_nonempty n ell Y)
  rintro _ ⟨q, rfl⟩
  exact normalizedJet_le n ell hY q

def testSeminorm (d : ℕ) (ell : D4 → ℤ) (Y : ℝ) : ℝ :=
  ∑ n ∈ range (d + 1), normalizedJetSup n ell Y

theorem testSeminorm_nonneg (d : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    0 ≤ testSeminorm d ell Y :=
  sum_nonneg (fun n _ => normalizedJetSup_nonneg n ell hY)

theorem testSeminorm_le (d : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    testSeminorm d ell Y ≤ finiteTestJetConstant d * (1 + |(ell 0 : ℝ)|) ^ d := by
  have hbase : 1 ≤ 1 + |(ell 0 : ℝ)| := by linarith [abs_nonneg (ell 0 : ℝ)]
  calc
    _ ≤ ∑ n ∈ range (d + 1), testJetConstant n * (1 + |(ell 0 : ℝ)|) ^ d := by
      apply sum_le_sum
      intro n hn
      have hnd : n ≤ d := Nat.le_of_lt_succ (mem_range.mp hn)
      exact (normalizedJetSup_le n ell hY).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hbase hnd) (testJetConstant_pos n).le)
    _ = (∑ n ∈ range (d + 1), testJetConstant n) * (1 + |(ell 0 : ℝ)|) ^ d := by
      rw [Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hbase) d)
      unfold finiteTestJetConstant
      linarith

/-- Each Fourier mode pays for the suprema of its own normalized derivatives
through order d. The constant is uniform in rho, sigma and Y. -/
theorem actual_uniform_testSeminorm_budget (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
      ∀ Y : ℝ, 0 < Y →
        Summable (fun ell : D4 → ℤ => ‖actualCoeff rho sigma ell‖ * testSeminorm d ell Y) ∧
        (∑' ell : D4 → ℤ, ‖actualCoeff rho sigma ell‖ * testSeminorm d ell Y) ≤
          C * (1 + rho) ^ (4 * (d + 3)) := by
  obtain ⟨A, hA, hbudget⟩ := actual_uniform_weighted_l1 d
  refine ⟨finiteTestJetConstant d * A, mul_pos (finiteTestJetConstant_pos d) hA, ?_⟩
  intro rho hrho sigma hsigma Y hY
  obtain ⟨hweight, hcost⟩ := hbudget rho hrho sigma hsigma
  change Summable (fun ell : D4 → ℤ => ‖actualCoeff rho sigma ell‖ *
    (1 + |(ell 0 : ℝ)|) ^ d) at hweight
  have hmajor := hweight.mul_left (finiteTestJetConstant d)
  have hpoint (ell : D4 → ℤ) :
      ‖actualCoeff rho sigma ell‖ * testSeminorm d ell Y ≤
        finiteTestJetConstant d * (‖actualCoeff rho sigma ell‖ * (1 + |(ell 0 : ℝ)|) ^ d) := by
    calc
      _ ≤ ‖actualCoeff rho sigma ell‖ * (finiteTestJetConstant d * (1 + |(ell 0 : ℝ)|) ^ d) :=
        mul_le_mul_of_nonneg_left (testSeminorm_le d ell hY) (norm_nonneg _)
      _ = _ := by ring
  have hsum : Summable (fun ell : D4 → ℤ => ‖actualCoeff rho sigma ell‖ * testSeminorm d ell Y) :=
    hmajor.of_nonneg_of_le (fun ell => mul_nonneg (norm_nonneg _) (testSeminorm_nonneg d ell hY)) hpoint
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' ell : D4 → ℤ, finiteTestJetConstant d *
        (‖actualCoeff rho sigma ell‖ * (1 + |(ell 0 : ℝ)|) ^ d) :=
      hsum.tsum_le_tsum hpoint hmajor
    _ = finiteTestJetConstant d * actualW rho sigma d := by
      rw [hweight.tsum_mul_left]
      rfl
    _ ≤ finiteTestJetConstant d * (A * (1 + rho) ^ (4 * (d + 3))) :=
      mul_le_mul_of_nonneg_left hcost (finiteTestJetConstant_pos d).le
    _ = _ := by ring

end ImbalancedChen.Part3.ActualSpectralTestSeminorm
end
