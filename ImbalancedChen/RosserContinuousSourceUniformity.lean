import ImbalancedChen.ActualRosserEvenSourceSeries
import ImbalancedChen.RosserGlobalSourceIdentity
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Uniform tails and continuity of the genuine continuous Rosser source

Each nonnegative layer decreases on its exact parity domain. Its value at
the left endpoint therefore supplies a summable majorant for the whole
half-line. The endpoint summability is supplied by the proved concrete JR
source contract. The M-test gives uniform convergence and continuity of
the canonical Suzuki factors, with no discrete density or uniform-tail
hypothesis. The odd endpoint must exceed one; the even endpoint may equal
two. No replacement by a finite-interval formula for another factor occurs.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

private theorem mem_odd_source_parityDomain {s : ℝ} (hs : 1 < s) (k : ℕ) :
    s ∈ suzukiParityDomainOne 2 (2 * k + 1) := by
  simp [suzukiParityDomainOne, KappaOneModel.parityDomain]
  linarith

private theorem mem_even_source_parityDomain {s : ℝ} (hs : 2 ≤ s) (k : ℕ) :
    s ∈ suzukiParityDomainOne 2 (2 * (k + 1)) := by
  simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hs

/-- A single endpoint value dominates an odd layer on the entire half-line. -/
theorem suzukiOddSourceLayer_norm_le_at_left {sigma s : ℝ}
    (hsigma : 1 < sigma) (hs : sigma ≤ s) (k : ℕ) :
    ‖suzukiLayer 1 2 (2 * k + 1) s‖ ≤ suzukiLayer 1 2 (2 * k + 1) sigma := by
  rw [Real.norm_eq_abs, abs_of_nonneg (suzukiLayer_one_two_odd_nonneg (hsigma.trans_le hs) k)]
  exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * k + 1)
    (mem_odd_source_parityDomain hsigma k)
    (mem_odd_source_parityDomain (hsigma.trans_le hs) k) hs

/-- The closed lower endpoint two is allowed in the even-layer majorant. -/
theorem suzukiEvenSourceLayer_norm_le_at_left {sigma s : ℝ}
    (hsigma : 2 ≤ sigma) (hs : sigma ≤ s) (k : ℕ) :
    ‖suzukiLayer 1 2 (2 * (k + 1)) s‖ ≤ suzukiLayer 1 2 (2 * (k + 1)) sigma := by
  rw [Real.norm_eq_abs, abs_of_nonneg (suzukiLayer_one_two_even_nonneg (hsigma.trans hs) k)]
  exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * (k + 1))
    (mem_even_source_parityDomain hsigma k)
    (mem_even_source_parityDomain (hsigma.trans hs) k) hs

theorem continuousOn_suzukiOddSourceLayer_Ici (k : ℕ) {sigma : ℝ}
    (hsigma : 1 < sigma) :
    ContinuousOn (suzukiLayer 1 2 (2 * k + 1)) (Set.Ici sigma) := by
  apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num) (2 * k + 1)).mono
  intro s hs
  exact mem_odd_source_parityDomain (hsigma.trans_le hs) k

theorem continuousOn_suzukiEvenSourceLayer_Ici (k : ℕ) {sigma : ℝ}
    (hsigma : 2 ≤ sigma) :
    ContinuousOn (suzukiLayer 1 2 (2 * (k + 1))) (Set.Ici sigma) := by
  apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num) (2 * (k + 1))).mono
  intro s hs
  exact mem_even_source_parityDomain (hsigma.trans hs) k

/-- The actual odd source series converges uniformly on every closed
half-line strictly above one, not just on bounded intervals. -/
theorem tendstoUniformlyOn_suzukiOddSourcePartialSum {sigma : ℝ}
    (hsigma : 1 < sigma) :
    TendstoUniformlyOn
      (fun m : ℕ => fun s : ℝ => ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * k + 1) s)
      suzukiProposition118SourceTPlus atTop (Set.Ici sigma) := by
  exact tendstoUniformlyOn_tsum_nat
    (summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract hsigma)
    (fun k s hs => suzukiOddSourceLayer_norm_le_at_left hsigma hs k)

/-- The genuine even source series has a uniform tail on `[sigma,infinity)`
for every `sigma >= 2`, including the source's lower endpoint. -/
theorem tendstoUniformlyOn_suzukiEvenSourcePartialSum {sigma : ℝ}
    (hsigma : 2 ≤ sigma) :
    TendstoUniformlyOn
      (fun m : ℕ => fun s : ℝ => ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * (k + 1)) s)
      suzukiProposition118SourceTMinus atTop (Set.Ici sigma) := by
  exact tendstoUniformlyOn_tsum_nat
    (summable_suzukiProposition118SourceTMinus_of_sourceContract
      jr1965Section13HatSourceContract hsigma)
    (fun k s hs => suzukiEvenSourceLayer_norm_le_at_left hsigma hs k)

theorem continuousOn_suzukiProposition118SourceTPlus_Ici {sigma : ℝ}
    (hsigma : 1 < sigma) :
    ContinuousOn suzukiProposition118SourceTPlus (Set.Ici sigma) := by
  exact continuousOn_tsum (fun k => continuousOn_suzukiOddSourceLayer_Ici k hsigma)
    (summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract hsigma)
    (fun k s hs => suzukiOddSourceLayer_norm_le_at_left hsigma hs k)

theorem continuousOn_suzukiProposition118SourceTMinus_Ici {sigma : ℝ}
    (hsigma : 2 ≤ sigma) :
    ContinuousOn suzukiProposition118SourceTMinus (Set.Ici sigma) := by
  exact continuousOn_tsum (fun k => continuousOn_suzukiEvenSourceLayer_Ici k hsigma)
    (summable_suzukiProposition118SourceTMinus_of_sourceContract
      jr1965Section13HatSourceContract hsigma)
    (fun k s hs => suzukiEvenSourceLayer_norm_le_at_left hsigma hs k)

/-- Continuity of the canonical upper factor on its full legal domain. -/
theorem continuousOn_suzukiContinuousUpperFactor :
    ContinuousOn suzukiContinuousUpperFactor (Set.Ioi 1) := by
  have hsource : ContinuousOn suzukiProposition118SourceTPlus (Set.Ioi 1) := by
    intro s hs
    have hleft : 1 < (1 + s) / 2 := by change 1 < s at hs; linarith
    have hinside : (1 + s) / 2 < s := by change 1 < s at hs; linarith
    exact ((continuousOn_suzukiProposition118SourceTPlus_Ici hleft).continuousAt
      (Ici_mem_nhds hinside)).continuousWithinAt
  exact continuousOn_const.add hsource

/-- Continuity of the canonical lower factor, retaining the endpoint two. -/
theorem continuousOn_suzukiContinuousLowerFactor :
    ContinuousOn suzukiContinuousLowerFactor (Set.Ici 2) := by
  exact continuousOn_const.sub
    (continuousOn_suzukiProposition118SourceTMinus_Ici (by norm_num : (2 : ℝ) ≤ 2))

/-- A uniform finite prefix for the canonical upper factor. The prefix
threshold precedes every real residual in the whole legal half-line. -/
theorem exists_suzukiOddSourcePartialSum_uniform_threshold {sigma : ℝ}
    (hsigma : 1 < sigma) (eta : ℝ) (heta : 0 < eta) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ s : ℝ, sigma ≤ s →
      |(1 + ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * k + 1) s) -
        suzukiContinuousUpperFactor s| < eta := by
  have h := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_suzukiOddSourcePartialSum hsigma) eta heta
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp h
  refine ⟨m0, fun m hm s hs => ?_⟩
  have hms := hm0 m hm s hs
  simpa only [Real.dist_eq, suzukiContinuousUpperFactor, add_sub_add_left_eq_sub,
    abs_sub_comm] using hms

/-- The same uniform finite-prefix statement for one minus the even loss. -/
theorem exists_suzukiEvenSourcePartialSum_uniform_threshold {sigma : ℝ}
    (hsigma : 2 ≤ sigma) (eta : ℝ) (heta : 0 < eta) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ s : ℝ, sigma ≤ s →
      |(1 - ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * (k + 1)) s) -
        suzukiContinuousLowerFactor s| < eta := by
  have h := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_suzukiEvenSourcePartialSum hsigma) eta heta
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp h
  refine ⟨m0, fun m hm s hs => ?_⟩
  have hms := hm0 m hm s hs
  simpa only [Real.dist_eq, suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    sub_sub_sub_cancel_left, abs_sub_comm] using hms

/-- The actual odd-region integrals inherit the uniform source-series tail. -/
theorem tendstoUniformlyOn_rosserOddLayerIntegral_partialSum {sigma : ℝ}
    (hsigma : 1 < sigma) :
    TendstoUniformlyOn
      (fun m : ℕ => fun s : ℝ => ∑ k ∈ Finset.range m, rosserOddLayerIntegral k s)
      suzukiProposition118SourceTPlus atTop (Set.Ici sigma) := by
  apply (tendstoUniformlyOn_suzukiOddSourcePartialSum hsigma).congr
  filter_upwards [] with m
  intro s hs
  apply Finset.sum_congr rfl
  intro k _hk
  exact (rosserOddLayerIntegral_eq_suzukiLayer_of_pos k s
    (lt_of_lt_of_le (by linarith : 0 < sigma) hs)).symm

/-- The actual even-region integrals inherit the tail including `sigma=2`. -/
theorem tendstoUniformlyOn_rosserEvenLayerIntegral_partialSum {sigma : ℝ}
    (hsigma : 2 ≤ sigma) :
    TendstoUniformlyOn
      (fun m : ℕ => fun s : ℝ => ∑ k ∈ Finset.range m, rosserEvenLayerIntegral k s)
      suzukiProposition118SourceTMinus atTop (Set.Ici sigma) := by
  apply (tendstoUniformlyOn_suzukiEvenSourcePartialSum hsigma).congr
  filter_upwards [] with m
  intro s hs
  apply Finset.sum_congr rfl
  intro k _hk
  exact (rosserEvenLayerIntegral_eq_suzukiLayer k s (hsigma.trans hs)).symm

/-- One finite prefix of actual odd-region integrals approximates the
canonical upper factor throughout the same half-line. -/
theorem exists_rosserOddLayerIntegral_partialSum_uniform_threshold {sigma : ℝ}
    (hsigma : 1 < sigma) (eta : ℝ) (heta : 0 < eta) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ s : ℝ, sigma ≤ s →
      |(1 + ∑ k ∈ Finset.range m, rosserOddLayerIntegral k s) -
        suzukiContinuousUpperFactor s| < eta := by
  obtain ⟨m0, hm0⟩ := exists_suzukiOddSourcePartialSum_uniform_threshold hsigma eta heta
  refine ⟨m0, fun m hm s hs => ?_⟩
  simpa only [rosserOddLayerIntegral_eq_suzukiLayer_of_pos _ s
    (show 0 < s by linarith)] using hm0 m hm s hs

/-- One finite prefix of actual even losses suffices uniformly, including
the lower boundary `sigma = 2`. -/
theorem exists_rosserEvenLayerIntegral_partialSum_uniform_threshold {sigma : ℝ}
    (hsigma : 2 ≤ sigma) (eta : ℝ) (heta : 0 < eta) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ s : ℝ, sigma ≤ s →
      |(1 - ∑ k ∈ Finset.range m, rosserEvenLayerIntegral k s) -
        suzukiContinuousLowerFactor s| < eta := by
  obtain ⟨m0, hm0⟩ := exists_suzukiEvenSourcePartialSum_uniform_threshold hsigma eta heta
  refine ⟨m0, fun m hm s hs => ?_⟩
  simpa only [rosserEvenLayerIntegral_eq_suzukiLayer _ s (hsigma.trans hs)] using hm0 m hm s hs

end

end ImbalancedChen
