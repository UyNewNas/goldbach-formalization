import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenAdaptiveDepthAbsorption
import Mathlib.Topology.Order.Compact

/-!
# Compact-parameter absorption of the literal all-depth Rosser error

The two continuous Section 13 hat layers have one bound on any positive
compact interval.  The depth only selects one of those two layers.  Bounding
the perturbation by `2 ^ b` therefore gives one logarithmic-decay threshold
for every depth and every `s ∈ [a,b]`.  This is a scalar error theorem; it
does not assert uniformity of the actual discrete Rosser densities.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- One nonnegative bound controls both hat layers on a positive compact interval. -/
theorem exists_section13Hat_compact_bound
    (H : Section13HatLayers) {β a b : ℝ}
    (hH : Section13HatContract H β) (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ sign : ErrorSign, ∀ s ∈ Icc a b, H.T sign s ≤ M := by
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun _ hs => ha.trans_le hs.1
  obtain ⟨Mp, hMp⟩ := isCompact_Icc.bddAbove_image ((hH.continuous .plus).mono hsub)
  obtain ⟨Mm, hMm⟩ := isCompact_Icc.bddAbove_image ((hH.continuous .minus).mono hsub)
  refine ⟨max 0 (max Mp Mm), le_max_left _ _, ?_⟩
  intro sign s hs
  cases sign with
  | plus =>
    exact (hMp (mem_image_of_mem _ hs)).trans
      ((le_max_left Mp Mm).trans (le_max_right 0 _))
  | minus =>
    exact (hMm (mem_image_of_mem _ hs)).trans
      ((le_max_right Mp Mm).trans (le_max_right 0 _))

/-- A compact interval bound for the literal envelope is independent of depth. -/
theorem exists_all_depth_errorEnvelope_compact_bound
    (H : Section13HatLayers) {β a b d : ℝ}
    (hH : Section13HatContract H β) (ha : 0 < a) (hab : a ≤ b)
    (hd : 0 ≤ d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ D : ℝ, 1 < D → b ^ d ≤ Real.log D →
      ∀ depth : ℕ, ∀ s ∈ Icc a b,
        0 ≤ errorEnvelope H depth D d s ∧ errorEnvelope H depth D d s ≤ B := by
  obtain ⟨M, hM0, hM⟩ := exists_section13Hat_compact_bound H hH ha
  refine ⟨(2 : ℝ) ^ b * b * M, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (ha.le.trans hab)) hM0
  intro D hD hlog depth s hs
  have hspos : 0 < s := ha.trans_le hs.1
  have hlogpos : 0 < Real.log D := Real.log_pos hD
  have hsd : s ^ d ≤ b ^ d := Real.rpow_le_rpow hspos.le hs.2 hd
  have hratio : s ^ d / Real.log D ≤ 1 :=
    (div_le_one hlogpos).2 (hsd.trans hlog)
  have hbase0 : 0 ≤ 1 + s ^ d / Real.log D := by positivity
  have hperturb : (1 + s ^ d / Real.log D) ^ s ≤ (2 : ℝ) ^ b := by
    calc
      (1 + s ^ d / Real.log D) ^ s ≤ (2 : ℝ) ^ s :=
        Real.rpow_le_rpow hbase0 (by linarith) hspos.le
      _ ≤ (2 : ℝ) ^ b :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hs.2
  have hT0 : 0 ≤ H.T (ErrorSign.ofDepth depth) s :=
    (hH.positive _ s hspos).le
  refine ⟨errorEnvelope_nonneg H depth hD hspos.le hT0, ?_⟩
  simp only [errorEnvelope, Section13HatLayers.kappaHat,
    sub_self, zero_add, Real.rpow_one]
  exact mul_le_mul
    (mul_le_mul hperturb hs.2 hspos.le (Real.rpow_nonneg (by norm_num) _))
    (hM _ s hs) hT0
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (ha.le.trans hab))

/-- One threshold absorbs every adaptive depth and every parameter in `[a,b]`.
The constants, endpoints, exponent and error allowance are fixed first. -/
theorem eventually_all_depth_suzuki_error_compact
    (H : Section13HatLayers) {β C K a b d Δ ρ : ℝ}
    (hH : Section13HatContract H β) (hC : 0 ≤ C)
    (ha : 0 < a) (hab : a ≤ b) (hd : 0 ≤ d) (hΔ : 0 < Δ) (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ depth : ℕ, ∀ s ∈ Icc a b,
      0 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H depth D d s *
          (Real.log D) ^ (-Δ) ∧
      C * Real.exp (Real.sqrt K) * errorEnvelope H depth D d s *
          (Real.log D) ^ (-Δ) < ρ := by
  obtain ⟨B, _hB0, hB⟩ := exists_all_depth_errorEnvelope_compact_bound H hH ha hab hd
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-Δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hΔ).comp Real.tendsto_log_atTop
  let A : ℝ := C * Real.exp (Real.sqrt K) * B
  have hsmall : ∀ᶠ D : ℝ in atTop, A * (Real.log D) ^ (-Δ) < ρ := by
    have hmul : Tendsto (fun D : ℝ => A * (Real.log D) ^ (-Δ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).mul hdecay)
    exact (tendsto_order.1 hmul).2 ρ hρ
  have hlargeLog : ∀ᶠ D : ℝ in atTop, b ^ d ≤ Real.log D :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (b ^ d))
  filter_upwards [hsmall, hlargeLog, eventually_gt_atTop (1 : ℝ)] with D hsmallD hlogD hD
  intro depth s hs
  obtain ⟨hE0, hE⟩ := hB D hD hlogD depth s hs
  have hdecay0 : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg (Real.log_pos hD).le _
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) hE0) hdecay0
  · calc
      C * Real.exp (Real.sqrt K) * errorEnvelope H depth D d s *
          (Real.log D) ^ (-Δ) ≤ A * (Real.log D) ^ (-Δ) := by
            apply mul_le_mul_of_nonneg_right _ hdecay0
            exact mul_le_mul_of_nonneg_left hE (mul_nonneg hC (Real.exp_pos _).le)
      _ < ρ := hsmallD

end

end ImbalancedChen
