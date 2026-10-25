import ImbalancedChen.P5U6OriginalOwnerKernelConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Formula-derived uniform bounds for the true generated U6 envelopes.
Only outer cells need a rational upper bound: their query stays in the
actual profile range, the actual LOWER floor has range [0,1], and every
denominator has the fixed full-rectangle margin R>=14/125. Generated
ownership makes each finite sample a SINGLE coefficient, not a sum of
cell bounds. The resulting actual compactly supported dominator is proved
integrable. No bound or domination premise is supplied by a caller.
-/

namespace ImbalancedChen.P5U6OriginalUniformEnvelopeBounds

noncomputable section

open Set Filter Topology MeasureTheory Classical
open scoped BigOperators
open P2ContinuousSieveRational
open P5U6OriginalRationalBoxBounds P5U6OriginalRationalIntegralCertificates
open P5U6OriginalLowerFloorLocal P5U6OriginalUniformLogTail
open P5U6OriginalOwnerKernelConvergence
open P5U6AdoptedH248BindingSourceOnly P5U6RetainedAdoptedIntegralSourceOnly
open P5U6RetainedExplicitBufferSourceOnly

def densityBound : ℚ := 30000

theorem uniform_rate_le_four (n : ℕ) : rate n ≤ 4 := by
  have hp : ratio ^ (2 * n + 1) ≤ (1 : ℚ) :=
    pow_le_one₀ (by norm_num [ratio]) (by norm_num [ratio])
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

theorem actual_logUpper_le_six (n : ℕ) (q : ℚ)
    (hq : 2 ≤ q) (hM : q ≤ 1323 / 417) : logUpper n q ≤ 6 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (q : ℝ) ≤ 1323 / 417 := by exact_mod_cast hM
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (q : ℝ) - 1 by linarith)
  have hLo := (log_bounds n q hq).1
  have hGap : (logUpper n q : ℝ) - (logLower n q : ℝ) ≤ (rate n : ℝ) := by
    exact_mod_cast (rational_gap_le_rate n q hq hM).2
  have hRate : (rate n : ℝ) ≤ 4 := by exact_mod_cast uniform_rate_le_four n
  have hreal : (logUpper n q : ℝ) ≤ 6 := by
    linarith only [hMR, hlog, hLo, hGap, hRate]
  exact_mod_cast hreal

theorem outer_densityUpper_le (n precision : ℕ) {j : Index n} (hj : j ∈ outer n) :
    densityUpper n precision j ≤ densityBound := by
  let b := gridBox n j
  let c : ℚ := (14 / 125) * (417 / 5000) * (19 / 125)
  have hc : 0 < c := by norm_num [c]
  have hR : 14 / 125 ≤ b.rLo := grid_residual_margin n j
  have hu : 417 / 5000 ≤ b.uLo := (corner_bounds n j 0).1
  have ht : 19 / 125 ≤ b.tLo := (corner_bounds n j 1).1
  have hRp : 0 < b.rLo := lt_of_lt_of_le (by norm_num) hR
  have hup : 0 < b.uLo := lt_of_lt_of_le (by norm_num) hu
  have hden : c ≤ b.denLo := by
    exact mul_le_mul (mul_le_mul hR hu (by norm_num) hRp.le) ht (by norm_num) (by positivity)
  have hdenp := hc.trans_le hden
  have hq := grid_queries_range n hj
  have hlog := actual_logUpper_le_six precision b.sHi (hq.1.trans hq.2.1) hq.2.2
  have hh := (interval_range hq.2.1).2.2
  have hnum : 4 * (logUpper precision b.sHi + hUpper b.sLo b.sHi) ≤ 28 := by
    linarith only [hlog, hh]
  have hkernel : b.kernelUpper precision ≤ densityBound := by
    calc
      _ ≤ 28 / b.denLo := div_le_div_of_nonneg_right hnum hdenp.le
      _ ≤ 28 / c := div_le_div_of_nonneg_left (by norm_num) hc hden
      _ ≤ densityBound := by norm_num [c, densityBound]
  exact max_le (by norm_num [densityBound]) hkernel

def sample (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ) (x : Fin 2 → ℝ) : ℝ :=
  ∑ j ∈ S, (cell n j).indicator (fun _ => (q j : ℝ)) x

theorem sample_eq_owner (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ)
    {x : Fin 2 → ℝ} (hx : x ∈ currentChenUpsilon6LogRectangle) :
    sample n S q x = if owner n x hx ∈ S then (q (owner n x hx) : ℝ) else 0 := by
  by_cases ho : owner n x hx ∈ S
  · rw [sample, if_pos ho, Finset.sum_eq_single (owner n x hx)]
    · exact indicator_of_mem (owner_mem n x hx) _
    · intro j hj hjo
      exact indicator_of_notMem (fun hcell => hjo (cell_unique hcell (owner_mem n x hx))) _
    · intro hn
      exact (hn ho).elim
  · rw [sample, if_neg ho]
    apply Finset.sum_eq_zero
    intro j hj
    exact indicator_of_notMem (fun hcell => ho ((cell_unique hcell (owner_mem n x hx)) ▸ hj)) _

theorem sample_eq_zero_outside (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ)
    {x : Fin 2 → ℝ} (hx : x ∉ currentChenUpsilon6LogRectangle) : sample n S q x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact indicator_of_notMem (fun hcell => hx (cell_subset_rectangle n j hcell)) _

theorem sample_integrable (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ) :
    Integrable (sample n S q) :=
  integrable_finsetSum S (fun j _ => cell_constant_integrable n j _)

theorem sample_integral (n : ℕ) (S : Finset (Index n)) (q : Index n → ℚ) :
    (∫ x, sample n S q x) = ((∑ j ∈ S, q j * area n j : ℚ) : ℝ) := by
  rw [sample, integral_finsetSum S (fun j _ => cell_constant_integrable n j _)]
  calc
    _ = ∑ j ∈ S, ((q j * area n j : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_cell_constant n j _
    _ = _ := by push_cast

theorem lower_sample_bound (n precision : ℕ) (S : Finset (Index n))
    (hS : S ⊆ inner n) (x : Fin 2 → ℝ) :
    ‖sample n S (densityLower n precision) x‖ ≤
      currentChenUpsilon6LogRectangle.indicator (fun _ => (densityBound : ℝ)) x := by
  by_cases hx : x ∈ currentChenUpsilon6LogRectangle
  · rw [sample_eq_owner n S _ hx, indicator_of_mem hx]
    by_cases ho : owner n x hx ∈ S
    · rw [if_pos ho, Real.norm_eq_abs, abs_of_nonneg]
      · have hD := inner_cell_subset_domain n (hS ho) (owner_mem n x hx)
        have hL := (kernel_cell_bounds n precision (owner n x hx) (owner_mem n x hx) hD).1
        have hK : adoptedKernel x ≤ 6000 := (le_abs_self _).trans
          (by simpa only [Real.norm_eq_abs] using adoptedKernel_norm_le_6000 hD)
        exact (hL.trans hK).trans (by norm_num [densityBound])
      · exact_mod_cast (le_max_left (0 : ℚ) ((gridBox n (owner n x hx)).kernelLower precision))
    · rw [if_neg ho, norm_zero]
      norm_num [densityBound]
  · simp only [sample_eq_zero_outside n S _ hx, indicator_of_notMem hx, norm_zero, le_refl]

theorem upper_sample_bound (n precision : ℕ) (S : Finset (Index n))
    (hS : S ⊆ outer n) (x : Fin 2 → ℝ) :
    ‖sample n S (densityUpper n precision) x‖ ≤
      currentChenUpsilon6LogRectangle.indicator (fun _ => (densityBound : ℝ)) x := by
  by_cases hx : x ∈ currentChenUpsilon6LogRectangle
  · rw [sample_eq_owner n S _ hx, indicator_of_mem hx]
    by_cases ho : owner n x hx ∈ S
    · rw [if_pos ho, Real.norm_eq_abs, abs_of_nonneg]
      · exact_mod_cast outer_densityUpper_le n precision (hS ho)
      · exact_mod_cast (le_max_left (0 : ℚ) ((gridBox n (owner n x hx)).kernelUpper precision))
    · rw [if_neg ho, norm_zero]
      norm_num [densityBound]
  · simp only [sample_eq_zero_outside n S _ hx, indicator_of_notMem hx, norm_zero, le_refl]

def domination (x : Fin 2 → ℝ) : ℝ :=
  currentChenUpsilon6LogRectangle.indicator (fun _ => 2 * (densityBound : ℝ)) x

theorem sample_difference_dominated (n precision : ℕ) (L U : Finset (Index n))
    (hL : L ⊆ inner n) (hU : U ⊆ outer n) (x : Fin 2 → ℝ) :
    ‖sample n U (densityUpper n precision) x - sample n L (densityLower n precision) x‖ ≤
      domination x := by
  have h := (norm_sub_le _ _).trans (add_le_add
    (upper_sample_bound n precision U hU x) (lower_sample_bound n precision L hL x))
  by_cases hx : x ∈ currentChenUpsilon6LogRectangle
  · simpa only [domination, indicator_of_mem hx, two_mul] using h
  · simpa only [domination, indicator_of_notMem hx, add_zero] using h

theorem domination_integrable : Integrable domination := by
  let C : Set (Fin 2 → ℝ) := Icc (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ))
  have hsub : currentChenUpsilon6LogRectangle ⊆ C := by
    intro x hx
    have h := mem_currentChenUpsilon6LogRectangle.mp hx
    constructor
    · intro i
      fin_cases i
      · exact h.1
      · exact h.2.2.1
    · intro i
      fin_cases i
      · exact h.2.1.le
      · exact h.2.2.2.le
  have hc : IntegrableOn (fun _ : Fin 2 → ℝ => 2 * (densityBound : ℝ)) C :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  exact (hc.mono_set hsub).integrable_indicator measurableSet_currentChenUpsilon6LogRectangle

end

end ImbalancedChen.P5U6OriginalUniformEnvelopeBounds
