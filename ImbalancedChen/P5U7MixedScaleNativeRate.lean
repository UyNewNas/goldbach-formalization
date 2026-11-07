import ImbalancedChen.P5U7MixedScalePrimeKernel

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native scalar mixed-scale error modulus for an actual cutoff sequence.
Only the genuine cutoff-ratio limit M(N)/N->beta is an input. The desired
prime-main comparison is derived uniformly before choosing a; no arithmetic
mean, final density or CDF asymptotic is assumed.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology

def p5U7MixedScaleNativeRate (M : ℕ → ℕ) (beta : ℝ) (N : ℕ) : ℝ :=
  |((M N : ℕ) : ℝ)/(N : ℝ)-beta|+1/Real.log (N : ℝ)

/-- The explicit native error rate vanishes at every actual ratio limit. -/
theorem p5U7MixedScaleNativeRate_tendsto_zero (M : ℕ → ℕ) (beta : ℝ)
    (hscale : Tendsto (fun N : ℕ => ((M N : ℕ) : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (p5U7MixedScaleNativeRate M beta) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => beta) atTop (𝓝 beta) := tendsto_const_nhds
  have h1 := (hscale.sub hc).abs
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2 := hlog.const_div_atTop (1 : ℝ)
  have hh := h1.add h2
  simpa only [p5U7MixedScaleNativeRate,sub_self,abs_zero,zero_add] using hh

/-- Cutoff ratio and scalar log transport supply ONE N threshold before
all physical multipliers a. This is a native kernel estimate, not a sum. -/
theorem p5U7MixedScale_eventually_uniform_prime_main (M : ℕ → ℕ)
    (beta alpha epsilon : ℝ) (hbeta : 0 < beta) (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hM : ∀ N, M N ≤ N)
    (hscale : Tendsto (fun N : ℕ => ((M N : ℕ) : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, 0 < a → (N : ℝ)^alpha ≤ ((M N : ℕ) : ℝ)/a →
      |(Real.log (N : ℝ)/(N : ℝ))*((((M N : ℕ) : ℝ)/a)/Real.log (((M N : ℕ) : ℝ)/a))-
        beta*(1/a)*(Real.log (N : ℝ)/Real.log ((N : ℝ)/a))| ≤ epsilon/a := by
  let C := p5U7MixedScaleKernelConstant alpha (beta/2)
  have hscaled : Tendsto (fun N : ℕ => C*p5U7MixedScaleNativeRate M beta N) atTop (𝓝 0) := by
    simpa only [mul_zero] using (p5U7MixedScaleNativeRate_tendsto_zero M beta hscale).const_mul C
  have hsmall := hscaled.eventually (gt_mem_nhds hepsilon)
  have hlower := hscale.eventually (Ioi_mem_nhds (half_lt_self hbeta))
  filter_upwards [hsmall,hlower,eventually_ge_atTop (2 : ℕ)] with N hsmall hlower hN
  intro a ha hx
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hupper : ((M N : ℕ) : ℝ)/(N : ℝ) ≤ 1 :=
    (div_le_one hn0).mpr (show ((M N : ℕ) : ℝ) ≤ N by exact_mod_cast hM N)
  have hh := p5U7MixedScale_prime_main_rate_bound (N : ℝ) ((M N : ℕ) : ℝ) a
    alpha (beta/2) beta hn ha halpha (half_pos hbeta) hlower.le hupper hx
  change |(Real.log (N : ℝ)/(N : ℝ))*((((M N : ℕ) : ℝ)/a)/Real.log (((M N : ℕ) : ℝ)/a))-
      beta*(1/a)*(Real.log (N : ℝ)/Real.log ((N : ℝ)/a))| ≤
    (1/a)*C*p5U7MixedScaleNativeRate M beta N at hh
  calc
    _ ≤ (1/a)*C*p5U7MixedScaleNativeRate M beta N := hh
    _ = (1/a)*(C*p5U7MixedScaleNativeRate M beta N) := by ring
    _ ≤ (1/a)*epsilon := mul_le_mul_of_nonneg_left hsmall.le (one_div_nonneg.mpr ha.le)
    _ = epsilon/a := by ring
end
end ImbalancedChen

