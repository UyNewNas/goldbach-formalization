import ImbalancedChen.Part3ComplexOrderKPositiveLaplace

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
For every fixed complex order with positive real part, the actual K
integral has its Gamma-normalized leading term as positive q tends to zero.
The proof uses its exact scaled Laplace representation and dominated
convergence against the absolutely integrable complex Gamma kernel.
All cpow bases in the final limit are positive reals, using principal log.
-/

namespace ImbalancedChen.Part3.ComplexOrderKSmallArgument20261025a
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly
open ComplexOrderKPositiveLaplace20261025a

private def gammaDensity (ν : ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * (t : ℂ) ^ (ν - 1)

theorem dampedGammaDensity_norm_le (ν : ℂ) (q : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖dampedGammaDensity ν q t‖ ≤ ‖gammaDensity ν t‖ := by
  have hd : 0 ≤ q ^ 2 / (4 * t) := div_nonneg (sq_nonneg q) (by positivity)
  have he : Real.exp (-(q ^ 2 / (4 * t))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd)
  change ‖gammaDensity ν t * (Real.exp (-(q ^ 2 / (4 * t))) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg (gammaDensity ν t))

theorem dampedGammaDensity_integrable {ν : ℂ} (hν : 0 < ν.re) (q : ℝ) :
    IntegrableOn (dampedGammaDensity ν q) (Ioi 0) := by
  have hg : IntegrableOn (gammaDensity ν) (Ioi 0) := Complex.GammaIntegral_convergent hν
  have hm : Measurable (fun t : ℝ => (Real.exp (-(q ^ 2 / (4 * t))) : ℂ)) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (dampedGammaDensity ν q)
      (volume.restrict (Ioi (0 : ℝ))) := hg.aestronglyMeasurable.mul hm.aestronglyMeasurable
  apply hg.norm.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact dampedGammaDensity_norm_le ν q ht

/-- The reciprocal damping tends to one and is bounded by one on t>0. -/
theorem dampedGamma_integral_tendsto {ν : ℂ} (hν : 0 < ν.re) :
    Tendsto (fun q : ℝ => ∫ t in Ioi (0 : ℝ), dampedGammaDensity ν q t)
      (𝓝 (0 : ℝ)) (𝓝 (Complex.Gamma ν)) := by
  rw [Complex.Gamma_eq_integral hν]
  change Tendsto (fun q : ℝ => ∫ t in Ioi (0 : ℝ), dampedGammaDensity ν q t)
    (𝓝 (0 : ℝ)) (𝓝 (∫ t in Ioi (0 : ℝ), gammaDensity ν t))
  have hg : IntegrableOn (gammaDensity ν) (Ioi 0) := Complex.GammaIntegral_convergent hν
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖gammaDensity ν t‖)
  · exact Eventually.of_forall (fun q => (dampedGammaDensity_integrable hν q).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro q
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact dampedGammaDensity_norm_le ν q ht
  · exact hg.norm
  · apply Eventually.of_forall
    intro t
    have hc : Continuous (fun q : ℝ => dampedGammaDensity ν q t) := by
      unfold dampedGammaDensity
      fun_prop
    have ht : Tendsto (fun q : ℝ => dampedGammaDensity ν q t)
        (𝓝 (0 : ℝ)) (𝓝 (dampedGammaDensity ν 0 t)) := hc.continuousAt
    simpa only [dampedGammaDensity, gammaDensity, zero_pow (by decide : 2 ≠ 0),
      zero_div, neg_zero, Real.exp_zero, Complex.ofReal_one, mul_one] using
        ht

/-- Exact positive-base normalization, before passing to the limit. -/
theorem normalized_K_eq_dampedGamma (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ ν * complexOrderK ν q =
      (2 : ℂ) ^ (ν - 1) * ∫ t in Ioi (0 : ℝ), dampedGammaDensity ν q t := by
  have hc : 0 < q / 2 := half_pos hq
  have htwo : (2 : ℂ) ^ (ν - 1) * 2 = (2 : ℂ) ^ ν := by
    calc
      _ = (2 : ℂ) ^ (ν - 1) * (2 : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = (2 : ℂ) ^ ((ν - 1) + 1) :=
        (Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)).symm
      _ = _ := by congr 1; ring
  have hqsplit : (q : ℂ) ^ ν = (2 : ℂ) ^ ν * ((q / 2 : ℝ) : ℂ) ^ ν := by
    have heq : (q : ℂ) = ((2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) := by push_cast; ring
    calc
      _ = (((2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ)) ^ ν := congrArg (fun z : ℂ => z ^ ν) heq
      _ = _ := by
        simpa only [Complex.ofReal_ofNat] using
          Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc.le ν
  rw [dampedGammaDensity_integral ν hq, hqsplit]
  calc
    _ = ((2 : ℂ) ^ (ν - 1) * 2) * ((q / 2 : ℝ) : ℂ) ^ ν * complexOrderK ν q := by
      rw [htwo]
    _ = _ := by ring

/-- Genuine leading small-argument coefficient for every Re nu>0.
No asymptotic or K/I connection formula is a hypothesis. -/
theorem complexOrderK_small_argument {ν : ℂ} (hν : 0 < ν.re) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ ν * complexOrderK ν q)
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℂ) ^ (ν - 1) * Complex.Gamma ν)) := by
  have hlim := (dampedGamma_integral_tendsto hν).mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun q : ℝ => (2 : ℂ) ^ (ν - 1) *
      ∫ t in Ioi (0 : ℝ), dampedGammaDensity ν q t)
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℂ) ^ (ν - 1) * Complex.Gamma ν)) :=
    tendsto_const_nhds.mul hlim
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (normalized_K_eq_dampedGamma ν hq).symm

end
end ImbalancedChen.Part3.ComplexOrderKSmallArgument20261025a
