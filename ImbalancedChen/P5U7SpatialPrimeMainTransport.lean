import ImbalancedChen.P5U7SpatialInteriorMixedGeometry
import ImbalancedChen.P5U7MixedScalePrimeKernel

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Summed native mixed-cutoff prime main on the SAME actual marked selector.
The scalar log-shift bound is paid by the existing true harmonic pair
bound 25, preserving target N. Hence cutoff M(N)/N -> beta multiplies the
genuine fixed-interior prime leading integral by beta. No spatial CDF
mean or prime-window arithmetic mean is used as a premise here.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

def p5U7SpatialPrimeMain (N M : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))

def p5U7SpatialPrimeMainError (N M : ℕ) (alpha beta0 beta : ℝ) : ℝ :=
  |(M : ℝ)/(N : ℝ)-beta|/alpha+(-Real.log beta0)/(alpha^2*Real.log (N : ℝ))

/-- Finite summed native main transport at the original marked pairs.
All comparison constants come from actual scalar log geometry and the
proved arithmetic reciprocal-pair bound. -/
theorem p5U7SpatialPrimeMain_normalized_error_le {N M : ℕ} (hN : 2 ≤ N)
    (eta alpha beta0 beta : ℝ) (halpha : 0 < alpha) (hbeta0 : 0 < beta0)
    (hr0 : beta0 ≤ (M : ℝ)/(N : ℝ)) (hr1 : (M : ℝ)/(N : ℝ) ≤ 1)
    (hbase : ∀ t ∈ p5U7InteriorSelector N eta,
      (N : ℝ)^alpha ≤ (M : ℝ)/((t.1*t.2 : ℕ) : ℝ))
    (houter : p5U7BoundaryOuterReciprocalMass N ≤ 5) :
    |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N M eta-
      beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta)| ≤
      25*p5U7SpatialPrimeMainError N M alpha beta0 beta := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNR : (0 : ℝ) < N := zero_lt_one.trans hn
  have hE : 0 ≤ p5U7SpatialPrimeMainError N M alpha beta0 beta := by
    unfold p5U7SpatialPrimeMainError
    exact add_nonneg (div_nonneg (abs_nonneg _) halpha.le)
      (div_nonneg (neg_nonneg.mpr (Real.log_nonpos hbeta0.le (hr0.trans hr1)))
        (mul_nonneg (sq_nonneg _) (Real.log_pos hn).le))
  have hrow (t : ℕ × ℕ) (ht : t ∈ p5U7InteriorSelector N eta) :
      |(Real.log (N : ℝ)/(N : ℝ))*
        (((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)))-
        beta*((Real.log (N : ℝ)/(N : ℝ))*
          (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))))| ≤
      (1/((t.1*t.2 : ℕ) : ℝ))*p5U7SpatialPrimeMainError N M alpha beta0 beta := by
    have ha := (p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1).1
    have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast ha
    have hid : (Real.log (N : ℝ)/(N : ℝ))*
        (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))) =
        (1/((t.1*t.2 : ℕ) : ℝ))*(Real.log (N : ℝ)/Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))) := by
      calc
        _ = ((N : ℝ)/(N : ℝ))*(1/((t.1*t.2 : ℕ) : ℝ))*
            (Real.log (N : ℝ)/Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))) := by
          simp only [div_eq_mul_inv]
          ring
        _ = _ := by rw [div_self hNR.ne',one_mul]
    rw [hid]
    simpa only [mul_assoc,p5U7SpatialPrimeMainError] using p5U7MixedScale_prime_main_error (N : ℝ) (M : ℝ) ((t.1*t.2 : ℕ) : ℝ)
      alpha beta0 beta hn haR halpha hbeta0 hr0 hr1 (hbase t ht)
  have hid : (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N M eta-
      beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta) =
      ∑ t ∈ p5U7InteriorSelector N eta,
        ((Real.log (N : ℝ)/(N : ℝ))*
          (((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)))-
          beta*((Real.log (N : ℝ)/(N : ℝ))*
            (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))))) := by
    unfold p5U7SpatialPrimeMain p5U7PrimeLeadingMain
    simp only [Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hid]
  calc
    _ ≤ ∑ t ∈ p5U7InteriorSelector N eta,
        |(Real.log (N : ℝ)/(N : ℝ))*
          (((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)))-
          beta*((Real.log (N : ℝ)/(N : ℝ))*
            (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ p5U7InteriorSelector N eta,
        (1/((t.1*t.2 : ℕ) : ℝ))*p5U7SpatialPrimeMainError N M alpha beta0 beta :=
      Finset.sum_le_sum hrow
    _ = (∑ t ∈ p5U7InteriorSelector N eta,1/((t.1*t.2 : ℕ) : ℝ))*
        p5U7SpatialPrimeMainError N M alpha beta0 beta := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (p5U7ActualInterior_pair_mass_le hN eta houter) hE

theorem tendsto_p5U7SpatialPrimeMainError (M : ℕ → ℕ) (alpha beta0 beta : ℝ)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => p5U7SpatialPrimeMainError N (M N) alpha beta0 beta) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun N : ℕ => |(M N : ℝ)/(N : ℝ)-beta|/alpha) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_div] using (hratio.sub_const beta).abs.div_const alpha
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsecond : Tendsto (fun N : ℕ => (-Real.log beta0)/(alpha^2*Real.log (N : ℝ)))
      atTop (𝓝 0) := by
    have h := hlog.const_div_atTop ((-Real.log beta0)/alpha^2)
    convert h using 1
    funext N
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  simpa only [p5U7SpatialPrimeMainError,zero_add] using hfirst.add hsecond

/-- Actual mixed-cutoff normalized prime MAIN converges to beta times
the genuine original fixed-interior leading integral. -/
theorem tendsto_p5U7SpatialPrimeMain_normalized (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta)
      atTop (𝓝 (beta*p5U7PrimeLeadingIntegral eta)) := by
  have hrate := (tendsto_p5U7SpatialPrimeMainError M (59/500 : ℝ) (beta/2) beta hratio).const_mul 25
  have hratio0 := hratio.eventually (Ioi_mem_nhds (show beta/2 < beta by linarith only [hb]))
  have habs : Tendsto (fun N : ℕ =>
      |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta-
        beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [mul_zero] using hrate)
    filter_upwards [hMN,hratio0,p5U7Boundary_eventually_outer_mass_le_five,
      p5U7Spatial_eventually_interior_mixed_geometry M beta eta hb heta hratio,
      eventually_ge_atTop (2 : ℕ)] with N hm hr ho hg hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hr1 : (M N : ℝ)/(N : ℝ) ≤ 1 := (div_le_one hNR).mpr (by exact_mod_cast hm)
    exact p5U7SpatialPrimeMain_normalized_error_le hN eta (59/500 : ℝ) (beta/2) beta
      (by norm_num) (half_pos hb) hr.le hr1 (fun t ht => (hg t ht).2.1) ho
  have hdiff : Tendsto (fun N : ℕ =>
      (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialPrimeMain N (M N) eta-
        beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact habs
  have h := hdiff.add ((tendsto_p5U7PrimeLeadingMain_normalized eta heta.le).const_mul beta)
  simpa only [sub_add_cancel,zero_add] using h

end
end ImbalancedChen
