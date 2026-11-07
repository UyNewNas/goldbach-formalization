import ImbalancedChen.P5U7SpatialBuchstabArgumentGeometry
import ImbalancedChen.P5U7MixedScaleBuchstabKernel

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Required summed mixed-cutoff native Buchstab transport. Actual native
argument geometry is derived on original marked pairs before consuming
the range-respecting scalar kernel. The true same-selector harmonic
bound 25 pays every row error. Actual mixed rough/native and target-loss
limits then give the full mixed-cutoff fixed-interior arithmetic mean.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

/-- Actual summed native Buchstab main error with original target N.
The only scalar regularity used is on the proved original native range. -/
theorem p5U7SpatialBuchstabMain_normalized_error_le {N M : ℕ} (hN : 2 ≤ N) (hMN : M ≤ N)
    (eta beta0 beta : ℝ) (heta : 0 ≤ eta) (hbeta0 : 0 < beta0)
    (hr0 : beta0 ≤ (M : ℝ)/(N : ℝ))
    (hlower : ∀ t ∈ p5U7InteriorSelector N eta,(t.2 : ℝ) ≤ (M : ℝ)/((t.1*t.2 : ℕ) : ℝ))
    (houter : p5U7BoundaryOuterReciprocalMass N ≤ 5) :
    |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialBuchstabMain N M eta-
      beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7MassBuchstabInteriorMain N eta)| ≤
      25*p5U7SpatialPrimeMainError N M (59/250 : ℝ) beta0 beta := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNR : (0 : ℝ) < N := zero_lt_one.trans hn
  have hr1 : (M : ℝ)/(N : ℝ) ≤ 1 := (div_le_one hNR).mpr (by exact_mod_cast hMN)
  have hE : 0 ≤ p5U7SpatialPrimeMainError N M (59/250 : ℝ) beta0 beta := by
    unfold p5U7SpatialPrimeMainError
    exact add_nonneg (div_nonneg (abs_nonneg _) (by norm_num))
      (div_nonneg (neg_nonneg.mpr (Real.log_nonpos hbeta0.le (hr0.trans hr1)))
        (mul_nonneg (sq_nonneg _) (Real.log_pos hn).le))
  have hrow (t : ℕ × ℕ) (ht : t ∈ p5U7InteriorSelector N eta) :
      |(Real.log (N : ℝ)/(N : ℝ))*
        (((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
          buchstab (Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ))-
        beta*((Real.log (N : ℝ)/(N : ℝ))*
          (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
            buchstab (Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ)))| ≤
      (1/((t.1*t.2 : ℕ) : ℝ))*p5U7SpatialPrimeMainError N M (59/250 : ℝ) beta0 beta := by
    have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
    have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
    have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
    have hz : (1 : ℝ) < t.2 := by exact_mod_cast hq.one_lt
    have hs := p5U7Spatial_buchstab_argument_geometry hN hMN heta ht (hlower t ht)
    simpa only [p5U7SpatialPrimeMainError] using p5U7MixedScale_buchstab_main_error
      (N : ℝ) (M : ℝ) ((t.1*t.2 : ℕ) : ℝ) (t.2 : ℝ) (59/250 : ℝ) beta0 beta
      hn haR hz (by norm_num) hg.2.1 hbeta0 hr0 hr1 hs.1.1 hs.2.2.1 hs.2.1.2
  have hid : (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialBuchstabMain N M eta-
      beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7MassBuchstabInteriorMain N eta) =
      ∑ t ∈ p5U7InteriorSelector N eta,
        ((Real.log (N : ℝ)/(N : ℝ))*
          (((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
            buchstab (Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ))-
          beta*((Real.log (N : ℝ)/(N : ℝ))*
            (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
              buchstab (Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ)))) := by
    unfold p5U7SpatialBuchstabMain p5U7MassBuchstabInteriorMain
    simp only [Finset.mul_sum,Finset.sum_sub_distrib]
  rw [hid]
  calc
    _ ≤ ∑ t ∈ p5U7InteriorSelector N eta,
        |(Real.log (N : ℝ)/(N : ℝ))*
          (((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
            buchstab (Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ))-
          beta*((Real.log (N : ℝ)/(N : ℝ))*
            (((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
              buchstab (Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ p5U7InteriorSelector N eta,
        (1/((t.1*t.2 : ℕ) : ℝ))*p5U7SpatialPrimeMainError N M (59/250 : ℝ) beta0 beta :=
      Finset.sum_le_sum hrow
    _ = (∑ t ∈ p5U7InteriorSelector N eta,1/((t.1*t.2 : ℕ) : ℝ))*
        p5U7SpatialPrimeMainError N M (59/250 : ℝ) beta0 beta := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (p5U7ActualInterior_pair_mass_le hN eta houter) hE

theorem tendsto_p5U7SpatialBuchstabMain_normalized (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta) (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialBuchstabMain N (M N) eta)
      atTop (𝓝 (beta*p5U7InteriorOmegaIntegral eta)) := by
  have hrate := (tendsto_p5U7SpatialPrimeMainError M (59/250 : ℝ) (beta/2) beta hratio).const_mul 25
  have hr0 := hratio.eventually (Ioi_mem_nhds (show beta/2 < beta by linarith only [hb]))
  have habs : Tendsto (fun N : ℕ =>
      |(Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialBuchstabMain N (M N) eta-
        beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7MassBuchstabInteriorMain N eta)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [mul_zero] using hrate)
    filter_upwards [hMN,hr0,p5U7Boundary_eventually_outer_mass_le_five,
      p5U7Spatial_eventually_native_band_geometry M beta eta hb heta hMN hratio,
      eventually_ge_atTop (2 : ℕ)] with N hm hr ho hg hN
    exact p5U7SpatialBuchstabMain_normalized_error_le hN hm eta (beta/2) beta heta.le (half_pos hb)
      hr.le (fun t ht => (hg t ht).1) ho
  have hdiff : Tendsto (fun N : ℕ =>
      (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialBuchstabMain N (M N) eta-
        beta*((Real.log (N : ℝ)/(N : ℝ))*p5U7MassBuchstabInteriorMain N eta)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact habs
  have h := hdiff.add ((tendsto_p5U7MassBuchstabInteriorMain_normalized heta.le).const_mul beta)
  simpa only [sub_add_cancel,zero_add] using h

/-- Actual mixed rough-mother arithmetic mean, using the genuine native
band3 error transport in addition to the independently proved main. -/
theorem tendsto_p5U7SpatialInteriorRoughMass_normalized (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta) (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorRoughMass N (M N) eta)
      atTop (𝓝 (beta*p5U7InteriorOmegaIntegral eta)) := by
  have h := (tendsto_p5U7Spatial_rough_main_difference M beta eta hb heta hMN hratio).add
    (tendsto_p5U7SpatialBuchstabMain_normalized M beta eta hb heta hMN hratio)
  convert h using 1
  · funext N
    ring
  · simp only [zero_add]

/-- Actual BOTH-component mixed-cutoff fixed-interior mean. Original-N
target-divisor losses, the unit and cutoff-M endpoint have all been paid. -/
theorem tendsto_p5U7SpatialInteriorFullMass_normalized (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta) (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*p5U7SpatialInteriorFullMass N (M N) eta)
      atTop (𝓝 (beta*p5U7InteriorOmegaIntegral eta)) := by
  have h := (tendsto_p5U7SpatialInteriorRoughMass_normalized M beta eta hb heta hMN hratio).sub
    (tendsto_p5U7Spatial_actual_target_loss M eta hMN)
  convert h using 1
  · funext N
    ring
  · simp only [sub_zero]

end
end ImbalancedChen
