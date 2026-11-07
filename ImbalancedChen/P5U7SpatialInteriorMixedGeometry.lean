import ImbalancedChen.P5U7SpatialComponentCDF
import ImbalancedChen.P5U7TerminalPrimeMixedUniform

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual original marked factor geometry for a mixed spatial cutoff M.
A positive limiting ratio M(N)/N supplies the lowered prefix exponent
59/500 and terminal margin exponent (59/500)*eta. The generic mixed-window
PNT is consumed only after these finite geometric conditions are proved.
Original target N and its excluded prime divisors remain fixed.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

/-- Finite ratio-loss transport for the original fixed-positive-eta
interior. M controls only the upper product wall. -/
theorem p5U7Spatial_interior_mixed_geometry {N M : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) {t : ℕ × ℕ} (ht : t ∈ p5U7InteriorSelector N eta)
    (hbase : (N : ℝ)^(-(59/500 : ℝ)) ≤ (M : ℝ)/(N : ℝ))
    (hwall : (N : ℝ)^(-((59/500 : ℝ)*eta)) ≤ (M : ℝ)/(N : ℝ)) :
    0 < t.1*t.2 ∧
      (N : ℝ)^(59/500 : ℝ) ≤ (M : ℝ)/((t.1*t.2 : ℕ) : ℝ) ∧
      (t.2 : ℝ) ≤ ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))*(N : ℝ)^(-((59/500 : ℝ)*eta)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
  have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
  let y : ℝ := (N : ℝ)/((t.1*t.2 : ℕ) : ℝ)
  let r : ℝ := (M : ℝ)/(N : ℝ)
  have hy : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) haR.le
  have hr : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hid : r*y=(M : ℝ)/((t.1*t.2 : ℕ) : ℝ) := by
    dsimp only [r,y]
    field_simp [hNR.ne',haR.ne']
  have hybase : (N : ℝ)^(59/250 : ℝ) ≤ y := hg.2.1.trans hg.2.2.1.le
  have hprod := mul_le_mul hbase hybase (Real.rpow_nonneg hNR.le _) hr
  have hpow : (N : ℝ)^(-(59/500 : ℝ))*(N : ℝ)^(59/250 : ℝ) =
      (N : ℝ)^(59/500 : ℝ) := by
    rw [← Real.rpow_add hNR]
    congr 1
    norm_num
  rw [hpow,hid] at hprod
  have hold := p5U7TerminalPrime_interior_wall (show 0 < N by omega) heta
    (p5U7InteriorSelector_subset_band hN eta ht)
  have hpow2 : (N : ℝ)^(-((59/250 : ℝ)*eta)) =
      (N : ℝ)^(-((59/500 : ℝ)*eta))*(N : ℝ)^(-((59/500 : ℝ)*eta)) := by
    rw [← Real.rpow_add hNR]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hwall
    (mul_nonneg hy (Real.rpow_nonneg hNR.le (-((59/500 : ℝ)*eta))))
  rw [hpow2] at hold
  change (t.2 : ℝ) ≤ y*((N : ℝ)^(-((59/500 : ℝ)*eta))*
    (N : ℝ)^(-((59/500 : ℝ)*eta))) at hold
  have hlast : (t.2 : ℝ) ≤ r*y*(N : ℝ)^(-((59/500 : ℝ)*eta)) := by
    nlinarith only [hold,hm]
  rw [hid] at hlast
  exact ⟨hg.1,hprod,hlast⟩

/-- A strictly positive limiting physical cutoff ratio supplies the two
power margins uniformly over all original marked interior pairs. -/
theorem p5U7Spatial_eventually_interior_mixed_geometry (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    ∀ᶠ N : ℕ in atTop,∀ t ∈ p5U7InteriorSelector N eta,
      0 < t.1*t.2 ∧ (N : ℝ)^(59/500 : ℝ) ≤ (M N : ℝ)/((t.1*t.2 : ℕ) : ℝ) ∧
      (t.2 : ℝ) ≤ ((M N : ℝ)/((t.1*t.2 : ℕ) : ℝ))*(N : ℝ)^(-((59/500 : ℝ)*eta)) := by
  have hbase : Tendsto (fun N : ℕ => (N : ℝ)^(-(59/500 : ℝ))) atTop (𝓝 0) :=
    (Real.tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 59/500)).comp tendsto_natCast_atTop_atTop
  have hwall : Tendsto (fun N : ℕ => (N : ℝ)^(-((59/500 : ℝ)*eta))) atTop (𝓝 0) :=
    (Real.tendsto_rpow_neg_atTop (show 0 < (59/500 : ℝ)*eta by positivity)).comp
      tendsto_natCast_atTop_atTop
  have hsmall1 := hbase.eventually (Iio_mem_nhds (half_pos hb))
  have hsmall2 := hwall.eventually (Iio_mem_nhds (half_pos hb))
  have hlarge := hratio.eventually (Ioi_mem_nhds (show beta/2 < beta by linarith only [hb]))
  filter_upwards [hsmall1,hsmall2,hlarge,eventually_ge_atTop (2 : ℕ)] with N h1 h2 hr hN
  intro t ht
  exact p5U7Spatial_interior_mixed_geometry hN heta.le ht (h1.trans hr).le (h2.trans hr).le

/-- Genuine mixed-window PNT on the actual original strict interior:
one threshold follows the chosen positive eta and cutoff-ratio limit. -/
theorem p5U7Spatial_eventually_actual_prime_window_error (M : ℕ → ℕ) (beta eta epsilon : ℝ)
    (hb : 0 < beta) (heta : 0 < eta) (he : 0 < epsilon)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    ∀ᶠ N : ℕ in atTop,∀ t ∈ p5U7InteriorSelector N eta,
      |((p5U7MassPrimeWindow N (M N) (t.1*t.2) t.2).card : ℝ)-
        ((M N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((M N : ℝ)/((t.1*t.2 : ℕ) : ℝ))| ≤
      epsilon*(((M N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log ((M N : ℝ)/((t.1*t.2 : ℕ) : ℝ))) := by
  have hPNT := p5U7TerminalPrimeMixed_eventually_uniform_abs (59/500 : ℝ)
    ((59/500 : ℝ)*eta) epsilon (by norm_num) (by positivity) he
  filter_upwards [hPNT,hMN,p5U7Spatial_eventually_interior_mixed_geometry M beta eta hb heta hratio]
    with N hp hn hg
  intro t ht
  have hd := hg t ht
  exact hp _ _ _ hn hd.1 hd.2.1 hd.2.2

end
end ImbalancedChen
