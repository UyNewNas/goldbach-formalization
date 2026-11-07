import ImbalancedChen.P5U7SpatialPrimeCDFMean

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Mixed-cutoff ACTUAL rough-mother and native band3 error transport. Cutoff M
changes x=M/(p1*p2), while the marked selector, prime-divisor exclusions,
and native error reserve keep original target N. The genuine bound z≤x≤z³
is derived before using native band3. Target, unit and endpoint losses are
paid by the existing explicit original-N reserve, never declared null.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7SpatialInteriorRoughMass (N M : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    (roughCount ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)

def p5U7SpatialInteriorFullMass (N M : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,((p5U7SpatialGoodRough N M t).card : ℝ)

def p5U7SpatialBuchstabMain (N M : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
      buchstab (Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ)

/-- The shifted x is eventually ABOVE its actual terminal roughness wall.
The original cube bound supplies the unchanged band3 upper wall. -/
theorem p5U7Spatial_eventually_native_band_geometry (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta) (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    ∀ᶠ N : ℕ in atTop,∀ t ∈ p5U7InteriorSelector N eta,
      (t.2 : ℝ) ≤ (M N : ℝ)/((t.1*t.2 : ℕ) : ℝ) ∧
      (M N : ℝ)/((t.1*t.2 : ℕ) : ℝ) ≤ (t.2 : ℝ)^3 := by
  filter_upwards [hMN,p5U7Spatial_eventually_interior_mixed_geometry M beta eta hb heta hratio,
    eventually_ge_atTop (2 : ℕ)] with N hm hg hN
  intro t ht
  have hd := hg t ht
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hd.1
  have hx : 0 ≤ (M N : ℝ)/((t.1*t.2 : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg _) haR.le
  have hp : (N : ℝ)^(-((59/500 : ℝ)*eta)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNR (neg_nonpos.mpr (mul_nonneg (by norm_num) heta.le))
  have hl := hd.2.2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hx)
  have hxy : (M N : ℝ)/((t.1*t.2 : ℕ) : ℝ) ≤ (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hm) haR.le
  exact ⟨hl,hxy.trans (p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1).2.2.2⟩

/-- The actual mixed-cutoff band error is bounded by the ORIGINAL target-N
strict-selector reserve, since x≤N/a and the native remainder is nonnegative. -/
theorem p5U7Spatial_native_rough_error_le {N M : ℕ} (hN : 2 ≤ N) (hMN : M ≤ N)
    (eta : ℝ) (hstart : primeErrorStart ≤ (N : ℝ)^(59/250 : ℝ))
    (hlower : ∀ t ∈ p5U7InteriorSelector N eta,(t.2 : ℝ) ≤ (M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) :
    |p5U7SpatialInteriorRoughMass N M eta-p5U7SpatialBuchstabMain N M eta| ≤
      p5U7InteriorBandError N eta := by
  have hrow (t : ℕ × ℕ) (ht : t ∈ p5U7InteriorSelector N eta) :
      |(roughCount ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)-
        ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))*
          buchstab (Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ))/Real.log (t.2 : ℝ)| ≤
        p5U7InteriorBandRowError N t := by
    have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
    have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
    have hz := hstart.trans hg.2.1
    have hlog : 0 ≤ Real.log (t.2 : ℝ) := (zero_lt_one.trans_le (one_le_log_of_start_le hz)).le
    have hxy : (M : ℝ)/((t.1*t.2 : ℕ) : ℝ) ≤ (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hMN) haR.le
    have hband := roughCount_buchstab_band_error 3 (by norm_num) hz (hlower t ht)
      (hxy.trans hg.2.2.2)
    have hrem := buchstabRemainder_nonneg hz
    have hC : 0 ≤ buchstabBandConstant 3 := by linarith [buchstabBandConstant_ge 3]
    have hm := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hxy hlog) hrem
    have hh := mul_le_mul_of_nonneg_left (add_le_add_right hm ((t.2 : ℝ)/Real.log (t.2 : ℝ))) hC
    unfold p5U7InteriorBandRowError
    exact hband.trans (by convert hh using 1 <;> ring)
  unfold p5U7SpatialInteriorRoughMass p5U7SpatialBuchstabMain
  rw [← Finset.sum_sub_distrib]
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hrow)
  have hreserve : (∑ t ∈ p5U7InteriorSelector N eta,p5U7InteriorBandRowError N t) ≤
      p5U7InteriorBandError N eta := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (p5U7InteriorSelector_subset_band hN eta)
      (fun t ht _ => p5U7Interior_row_error_nonneg hstart ht)
  exact hsum.trans hreserve

theorem tendsto_p5U7Spatial_rough_main_difference (M : ℕ → ℕ) (beta eta : ℝ)
    (hb : 0 < beta) (heta : 0 < eta) (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N)
    (hratio : Tendsto (fun N : ℕ => (M N : ℝ)/(N : ℝ)) atTop (𝓝 beta)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (p5U7SpatialInteriorRoughMass N (M N) eta-p5U7SpatialBuchstabMain N (M N) eta))
      atTop (𝓝 0) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ)^(59/250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' ?_ (p5U7Interior_band_error_normalized_tendsto_zero eta heta)
  filter_upwards [hMN,p5U7Spatial_eventually_native_band_geometry M beta eta hb heta hMN hratio,
    hgrowth.eventually (eventually_ge_atTop primeErrorStart),eventually_ge_atTop (2 : ℕ)]
    with N hm hg hs hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hnorm := div_nonneg hLN.le hNR.le
  have hh := mul_le_mul_of_nonneg_left
    (p5U7Spatial_native_rough_error_le hN hm eta hs (fun t ht => (hg t ht).1)) hnorm
  have hid : (Real.log (N : ℝ)/(N : ℝ))*p5U7InteriorBandError N eta =
      p5U7InteriorBandError N eta/((N : ℝ)/Real.log (N : ℝ)) := by
    field_simp [hNR.ne',hLN.ne']
    <;> ring
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hnorm,hid] using hh

/-- Mixed-cutoff target/unit/endpoint losses are paid by the existing
original-N explicit reserve. The target logarithm remains log N. -/
theorem p5U7Spatial_target_loss_le {N M : ℕ} (hN : 2 ≤ N) (hMN : M ≤ N) (eta : ℝ)
    (houter : p5U7BoundaryOuterReciprocalMass N ≤ 5) :
    0 ≤ p5U7SpatialInteriorRoughMass N M eta-p5U7SpatialInteriorFullMass N M eta ∧
      p5U7SpatialInteriorRoughMass N M eta-p5U7SpatialInteriorFullMass N M eta ≤
      25*(Real.log (N : ℝ)/Real.log 2+2)*((N : ℝ)/(N : ℝ)^(59/250 : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^(59/250 : ℝ) := Real.rpow_pos_of_pos hNR _
  have hL : 0 ≤ Real.log (N : ℝ)/Real.log 2 := div_nonneg
    (Real.log_natCast_nonneg _) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hrow (t : ℕ × ℕ) (ht : t ∈ p5U7InteriorSelector N eta) :
      0 ≤ (roughCount ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)-
        ((p5U7SpatialGoodRough N M t).card : ℝ) ∧
      (roughCount ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)-
        ((p5U7SpatialGoodRough N M t).card : ℝ) ≤
      (Real.log (N : ℝ)/Real.log 2+2)*((N : ℝ)/(N : ℝ)^(59/250 : ℝ))*
        (1/((t.1*t.2 : ℕ) : ℝ)) := by
    have hto := (Finset.mem_filter.mp ht).1
    have hg := p5U7Mass_outer_geometry hto
    have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
    have hc := (Finset.mem_filter.mp hto).1
    have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
    have hz : (0 : ℝ) < t.2 := by exact_mod_cast hp.pos
    have hy : (0 : ℝ) < (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) := hz.trans hg.2.2.1
    have hxy : (M : ℝ)/((t.1*t.2 : ℕ) : ℝ) ≤ (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hMN) haR.le
    have hgap := p5U7SpatialRough_gap_le (M := M) (show 0 < N by omega) hto
    have hratio1 : 1 ≤ ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/(t.2 : ℝ) :=
      (one_le_div hz).mpr hg.2.2.1.le
    have hratio : ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/(t.2 : ℝ) ≤
        ((N : ℝ)/(N : ℝ)^(59/250 : ℝ))*(1/((t.1*t.2 : ℕ) : ℝ)) := by
      have hh := div_le_div_of_nonneg_left hy.le hA hg.2.1
      convert hh using 1 <;> ring
    have hsmall := div_le_div_of_nonneg_right hxy hz.le
    have hscaled := mul_le_mul_of_nonneg_left hsmall hL
    have hbound := mul_le_mul_of_nonneg_left hratio (show 0 ≤ Real.log (N : ℝ)/Real.log 2+2 by linarith only [hL])
    exact ⟨hgap.1,by nlinarith only [hgap.2,hscaled,hbound,hratio1]⟩
  unfold p5U7SpatialInteriorRoughMass p5U7SpatialInteriorFullMass
  rw [← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_nonneg (fun t ht => (hrow t ht).1),?_⟩
  have hh := Finset.sum_le_sum (fun t ht => (hrow t ht).2)
  have hmass := p5U7ActualInterior_pair_mass_le hN eta houter
  have hfactor : 0 ≤ (Real.log (N : ℝ)/Real.log 2+2)*((N : ℝ)/(N : ℝ)^(59/250 : ℝ)) := by positivity
  have htotal := mul_le_mul_of_nonneg_left hmass hfactor
  rw [← Finset.mul_sum] at hh
  nlinarith only [hh,htotal]

theorem tendsto_p5U7Spatial_actual_target_loss (M : ℕ → ℕ) (eta : ℝ)
    (hMN : ∀ᶠ N : ℕ in atTop,M N ≤ N) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (p5U7SpatialInteriorRoughMass N (M N) eta-p5U7SpatialInteriorFullMass N (M N) eta))
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ p5U7ActualTargetLossCoefficient_tendsto_zero
  · filter_upwards [hMN,p5U7Boundary_eventually_outer_mass_le_five,eventually_ge_atTop (2 : ℕ)] with N hm ho hN
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
      (p5U7Spatial_target_loss_le hN hm eta ho).1
  · filter_upwards [hMN,p5U7Boundary_eventually_outer_mass_le_five,eventually_ge_atTop (2 : ℕ)] with N hm ho hN
    have hh := mul_le_mul_of_nonneg_left (p5U7Spatial_target_loss_le hN hm eta ho).2
      (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    convert hh using 1 <;> dsimp only [p5U7ActualTargetLossCoefficient] <;>
      field_simp [hNR.ne'] <;> ring

end
end ImbalancedChen
