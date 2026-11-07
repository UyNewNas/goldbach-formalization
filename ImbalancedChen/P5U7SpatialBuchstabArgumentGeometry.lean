import ImbalancedChen.P5U7SpatialNativeRoughErrors

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
The actual mixed-cutoff native Buchstab arguments remain in the genuine
original interval [1,132/59], after the required arithmetic lower wall is
proved. This is a coordinate/model identification, not a global Buchstab
Lipschitz claim across the jump below one.
-/
namespace ImbalancedChen
noncomputable section
open Set Filter Topology LiLiuPrereqBuchstab
open Classical

/-- Exact native range and logarithmic denominator geometry on actual
original marked pairs, with independent product cutoff M and target N. -/
theorem p5U7Spatial_buchstab_argument_geometry {N M : ℕ} (hN : 2 ≤ N) (hMN : M ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) {t : ℕ × ℕ} (ht : t ∈ p5U7InteriorSelector N eta)
    (hlower : (t.2 : ℝ) ≤ (M : ℝ)/((t.1*t.2 : ℕ) : ℝ)) :
    Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) ∈ Icc (1 : ℝ) (132/59) ∧
    Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) ∈ Icc (1 : ℝ) (132/59) ∧
    Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) ≤
      Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) ∧
    (59/250 : ℝ)*Real.log (N : ℝ) ≤ Real.log (t.2 : ℝ) := by
  have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hc
  have hp := (mem_chenAdditivePrimeCarrier.mp hp).2.1
  have hq := (mem_chenAdditivePrimeCarrier.mp hq).2.1
  have hz0 : (0 : ℝ) < t.2 := by exact_mod_cast hq.pos
  have hz1 : (1 : ℝ) < t.2 := by exact_mod_cast hq.one_lt
  have hlogz := Real.log_pos hz1
  have haR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hxy : (M : ℝ)/((t.1*t.2 : ℕ) : ℝ) ≤ (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hMN) haR.le
  have hlogxy := Real.log_le_log (hz0.trans_le hlower) hxy
  have horder := (div_le_div_of_nonneg_right hlogxy hlogz.le)
  have hnew1 : 1 ≤ Real.log ((M : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) :=
    (one_le_div hlogz).mpr (Real.log_le_log hz0 hlower)
  have hbox := (p5U7Interior_selector_iff_box hN heta ![t.1,t.2]).mp ht
  obtain ⟨hbox,hregion⟩ := Finset.mem_filter.mp hbox
  have hlogbox := ((mem_actualPrimeBoxTuples_log_iff (show 1 < N by omega) _ _ ![t.1,t.2]).mp hbox).2
  have hs := p5U7Interior_subset_original heta hlogbox hregion
  have hcOmega : p5U7OmegaClosedSupport
      (actualPrimeTupleLog N ![t.1,t.2] 0) (actualPrimeTupleLog N ![t.1,t.2] 1) :=
    ⟨hs.1,hs.2.1,hs.2.2.le⟩
  have harg : Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) =
      p5U7OmegaArgument (actualPrimeTupleLog N ![t.1,t.2] 0) (actualPrimeTupleLog N ![t.1,t.2] 1) := by
    simpa only [p5U7OmegaArgument,actualPrimeTupleLog,Matrix.cons_val_zero,Matrix.cons_val_one] using
      p5U7_original_log_argument hN hp.pos hq.two_le
  have hOld : Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))/Real.log (t.2 : ℝ) ∈ Icc (1 : ℝ) (132/59) := by
    rw [harg]
    exact ⟨(p5U7Omega_closed_geometry hcOmega).2.2.2.2.1,
      (p5U7Omega_closed_geometry hcOmega).2.2.2.2.2⟩
  have hden := Real.log_le_log (Real.rpow_pos_of_pos hNR (59/250 : ℝ)) hg.2.1
  rw [Real.log_rpow hNR] at hden
  exact ⟨⟨hnew1,horder.trans hOld.2⟩,hOld,horder,hden⟩

end
end ImbalancedChen
