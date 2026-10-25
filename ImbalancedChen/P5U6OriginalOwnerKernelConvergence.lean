import ImbalancedChen.P5U6OriginalLowerFloorLocal
import ImbalancedChen.P5U6OriginalUniformLogTail
import ImbalancedChen.P5U6OriginalRationalIntegralCertificates

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual generated U6 owner corners, residuals and positive denominators
converge. On the original product domain the rational query endpoints
remain in [2,1323/417]. The lower-table interval becomes its one actual
open-atom value off the proper affine knot walls; uniform real log tails
pay the moving Taylor queries. Both true original kernel bounds and their
nonnegative densities converge pointwise, without any continuity premise.
This module supplies endpoints, not yet the final DCT integral-gap theorem.
-/

namespace ImbalancedChen.P5U6OriginalOwnerKernelConvergence

noncomputable section

open Set Filter Topology Classical
open Part5OriginalUpsilon5CausalDictionary
open P2ContinuousSieveRational
open P5U6OriginalRationalBoxBounds P5U6OriginalRationalIntegralCertificates
open P5U6OriginalLowerFloorLocal P5U6OriginalUniformLogTail
open P5U6AdoptedH248BindingSourceOnly P5U6RetainedAdoptedIntegralSourceOnly

theorem full_rectangle_residual_margin {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) : (14 / 125 : ℝ) ≤ originalResidual x := by
  obtain ⟨hu, hu', ht, ht'⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
  unfold originalResidual
  linarith only [hu', ht']

theorem grid_residual_margin (n : ℕ) (j : Index n) : 14 / 125 ≤ (gridBox n j).rLo := by
  have hu := (corner_bounds n j 0).2.2
  have ht := (corner_bounds n j 1).2.2
  dsimp [hi] at hu ht
  change 14 / 125 ≤ 1 / 2 - upperCorner n j 0 - upperCorner n j 1
  linarith only [hu, ht]

theorem grid_queries_range (n : ℕ) {j : Index n} (hj : j ∈ outer n) :
    2 ≤ (gridBox n j).sLo ∧ (gridBox n j).sLo ≤ (gridBox n j).sHi ∧
      (gridBox n j).sHi ≤ 1323 / 417 := by
  have hcap := (Finset.mem_filter.mp hj).2
  have hu := corner_bounds n j 0
  have ht := corner_bounds n j 1
  have hR : (gridBox n j).rLo ≤ (gridBox n j).rHi := by
    dsimp [gridBox, Box.rLo, Box.rHi]
    linarith only [hu.2.1, ht.2.1]
  have hs2 : 2 ≤ (gridBox n j).sHi := by
    change 2 ≤ (1 / 2 - lowerCorner n j 0 - lowerCorner n j 1) / (417 / 5000 : ℚ)
    apply (le_div_iff₀ (by norm_num)).mpr
    change lowerCorner n j 0 + lowerCorner n j 1 ≤ 833 / 2500 at hcap
    linarith only [hcap]
  have hsU : (gridBox n j).sHi ≤ 1323 / 417 := by
    change (1 / 2 - lowerCorner n j 0 - lowerCorner n j 1) / (417 / 5000 : ℚ) ≤ 1323 / 417
    apply (div_le_iff₀ (by norm_num)).mpr
    dsimp [lo] at hu ht
    linarith only [hu.1, ht.1]
  exact ⟨le_max_left _ _, max_le hs2
    (div_le_div_of_nonneg_right hR (by norm_num)), hsU⟩

def owner (n : ℕ) (x : Fin 2 → ℝ) (hx : x ∈ currentChenUpsilon6LogRectangle) : Index n :=
  Classical.choose (rectangle_cell_cover n hx)
theorem owner_mem (n : ℕ) (x : Fin 2 → ℝ) (hx : x ∈ currentChenUpsilon6LogRectangle) :
    x ∈ cell n (owner n x hx) := Classical.choose_spec (rectangle_cell_cover n hx)

theorem corner_tendsto (j : ∀ n, Index n) {x : Fin 2 → ℝ}
    (hx : ∀ n, x ∈ cell n (j n)) (i : Fin 2) :
    Tendsto (fun n => (lowerCorner n (j n) i : ℝ)) atTop (𝓝 (x i)) ∧
      Tendsto (fun n => (upperCorner n (j n) i : ℝ)) atTop (𝓝 (x i)) := by
  have hcell (n : ℕ) : (fun _ : Fin 1 => x i) ∈
      logPrimeMeshCell (lo i : ℝ) (hi i : ℝ) n (fun _ => j n i) := by
    apply mem_logPrimeMeshCell.mpr
    intro v
    simpa only [lowerCorner, upperCorner, point_cast, logPrimeMeshLo, logPrimeMeshHi]
      using mem_logPrimeBox.mp (hx n) i
  have hL := tendsto_logPrimeMeshLo_apply (lo i : ℝ) (hi i : ℝ) (fun n _ => j n i) hcell 0
  have hU := tendsto_logPrimeMeshHi_apply (lo i : ℝ) (hi i : ℝ) (fun n _ => j n i) hcell 0
  exact ⟨by simpa only [lowerCorner, point_cast, logPrimeMeshLo] using hL,
    by simpa only [upperCorner, point_cast, logPrimeMeshHi] using hU⟩

theorem residual_tendsto (j : ∀ n, Index n) {x : Fin 2 → ℝ}
    (hx : ∀ n, x ∈ cell n (j n)) :
    Tendsto (fun n => ((gridBox n (j n)).rLo : ℝ)) atTop (𝓝 (originalResidual x)) ∧
      Tendsto (fun n => ((gridBox n (j n)).rHi : ℝ)) atTop (𝓝 (originalResidual x)) := by
  have h0 := corner_tendsto j hx 0
  have h1 := corner_tendsto j hx 1
  constructor
  · simpa only [gridBox, Box.rLo, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, originalResidual]
      using ((tendsto_const_nhds.sub h0.2).sub h1.2 :
        Tendsto (fun n => (1 / 2 : ℝ) - (upperCorner n (j n) 0 : ℝ) - upperCorner n (j n) 1)
          atTop (𝓝 ((1 / 2 : ℝ) - x 0 - x 1)))
  · simpa only [gridBox, Box.rHi, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, originalResidual]
      using ((tendsto_const_nhds.sub h0.1).sub h1.1 :
        Tendsto (fun n => (1 / 2 : ℝ) - (lowerCorner n (j n) 0 : ℝ) - lowerCorner n (j n) 1)
          atTop (𝓝 ((1 / 2 : ℝ) - x 0 - x 1)))

theorem denominator_tendsto (j : ∀ n, Index n) {x : Fin 2 → ℝ}
    (hx : ∀ n, x ∈ cell n (j n)) :
    Tendsto (fun n => ((gridBox n (j n)).denLo : ℝ)) atTop
        (𝓝 (originalResidual x * x 0 * x 1)) ∧
      Tendsto (fun n => ((gridBox n (j n)).denHi : ℝ)) atTop
        (𝓝 (originalResidual x * x 0 * x 1)) := by
  have h0 := corner_tendsto j hx 0
  have h1 := corner_tendsto j hx 1
  have hR := residual_tendsto j hx
  exact ⟨by simpa only [Box.denLo, gridBox, Rat.cast_mul] using (hR.1.mul h0.1).mul h1.1,
    by simpa only [Box.denHi, gridBox, Rat.cast_mul] using (hR.2.mul h0.2).mul h1.2⟩

theorem query_tendsto (j : ∀ n, Index n) {x : Fin 2 → ℝ}
    (hx : ∀ n, x ∈ cell n (j n)) (hD : x ∈ currentChenUpsilon6LogDomain 0) :
    Tendsto (fun n => ((gridBox n (j n)).sLo : ℝ)) atTop
        (𝓝 (currentChenUpsilon6OrdinaryProfile x)) ∧
      Tendsto (fun n => ((gridBox n (j n)).sHi : ℝ)) atTop
        (𝓝 (currentChenUpsilon6OrdinaryProfile x)) := by
  have hR := residual_tendsto j hx
  have hs2 := (P5U6RunboEnhancedFloorInterfaceSourceOnly.profile_range (by norm_num) hD).1
  have heq : originalResidual x / (417 / 5000 : ℝ) = currentChenUpsilon6OrdinaryProfile x := rfl
  have hL := tendsto_const_nhds.max (hR.1.div_const (417 / 5000 : ℝ))
  have hU := hR.2.div_const (417 / 5000 : ℝ)
  constructor
  · simpa only [Box.sLo, Rat.cast_max, Rat.cast_ofNat, Rat.cast_div, heq,
      max_eq_right hs2] using hL
  · simpa only [Box.sHi, Rat.cast_div, Rat.cast_ofNat, heq] using hU

theorem moving_logLower_tendsto (q : ℕ → ℚ) {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (1323 / 417))
    (hq : ∀ n, q n ∈ Icc (2 : ℚ) (1323 / 417))
    (ht : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n => (logLower n (q n) : ℝ)) atTop (𝓝 (Real.log (s - 1))) := by
  have hl : Tendsto (fun n => Real.log ((q n : ℝ) - 1)) atTop (𝓝 (Real.log (s - 1))) :=
    (Real.continuousAt_log (by linarith [hs.1] : s - 1 ≠ 0)).tendsto.comp
      (ht.sub_const 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hl.sub tendsto_rate) hl
  · intro n
    have h := real_log_errors_le_rate n (q n) (hq n).1 (hq n).2
    linarith only [h.2.1]
  · intro n
    exact (log_bounds n (q n) (hq n).1).1

theorem moving_logUpper_tendsto (q : ℕ → ℚ) {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (1323 / 417))
    (hq : ∀ n, q n ∈ Icc (2 : ℚ) (1323 / 417))
    (ht : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun n => (logUpper n (q n) : ℝ)) atTop (𝓝 (Real.log (s - 1))) := by
  have hl : Tendsto (fun n => Real.log ((q n : ℝ) - 1)) atTop (𝓝 (Real.log (s - 1))) :=
    (Real.continuousAt_log (by linarith [hs.1] : s - 1 ≠ 0)).tendsto.comp
      (ht.sub_const 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl
    (by simpa only [add_zero] using hl.add tendsto_rate)
  · intro n
    exact (log_bounds n (q n) (hq n).1).2
  · intro n
    have h := real_log_errors_le_rate n (q n) (hq n).1 (hq n).2
    linarith only [h.2.2.2]

/-- The generated owner, not an assumed endpoint approximation, supplies
both original R-denominator kernel limits on every off-knot domain point. -/
theorem generated_kernel_bounds_tendsto {x : Fin 2 → ℝ}
    (hD : x ∈ currentChenUpsilon6LogDomain 0)
    (hne : ∀ k : Fin 201, currentChenUpsilon6OrdinaryProfile x ≠ floorGrid k.val) :
    Tendsto (fun n => ((gridBox n (owner n x hD.1)).kernelLower n : ℝ)) atTop
        (𝓝 (adoptedKernel x)) ∧
      Tendsto (fun n => ((gridBox n (owner n x hD.1)).kernelUpper n : ℝ)) atTop
        (𝓝 (adoptedKernel x)) := by
  let j : ∀ n, Index n := fun n => owner n x hD.1
  have hx (n : ℕ) : x ∈ cell n (j n) := owner_mem n x hD.1
  have hq := query_tendsto j hx hD
  have hd := denominator_tendsto j hx
  have hs := P5U6RunboEnhancedFloorInterfaceSourceOnly.profile_range (by norm_num) hD
  have hqr (n : ℕ) := grid_queries_range n (domain_cell_is_outer n hD (hx n))
  have hLoRange (n : ℕ) : (gridBox n (j n)).sLo ∈ Icc (2 : ℚ) (1323 / 417) :=
    ⟨(hqr n).1, (hqr n).2.1.trans (hqr n).2.2⟩
  have hHiRange (n : ℕ) : (gridBox n (j n)).sHi ∈ Icc (2 : ℚ) (1323 / 417) :=
    ⟨(hqr n).1.trans (hqr n).2.1, (hqr n).2.2⟩
  have hfloor := eventually_interval_exact (fun n => (gridBox n (j n)).sLo)
    (fun n => (gridBox n (j n)).sHi) hs hne (fun n => (hqr n).1)
      (fun n => (hqr n).2.1) hq.1 hq.2
  have hFL : Tendsto (fun n => (hLower (gridBox n (j n)).sLo (gridBox n (j n)).sHi : ℝ))
      atTop (𝓝 (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hfloor] with n hn
    exact hn.1.symm
  have hFU : Tendsto (fun n => (hUpper (gridBox n (j n)).sLo (gridBox n (j n)).sHi : ℝ))
      atTop (𝓝 (adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hfloor] with n hn
    exact hn.2.symm
  have hNL := ((moving_logLower_tendsto _ hs hLoRange hq.1).add hFL).const_mul 4
  have hNU := ((moving_logUpper_tendsto _ hs hHiRange hq.2).add hFU).const_mul 4
  obtain ⟨hu, ht⟩ := currentChenUpsilon6LogRectangle_coordinates_pos hD.1
  have hR : 0 < originalResidual x := lt_of_lt_of_le (by norm_num)
    (full_rectangle_residual_margin hD.1)
  have hden : originalResidual x * x 0 * x 1 ≠ 0 := by positivity
  have hKL := hNL.div hd.2 hden
  have hKU := hNU.div hd.1 hden
  rw [adoptedKernel_eq_original_log]
  exact ⟨by simpa only [Box.kernelLower, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_ofNat, j] using hKL,
    by simpa only [Box.kernelUpper, Rat.cast_div, Rat.cast_mul,
      Rat.cast_add, Rat.cast_ofNat, j] using hKU⟩

theorem generated_density_bounds_tendsto {x : Fin 2 → ℝ}
    (hD : x ∈ currentChenUpsilon6LogDomain 0)
    (hne : ∀ k : Fin 201, currentChenUpsilon6OrdinaryProfile x ≠ floorGrid k.val) :
    Tendsto (fun n => (densityLower n n (owner n x hD.1) : ℝ)) atTop
        (𝓝 (adoptedKernel x)) ∧
      Tendsto (fun n => (densityUpper n n (owner n x hD.1) : ℝ)) atTop
        (𝓝 (adoptedKernel x)) := by
  have h := generated_kernel_bounds_tendsto hD hne
  have hK := adoptedKernel_nonneg (by norm_num) hD
  exact ⟨by simpa only [densityLower, Rat.cast_max, Rat.cast_zero, max_eq_right hK]
      using tendsto_const_nhds.max h.1,
    by simpa only [densityUpper, Rat.cast_max, Rat.cast_zero, max_eq_right hK]
      using tendsto_const_nhds.max h.2⟩

end

end ImbalancedChen.P5U6OriginalOwnerKernelConvergence
