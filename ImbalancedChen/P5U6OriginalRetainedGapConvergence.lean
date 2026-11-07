import ImbalancedChen.P5U6OriginalIntegralGapConvergence
import ImbalancedChen.P5U6OriginalRetainedRationalCertificates

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The ORIGINAL fixed17572-row mask keeps its literal Ico ownership and its
single (t,u)->U6(u,t) transpose. Every actual row boundary is a proper
coordinate line and is proved null. At an off-wall point, generated owner
cells eventually separate from every absent row or lie inside a present
row. These are actual rational classifier conclusions, not stability
premises. Together with the true lower-h248 kernel limits and integrable
domination they prove retained rational enclosure-gap convergence for
the actual full mask, E0 and E1. No moving-mask limit is asserted.
-/

namespace ImbalancedChen.P5U6OriginalRetainedGapConvergence

noncomputable section

open Set MeasureTheory Filter Topology Classical
open scoped BigOperators
open Part5OriginalUpsilon5CausalDictionary
open P5U6OriginalRationalBoxBounds P5U6OriginalRationalIntegralCertificates
open P5U6OriginalOwnerKernelConvergence P5U6OriginalUniformEnvelopeBounds
open P5U6OriginalRetainedRationalCertificates
open P5U6OriginalPairedMaskNativeHarmonicSourceOnly
open P5U6AdoptedH248BindingSourceOnly
open P5Z.U1011OriginalPairedFixedMaskHarmonic (e0Rows e1Rows)
open Certificates.PairedV2

def OffRowWalls (x : Fin 2 → ℝ) : Prop := ∀ r : ActualRow,
  x 0 ≠ (rowULo r : ℝ) ∧ x 0 ≠ (rowUHi r : ℝ) ∧
    x 1 ≠ (rowTLo r : ℝ) ∧ x 1 ≠ (rowTHi r : ℝ)

theorem ae_off_actual_row_walls : ∀ᵐ x : Fin 2 → ℝ ∂volume, OffRowWalls x := by
  have hcoord (i : Fin 2) (c : ℝ) : ∀ᵐ x : Fin 2 → ℝ ∂volume, x i ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using currentChenUpsilon6_coordinateWall_volume_zero i c
  apply ae_all_iff.mpr
  intro r
  filter_upwards [hcoord 0 (rowULo r), hcoord 0 (rowUHi r),
    hcoord 1 (rowTLo r), hcoord 1 (rowTHi r)] with x h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem eventually_owner_contained_row {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) (r : ActualRow)
    (hoff : OffRowWalls x) (hr : (x 1, x 0) ∈ FullMask.P1E0E1.pairCell r) :
    ∀ᶠ n in atTop, Contained (gridBox n (owner n x hx)) r := by
  have hrow := (row_dictionary r x).1 hr
  have h0 := corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 0
  have h1 := corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 1
  have huL : (rowULo r : ℝ) < x 0 := lt_of_le_of_ne hrow.1 (hoff r).1.symm
  have htL : (rowTLo r : ℝ) < x 1 := lt_of_le_of_ne hrow.2.2.1 (hoff r).2.2.1.symm
  filter_upwards [h0.1.eventually (Ioi_mem_nhds huL),
    h0.2.eventually (Iio_mem_nhds hrow.2.1), h1.1.eventually (Ioi_mem_nhds htL),
    h1.2.eventually (Iio_mem_nhds hrow.2.2.2)] with n hu hu' ht ht'
  exact ⟨by exact_mod_cast hu.le, by exact_mod_cast hu'.le,
    by exact_mod_cast ht.le, by exact_mod_cast ht'.le⟩

theorem eventually_owner_separated_row {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) (r : ActualRow)
    (hoff : OffRowWalls x) (hr : (x 1, x 0) ∉ FullMask.P1E0E1.pairCell r) :
    ∀ᶠ n in atTop, Separated (gridBox n (owner n x hx)) r := by
  have h0 := corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 0
  have h1 := corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 1
  by_cases huL : (rowULo r : ℝ) ≤ x 0
  · by_cases huH : x 0 < (rowUHi r : ℝ)
    · by_cases htL : (rowTLo r : ℝ) ≤ x 1
      · by_cases htH : x 1 < (rowTHi r : ℝ)
        · exact (hr ((row_dictionary r x).2 ⟨huL, huH, htL, htH⟩)).elim
        · have hh : (rowTHi r : ℝ) < x 1 :=
            lt_of_le_of_ne (le_of_not_gt htH) (hoff r).2.2.2.symm
          filter_upwards [h1.1.eventually (Ioi_mem_nhds hh)] with n hn
          exact Or.inr (Or.inr (Or.inr (by exact_mod_cast hn.le)))
      · have hh : x 1 < (rowTLo r : ℝ) := lt_of_not_ge htL
        filter_upwards [h1.2.eventually (Iio_mem_nhds hh)] with n hn
        exact Or.inr (Or.inr (Or.inl (by exact_mod_cast hn.le)))
    · have hh : (rowUHi r : ℝ) < x 0 :=
        lt_of_le_of_ne (le_of_not_gt huH) (hoff r).2.1.symm
      filter_upwards [h0.1.eventually (Ioi_mem_nhds hh)] with n hn
      exact Or.inr (Or.inl (by exact_mod_cast hn.le))
  · have hh : x 0 < (rowULo r : ℝ) := lt_of_not_ge huL
    filter_upwards [h0.2.eventually (Iio_mem_nhds hh)] with n hn
    exact Or.inl (by exact_mod_cast hn.le)

theorem eventually_owner_retained_inner (S : Finset ActualRow) {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) (hret : x ∈ retainedDomain S)
    (hoff : OffRowWalls x) (hcap : x 0 + x 1 < (833 / 2500 : ℝ)) :
    ∀ᶠ n in atTop, owner n x hx ∈ retainedInner S n := by
  have hrows : ∀ᶠ n in atTop, ∀ r ∈ S, Separated (gridBox n (owner n x hx)) r := by
    apply (eventually_all_finset S).mpr
    intro r hr
    apply eventually_owner_separated_row hx r hoff
    intro hrow
    exact hret.2 ((actual_mask_dictionary S x).2 ⟨r, hr, hrow⟩)
  filter_upwards [P5U6OriginalIntegralGapConvergence.eventually_owner_inner hx hcap,
    hrows] with n hn hrow
  exact Finset.mem_filter.mpr ⟨hn, hrow⟩

theorem retained_owner_outer (S : Finset ActualRow) {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) (hret : x ∈ retainedDomain S) (n : ℕ) :
    owner n x hx ∈ retainedOuter S n := by
  obtain ⟨j, hj, hxj⟩ := retained_outer_cover S n hret
  have heq : j = owner n x hx := cell_unique hxj (owner_mem n x hx)
  exact heq ▸ hj

def retainedSampleGap (S : Finset ActualRow) (n : ℕ) (x : Fin 2 → ℝ) : ℝ :=
  sample n (retainedOuter S n) (densityUpper n n) x -
    sample n (retainedInner S n) (densityLower n n) x

theorem retainedSampleGap_tendsto_zero (S : Finset ActualRow) (x : Fin 2 → ℝ)
    (hoff : OffRowWalls x)
    (hne : ∀ k : Fin 201, currentChenUpsilon6OrdinaryProfile x ≠ floorGrid k.val)
    (hproduct : x 0 + x 1 ≠ (833 / 2500 : ℝ)) :
    Tendsto (fun n => retainedSampleGap S n x) atTop (𝓝 0) := by
  by_cases hx : x ∈ currentChenUpsilon6LogRectangle
  · by_cases hD : x ∈ currentChenUpsilon6LogDomain 0
    · by_cases hm : x ∈ ascendingPointMask S
      · obtain ⟨r, hr, hxr⟩ := (actual_mask_dictionary S x).1 hm
        have hni (n : ℕ) : owner n x hx ∉ retainedInner S n := by
          intro hi
          exact (retained_inner_cell_subset S n hi (owner_mem n x hx)).2 hm
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_owner_contained_row hx r hoff hxr] with n hn
        have hno : owner n x hx ∉ retainedOuter S n := by
          intro ho
          exact (Finset.mem_filter.mp ho).2 ⟨r, hr, hn⟩
        rw [retainedSampleGap, sample_eq_owner n (retainedOuter S n) _ hx,
          sample_eq_owner n (retainedInner S n) _ hx, if_neg hno, if_neg (hni n), sub_self]
      · have hret : x ∈ retainedDomain S := ⟨hD, hm⟩
        have hcap : x 0 + x 1 < (833 / 2500 : ℝ) :=
          lt_of_le_of_ne (by simpa only [sub_zero] using hD.2) hproduct
        have hlims := generated_density_bounds_tendsto hD hne
        have ht : Tendsto (fun n => (densityUpper n n (owner n x hx) : ℝ) -
            (densityLower n n (owner n x hx) : ℝ)) atTop (𝓝 0) := by
          simpa only [sub_self] using hlims.2.sub hlims.1
        apply ht.congr'
        filter_upwards [eventually_owner_retained_inner S hx hret hoff hcap] with n hn
        rw [retainedSampleGap, sample_eq_owner n (retainedOuter S n) _ hx,
          sample_eq_owner n (retainedInner S n) _ hx,
          if_pos (retained_owner_outer S hx hret n), if_pos hn]
    · have hcap : (833 / 2500 : ℝ) < x 0 + x 1 := by
        apply lt_of_not_ge
        intro hc
        exact hD ⟨hx, by simpa only [sub_zero] using hc⟩
      have hni (n : ℕ) : owner n x hx ∉ retainedInner S n := by
        intro hi
        exact hD (retained_inner_cell_subset S n hi (owner_mem n x hx)).1
      apply tendsto_const_nhds.congr'
      filter_upwards [P5U6OriginalIntegralGapConvergence.eventually_owner_not_outer hx hcap] with n hn
      have hno : owner n x hx ∉ retainedOuter S n := fun ho => hn (Finset.mem_filter.mp ho).1
      rw [retainedSampleGap, sample_eq_owner n (retainedOuter S n) _ hx,
        sample_eq_owner n (retainedInner S n) _ hx, if_neg hno, if_neg (hni n), sub_self]
  · apply tendsto_const_nhds.congr
    intro n
    rw [retainedSampleGap, sample_eq_zero_outside n (retainedOuter S n) _ hx,
      sample_eq_zero_outside n (retainedInner S n) _ hx, sub_self]

theorem ae_retainedSampleGap_tendsto_zero (S : Finset ActualRow) :
    ∀ᵐ x : Fin 2 → ℝ ∂volume, Tendsto (fun n => retainedSampleGap S n x) atTop (𝓝 0) := by
  have hp : ∀ᵐ x : Fin 2 → ℝ ∂volume, x 0 + x 1 ≠ (833 / 2500 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using currentChenUpsilon6_productWall_volume_zero (833 / 2500 : ℝ)
  filter_upwards [ae_off_actual_row_walls, ae_profile_ne_all_knots, hp] with x hr hk hc
  exact retainedSampleGap_tendsto_zero S x hr hk hc

theorem retainedSampleGap_integrable (S : Finset ActualRow) (n : ℕ) :
    Integrable (retainedSampleGap S n) :=
  (sample_integrable n (retainedOuter S n) _).sub (sample_integrable n (retainedInner S n) _)

theorem retainedSampleGap_dominated (S : Finset ActualRow) (n : ℕ) (x : Fin 2 → ℝ) :
    ‖retainedSampleGap S n x‖ ≤ domination x :=
  sample_difference_dominated n n (retainedInner S n) (retainedOuter S n)
    (fun _ hj => (Finset.mem_filter.mp hj).1) (fun _ hj => (Finset.mem_filter.mp hj).1) x

theorem integral_retainedSampleGap_eq (S : Finset ActualRow) (n : ℕ) :
    (∫ x, retainedSampleGap S n x) =
      ((retainedRationalUpper S n n - retainedRationalLower S n n : ℚ) : ℝ) := by
  rw [retainedSampleGap,
    integral_sub (sample_integrable n (retainedOuter S n) _) (sample_integrable n (retainedInner S n) _),
    sample_integral, sample_integral]
  simp only [retainedRationalUpper, retainedRationalLower, Rat.cast_sub]

/-- True retained U6 convergence for a fixed subfamily of the actual
original rows. All row-wall geometry and DCT inputs are conclusions. -/
theorem tendsto_retained_diagonal_gap (S : Finset ActualRow) :
    Tendsto (fun n : ℕ => ((retainedRationalUpper S n n - retainedRationalLower S n n : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence domination
    (fun n => (retainedSampleGap_integrable S n).aestronglyMeasurable) domination_integrable
    (fun n => Eventually.of_forall (retainedSampleGap_dominated S n))
    (ae_retainedSampleGap_tendsto_zero S)
  simpa only [integral_retainedSampleGap_eq, integral_zero] using ht

theorem tendsto_actual_adopted_gap :
    Tendsto (fun n : ℕ => ((retainedRationalUpper Finset.univ n n -
      retainedRationalLower Finset.univ n n : ℚ) : ℝ)) atTop (𝓝 0) :=
  tendsto_retained_diagonal_gap Finset.univ
theorem tendsto_actual_e0_gap :
    Tendsto (fun n : ℕ => ((retainedRationalUpper e0Rows n n -
      retainedRationalLower e0Rows n n : ℚ) : ℝ)) atTop (𝓝 0) :=
  tendsto_retained_diagonal_gap e0Rows
theorem tendsto_actual_e1_gap :
    Tendsto (fun n : ℕ => ((retainedRationalUpper e1Rows n n -
      retainedRationalLower e1Rows n n : ℚ) : ℝ)) atTop (𝓝 0) :=
  tendsto_retained_diagonal_gap e1Rows

end

end ImbalancedChen.P5U6OriginalRetainedGapConvergence
