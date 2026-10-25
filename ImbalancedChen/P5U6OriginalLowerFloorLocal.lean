import ImbalancedChen.P5U6OriginalRationalBoxBounds
import ImbalancedChen.P5U6RetainedExplicitBuffer

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The ACTUAL LOWER adopted h248 extrema are attained, bounded, and collapse
inside one open grid atom. This is not the upper-H248 array. The scalar
lookup and its actual affine-profile pullback are locally constant away
from the literal 201 knot walls; those proper affine walls are already
proved null. Singleton values remain present in the underlying function.
No floor-continuity, boundary-null or limiting-gap premise is assumed.
-/

namespace ImbalancedChen.P5U6OriginalLowerFloorLocal

noncomputable section

open Set Filter Topology MeasureTheory Classical
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open P5Z.U1011H248Partition
open P5U6OriginalRationalBoxBounds P5U6AdoptedH248BindingSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly P5U6RetainedExplicitBufferSourceOnly

theorem lowerValue_bounds (a : AtomState) : 0 ≤ lowerValue a ∧ lowerValue a ≤ 1 := by
  refine ⟨lowerValue_nonneg a, ?_⟩
  cases a with
  | none => norm_num [lowerValue]
  | some b =>
    have h := adoptedAtomValue_le_one b
    rw [← lowerValue_cast] at h
    exact_mod_cast h

theorem interval_range {l u : ℚ} (hlu : l ≤ u) :
    0 ≤ hLower l u ∧ hLower l u ≤ hUpper l u ∧ hUpper l u ≤ 1 := by
  have hV := lowerValues_nonempty hlu
  obtain ⟨a, ha, heqa⟩ := Finset.mem_image.mp (Finset.min'_mem (lowerValues l u) hV)
  obtain ⟨b, hb, heqb⟩ := Finset.mem_image.mp (Finset.max'_mem (lowerValues l u) hV)
  have hA := lowerValue_bounds a
  have hB := lowerValue_bounds b
  rw [heqa] at hA
  rw [heqb] at hB
  simp only [hLower, hUpper, dif_pos hlu]
  exact ⟨hA.1, Finset.min'_le_max' _ hV, hB.2⟩

theorem lower_attained {l u : ℚ} (hl : 2 ≤ l) (hlu : l ≤ u) :
    ∃ s : ℚ, l ≤ s ∧ s ≤ u ∧ adoptedH248Floor (s : ℝ) = (hLower l u : ℝ) := by
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem (lowerValues l u) (lowerValues_nonempty hlu))
  obtain ⟨s, hsl, hsu, hs⟩ := P5Z.LiteralH248IntervalBounds.state_witness_of_reachable
    hlu (Finset.mem_filter.mp ha).2
  refine ⟨s, hsl, hsu, ?_⟩
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hl.trans hsl
  rw [adoptedFloor_eq_lowerValue hs2 hs]
  have hq : lowerValue a = hLower l u := by
    simpa only [hLower, dif_pos hlu] using heq
  exact_mod_cast hq

theorem upper_attained {l u : ℚ} (hl : 2 ≤ l) (hlu : l ≤ u) :
    ∃ s : ℚ, l ≤ s ∧ s ≤ u ∧ adoptedH248Floor (s : ℝ) = (hUpper l u : ℝ) := by
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp
    (Finset.max'_mem (lowerValues l u) (lowerValues_nonempty hlu))
  obtain ⟨s, hsl, hsu, hs⟩ := P5Z.LiteralH248IntervalBounds.state_witness_of_reachable
    hlu (Finset.mem_filter.mp ha).2
  refine ⟨s, hsl, hsu, ?_⟩
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hl.trans hsl
  rw [adoptedFloor_eq_lowerValue hs2 hs]
  have hq : lowerValue a = hUpper l u := by
    simpa only [hUpper, dif_pos hlu] using heq
  exact_mod_cast hq

theorem refinement {l u l' u' : ℚ} (hl2 : 2 ≤ l)
    (hl : l ≤ l') (hlu : l' ≤ u') (hu : u' ≤ u) :
    hLower l u ≤ hLower l' u' ∧ hUpper l' u' ≤ hUpper l u := by
  obtain ⟨s, hsl, hsu, hs⟩ := lower_attained (hl2.trans hl) hlu
  obtain ⟨t, htl, htu, ht⟩ := upper_attained (hl2.trans hl) hlu
  have hLs := (adoptedFloor_interval hl2 (l := l) (u := u) (s := (s : ℝ))
    (by exact_mod_cast hl.trans hsl) (by exact_mod_cast hsu.trans hu)).1
  have hUt := (adoptedFloor_interval hl2 (l := l) (u := u) (s := (t : ℝ))
    (by exact_mod_cast hl.trans htl) (by exact_mod_cast htu.trans hu)).2
  rw [hs] at hLs
  rw [ht] at hUt
  exact ⟨by exact_mod_cast hLs, by exact_mod_cast hUt⟩

/-- Rational queries strictly inside one atom have precisely its literal
lower-array value; no table monotonicity is used. -/
theorem exact_open_interval {l u : ℚ} (hl2 : 2 ≤ l) (hlu : l ≤ u)
    (i : Fin 200) (hl : P5Z.LiteralH248IntervalBounds.grid i.val < l)
    (hu : u < P5Z.LiteralH248IntervalBounds.grid (i.val + 1)) :
    hLower l u = lowerAtom i ∧ hUpper l u = lowerAtom i := by
  have hstate (s : ℚ) (hsl : l ≤ s) (hsu : s ≤ u) :
      (s : ℝ) ∈ scalarCell (some (.inl i)) := by
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hl2.trans hsl
    have hgL : floorGrid i.val < (s : ℝ) := by
      rw [← P5Z.LiteralH248IntervalBounds.grid_cast]
      exact_mod_cast hl.trans_le hsl
    have hgU : (s : ℝ) < floorGrid (i.val + 1) := by
      rw [← P5Z.LiteralH248IntervalBounds.grid_cast]
      exact_mod_cast hsu.trans_lt hu
    have hg5 : floorGrid (i.val + 1) ≤ 5 := by
      have hi : ((i.val + 1 : ℕ) : ℝ) ≤ 200 := by exact_mod_cast (show i.val + 1 ≤ 200 by omega)
      dsimp [floorGrid]
      linarith
    change max 2 (s : ℝ) ∈ Icc 1 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
    rw [max_eq_right hs2]
    exact ⟨⟨by linarith, hgU.le.trans hg5⟩, hgL, hgU⟩
  obtain ⟨s, hsl, hsu, hs⟩ := lower_attained hl2 hlu
  obtain ⟨t, htl, htu, ht⟩ := upper_attained hl2 hlu
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hl2.trans hsl
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast hl2.trans htl
  have hsval := adoptedFloor_eq_lowerValue hs2 (hstate s hsl hsu)
  have htval := adoptedFloor_eq_lowerValue ht2 (hstate t htl htu)
  rw [hs] at hsval
  rw [ht] at htval
  exact ⟨by exact_mod_cast hsval, by exact_mod_cast htval⟩

theorem exists_open_atom {s : ℝ} (hs : s ∈ Icc (2 : ℝ) (1323 / 417))
    (hne : ∀ j : Fin 201, s ≠ floorGrid j.val) :
    ∃ i : Fin 200, s ∈ Ioo (floorGrid i.val) (floorGrid (i.val + 1)) := by
  obtain ⟨b, hb⟩ := exists_upperAtom_of_mem
    (show s ∈ Icc (1 : ℝ) 5 from ⟨by linarith [hs.1], hs.2.trans (by norm_num)⟩)
  cases b with
  | inl i => exact ⟨i, hb.2⟩
  | inr j => exact (hne j hb.2).elim

/-- A concrete local constant neighborhood of the actual lower lookup. -/
theorem locally_constant_adoptedFloor {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (1323 / 417))
    (hne : ∀ j : Fin 201, s ≠ floorGrid j.val) :
    ∀ᶠ t in 𝓝 s, adoptedH248Floor t = adoptedH248Floor s := by
  obtain ⟨i, hi⟩ := exists_open_atom hs hne
  have hs2 : 2 < s := lt_of_le_of_ne hs.1 (by
    intro heq
    exact hne ⟨50, by norm_num⟩ (by simpa [floorGrid] using heq.symm))
  have hs5 : s < 5 := hs.2.trans_lt (by norm_num)
  have hval {t : ℝ} (ht : t ∈ Ioo (floorGrid i.val) (floorGrid (i.val + 1)))
      (ht2 : 2 ≤ t) (ht5 : t ≤ 5) : adoptedH248Floor t = (lowerAtom i : ℝ) := by
    apply adoptedFloor_eq_lowerValue ht2
    change max 2 t ∈ Icc 1 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
    rw [max_eq_right ht2]
    exact ⟨⟨by linarith, ht5⟩, ht⟩
  filter_upwards [Ioo_mem_nhds hi.1 hi.2, Ioo_mem_nhds hs2 hs5] with t ht h25
  exact (hval ht h25.1.le h25.2.le).trans (hval hi hs.1 hs5.le).symm

theorem continuousAt_adoptedFloor {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (1323 / 417))
    (hne : ∀ j : Fin 201, s ≠ floorGrid j.val) : ContinuousAt adoptedH248Floor s := by
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ => adoptedH248Floor s) s).congr_of_eventuallyEq
  exact (locally_constant_adoptedFloor hs hne).symm

/-- Converging rational interval endpoints eventually recover the EXACT
actual lower-table value off knots. The later generated-grid proof supplies
these endpoint convergences; no limiting envelope gap is an input here. -/
theorem eventually_interval_exact (L U : ℕ → ℚ) {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (1323 / 417))
    (hne : ∀ j : Fin 201, s ≠ floorGrid j.val)
    (hL2 : ∀ n, 2 ≤ L n) (hLU : ∀ n, L n ≤ U n)
    (hL : Tendsto (fun n => (L n : ℝ)) atTop (𝓝 s))
    (hU : Tendsto (fun n => (U n : ℝ)) atTop (𝓝 s)) :
    ∀ᶠ n in atTop, (hLower (L n) (U n) : ℝ) = adoptedH248Floor s ∧
      (hUpper (L n) (U n) : ℝ) = adoptedH248Floor s := by
  obtain ⟨i, hi⟩ := exists_open_atom hs hne
  have hstate : s ∈ scalarCell (some (.inl i)) := by
    change max 2 s ∈ Icc 1 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
    rw [max_eq_right hs.1]
    exact ⟨⟨by linarith [hs.1], hs.2.trans (by norm_num)⟩, hi⟩
  have hvalue : adoptedH248Floor s = (lowerAtom i : ℝ) :=
    adoptedFloor_eq_lowerValue hs.1 hstate
  filter_upwards [hL.eventually (Ioi_mem_nhds hi.1),
    hU.eventually (Iio_mem_nhds hi.2)] with n hnL hnU
  have hQL : P5Z.LiteralH248IntervalBounds.grid i.val < L n := by
    have hR : (P5Z.LiteralH248IntervalBounds.grid i.val : ℝ) < (L n : ℝ) := by
      simpa only [P5Z.LiteralH248IntervalBounds.grid_cast] using hnL
    exact_mod_cast hR
  have hQU : U n < P5Z.LiteralH248IntervalBounds.grid (i.val + 1) := by
    have hR : (U n : ℝ) < (P5Z.LiteralH248IntervalBounds.grid (i.val + 1) : ℝ) := by
      simpa only [P5Z.LiteralH248IntervalBounds.grid_cast] using hnU
    exact_mod_cast hR
  have h := exact_open_interval (hL2 n) (hLU n) i hQL hQU
  rw [h.1, h.2, hvalue]
  exact ⟨rfl, rfl⟩

/-- Actual profile knot walls are proper affine lines, already paid by
the original U6 wall theorem. The actual lower function is a.e. continuous
after pullback on the true product domain, with no boundary premise. -/
theorem ae_continuousAt_adopted_profile :
    ∀ᵐ x : Fin 2 → ℝ ∂volume.restrict (currentChenUpsilon6LogDomain 0),
      ContinuousAt (fun y => adoptedH248Floor (currentChenUpsilon6OrdinaryProfile y)) x := by
  filter_upwards [ae_restrict_of_ae ae_profile_ne_all_knots,
    ae_restrict_mem (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain 0)] with x hne hx
  have hs := P5U6RunboEnhancedFloorInterfaceSourceOnly.profile_range (by norm_num) hx
  have hp : Continuous currentChenUpsilon6OrdinaryProfile := by
    unfold currentChenUpsilon6OrdinaryProfile
    fun_prop
  exact (continuousAt_adoptedFloor hs hne).comp x hp.continuousAt

end

end ImbalancedChen.P5U6OriginalLowerFloorLocal
