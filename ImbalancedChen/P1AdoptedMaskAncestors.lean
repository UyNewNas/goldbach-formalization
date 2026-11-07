import ImbalancedChen.Certificates.PairedV2FullMaskGeometry
import ImbalancedChen.HistoricalPrefixCertificate

/-!
# The actual paired-v2 mask and its reverse-stored ancestors

This is the existing `FullMask.Row`, its frozen `cutoff`, and its actual
open support.  The rank-three image is computed exactly by eliminating
`w`; it is not declared to be an arbitrary supplied ancestor predicate.
The last section evaluates existing historical cap tables on a joint
mesh cell.  It does not assert that any such table instantiates the
manuscript's complete adopted lower policy.
-/

namespace ImbalancedChen.P1AdoptedMaskAncestors

noncomputable section

open Certificates.PairedV2

namespace Mask

/-- The exact three-dimensional projection of one actual adopted row. -/
def ancestor3Support (r : FullMask.Row) : Set (Fin 3 → ℝ) :=
  {y | (tLower (FullMask.indices r).1 : ℝ) < y 0 ∧
    y 0 < (tUpper (FullMask.indices r).1 : ℝ) ∧
    (uLower (FullMask.indices r).2 : ℝ) < y 1 ∧
    y 1 < (uUpper (FullMask.indices r).2 : ℝ) ∧
    (a : ℝ) < y 2 ∧ y 2 < (FullMask.cutoff r : ℝ)}

/-- An explicit witness for the eliminated fourth coordinate. -/
def lift3 (y : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![y 0, y 1, y 2, ((a : ℝ) + y 2) / 2]

theorem project_lift3 (y : Fin 3 → ℝ) :
    historicalPrefixProject (by omega : 3 ≤ 4) (lift3 y) = y := by
  funext i
  fin_cases i <;> rfl

/-- Projection loses precisely the two strict bounds on `w`. -/
theorem support_iff_ancestor3 (r : FullMask.Row) (x : Fin 4 → ℝ) :
    x ∈ FullMask.support r ↔
      historicalPrefixProject (by omega : 3 ≤ 4) x ∈ ancestor3Support r ∧
        (a : ℝ) < x 3 ∧ x 3 < x 2 := by
  change ((tLower (FullMask.indices r).1 : ℝ) < x 0 ∧
    x 0 < (tUpper (FullMask.indices r).1 : ℝ) ∧
    (uLower (FullMask.indices r).2 : ℝ) < x 1 ∧
    x 1 < (uUpper (FullMask.indices r).2 : ℝ) ∧
    (a : ℝ) < x 3 ∧ x 3 < x 2 ∧
    x 2 < (FullMask.cutoff r : ℝ)) ↔
    ((tLower (FullMask.indices r).1 : ℝ) < x 0 ∧
    x 0 < (tUpper (FullMask.indices r).1 : ℝ) ∧
    (uLower (FullMask.indices r).2 : ℝ) < x 1 ∧
    x 1 < (uUpper (FullMask.indices r).2 : ℝ) ∧
    (a : ℝ) < x 2 ∧ x 2 < (FullMask.cutoff r : ℝ)) ∧
    (a : ℝ) < x 3 ∧ x 3 < x 2
  constructor
  · rintro ⟨htl, htr, hul, hur, hw, hwz, hz⟩
    exact ⟨⟨htl, htr, hul, hur, hw.trans hwz, hz⟩, hw, hwz⟩
  · rintro ⟨⟨htl, htr, hul, hur, _ha, hz⟩, hw, hwz⟩
    exact ⟨htl, htr, hul, hur, hw, hwz, hz⟩

theorem lift3_mem_support (r : FullMask.Row) {y : Fin 3 → ℝ}
    (hy : y ∈ ancestor3Support r) : lift3 y ∈ FullMask.support r := by
  apply (support_iff_ancestor3 r (lift3 y)).2
  rw [project_lift3]
  have haz : (a : ℝ) < y 2 := hy.2.2.2.2.1
  refine ⟨hy, ?_, ?_⟩
  · change (a : ℝ) < ((a : ℝ) + y 2) / 2
    linarith
  · change ((a : ℝ) + y 2) / 2 < y 2
    linarith

/-- The forward inclusion and the explicit midpoint lift prove equality
of the real image sets, including the exact strict endpoints. -/
theorem image_support_eq_ancestor3Support (r : FullMask.Row) :
    historicalPrefixProject (by omega : 3 ≤ 4) '' FullMask.support r =
      ancestor3Support r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ((support_iff_ancestor3 r x).1 hx).1
  · intro hy
    exact ⟨lift3 y, lift3_mem_support r hy, project_lift3 y⟩

/-- Eliminating `w` does not merge distinct adopted rows: the two actual
outer mesh coordinates still determine the same decoded row. -/
theorem ancestor3_owner_unique {r s : FullMask.Row} {y : Fin 3 → ℝ}
    (hr : y ∈ ancestor3Support r) (hs : y ∈ ancestor3Support s) : r = s := by
  have hr' := lift3_mem_support r hr
  have hs' := lift3_mem_support s hs
  obtain ⟨hi, hj⟩ := openFibreSupport_unique_indices hr' hs'
  exact FullMask.indices_injective (Prod.ext hi hj)

def ancestor3Region : Set (Fin 3 → ℝ) := ⋃ r, ancestor3Support r

theorem image_region_eq_ancestor3Region :
    historicalPrefixProject (by omega : 3 ≤ 4) '' FullMask.region =
      ancestor3Region := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨r, ((support_iff_ancestor3 r x).1 hr).1⟩
  · intro hy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hy
    exact ⟨lift3 y, Set.mem_iUnion.mpr ⟨r, lift3_mem_support r hr⟩,
      project_lift3 y⟩

theorem ancestor3Region_unique_owner (y : Fin 3 → ℝ) :
    y ∈ ancestor3Region ↔ ∃! r, y ∈ ancestor3Support r := by
  constructor
  · intro hy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hy
    exact ⟨r, hr, fun s hs => ancestor3_owner_unique hs hr⟩
  · rintro ⟨r, hr, _⟩
    exact Set.mem_iUnion.mpr ⟨r, hr⟩

end Mask

/-- The fourth ancestor and its third ancestor retain the *same* real
adopted row.  No primality or admission test is needed for this identity. -/
theorem history_ancestors_mem_same_row (N : ℝ) {k : ℕ}
    (hk : 4 ≤ k) (history : List ℕ) (hlen : history.length = k)
    (r : FullMask.Row)
    (hmask : historicalPrefixProject hk (primeHistoryLogCoordinates N k history) ∈
      FullMask.support r) :
    primeHistoryLogCoordinates N 4 (rosserAncestor 4 history) ∈ FullMask.support r ∧
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
        Mask.ancestor3Support r := by
  constructor
  · rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N hk hlen]
    exact hmask
  · rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N
      (by omega : 3 ≤ k) hlen]
    simpa only [historicalPrefixProject_comp] using
      ((Mask.support_iff_ancestor3 r _).1 hmask).1

/-- A full adopted mask hit gives a unique common owner at ranks four
and three, rather than unrelated existential ancestors. -/
theorem history_region_common_owner (N : ℝ) {k : ℕ}
    (hk : 4 ≤ k) (history : List ℕ) (hlen : history.length = k)
    (hmask : historicalPrefixProject hk (primeHistoryLogCoordinates N k history) ∈
      FullMask.region) :
    ∃! r : FullMask.Row,
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 history) ∈ FullMask.support r ∧
        primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
          Mask.ancestor3Support r := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hmask
  have hanc := history_ancestors_mem_same_row N hk history hlen r hr
  refine ⟨r, hanc, ?_⟩
  intro s hs
  exact Mask.ancestor3_owner_unique hs.2 hanc.2

/-- The missing fourth-coordinate conditions are retained explicitly;
membership in the projected rank-three region alone is insufficient. -/
theorem history_rank4_support_iff (N : ℝ) {k : ℕ}
    (hk : 4 ≤ k) (history : List ℕ) (hlen : history.length = k)
    (r : FullMask.Row) :
    primeHistoryLogCoordinates N 4 (rosserAncestor 4 history) ∈ FullMask.support r ↔
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
        Mask.ancestor3Support r ∧
      (a : ℝ) < primeHistoryLogCoordinates N k history ⟨3, by omega⟩ ∧
      primeHistoryLogCoordinates N k history ⟨3, by omega⟩ <
        primeHistoryLogCoordinates N k history ⟨2, by omega⟩ := by
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N hk hlen,
    Mask.support_iff_ancestor3]
  rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N
    (by omega : 3 ≤ k) hlen]
  simp only [historicalPrefixProject_comp, historicalPrefixProject]

/-- Actual reverse storage is used literally: later primes are prepended.
Both adopted-row memberships are invariant under all later selections. -/
theorem history_support_append_iff (N : ℝ) (later history : List ℕ)
    (hk : 4 ≤ history.length) (r : FullMask.Row) :
    (primeHistoryLogCoordinates N 4 (rosserAncestor 4 (later ++ history)) ∈
        FullMask.support r ∧
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 (later ++ history)) ∈
        Mask.ancestor3Support r) ↔
    (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history) ∈ FullMask.support r ∧
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
        Mask.ancestor3Support r) := by
  rw [rosserAncestor_append 4 later history hk,
    rosserAncestor_append 3 later history (by omega)]

/-- Processing tuples are pulled back to the actual reversed four-prime
list, with no sort or renaming of the adopted mask. -/
theorem tuple_mem_mask_reverse_history (N : ℕ) (p : Fin 4 → ℕ) :
    actualPrimeTupleLog N p ∈ FullMask.region ↔
      primeHistoryLogCoordinates (N : ℝ) 4 [p 3, p 2, p 1, p 0] ∈
        FullMask.region := by
  have heq : primeHistoryLogCoordinates (N : ℝ) 4 [p 3, p 2, p 1, p 0] =
      actualPrimeTupleLog N p := by
    funext i
    fin_cases i <;> rfl
  rw [heq]

/-- A literal tuple in the adopted union supplies the reverse-stored
rank-four history and rank-three ancestor with one unique actual row. -/
theorem tuple_ancestors_unique_owner (N : ℕ) (p : Fin 4 → ℕ)
    (hmask : actualPrimeTupleLog N p ∈ FullMask.region) :
    ∃! r : FullMask.Row,
      primeHistoryLogCoordinates (N : ℝ) 4 [p 3, p 2, p 1, p 0] ∈
        FullMask.support r ∧
      primeHistoryLogCoordinates (N : ℝ) 3 [p 2, p 1, p 0] ∈
        Mask.ancestor3Support r := by
  have hm := (tuple_mem_mask_reverse_history N p).1 hmask
  have hm' : historicalPrefixProject (by omega : 4 ≤ 4)
      (primeHistoryLogCoordinates (N : ℝ) 4 [p 3, p 2, p 1, p 0]) ∈
        FullMask.region := by
    exact hm
  simpa [rosserAncestor] using
    history_region_common_owner (N : ℝ) (by omega : 4 ≤ 4)
      [p 3, p 2, p 1, p 0] (by simp) hm'

/-- The actual adopted geometric license is read on that same history.
This retains the frozen row cutoff and the unchanged `7/3` threshold. -/
theorem history_same_row_argument (N : ℝ) {k : ℕ}
    (hk : 4 ≤ k) (history : List ℕ) (hlen : history.length = k)
    (r : FullMask.Row)
    (hmask : historicalPrefixProject hk (primeHistoryLogCoordinates N k history) ∈
      FullMask.support r) :
    let x := primeHistoryLogCoordinates N 4 (rosserAncestor 4 history)
    (a : ℝ) < x 3 ∧ x 3 < x 2 ∧ x 2 < x 1 ∧ x 1 < (h : ℝ) ∧
      (h : ℝ) < x 0 ∧ x 0 < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - x 0 - x 1 - x 2 - x 3) / x 2 := by
  exact FullMask.row_fibre_argument r
    (history_ancestors_mem_same_row N hk history hlen r hmask).1

/-- Once the actual adopted four-coordinate point also has a historical
mesh owner, both effective ancestor levels are computed from its literal
projected labels.  An unselected fourth cell keeps its third fallback. -/
theorem joint_mask_mesh_ancestor_levels (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N : ℝ) {k : ℕ} (hk : 4 ≤ k)
    (history : List ℕ) (hlen : history.length = k) (r : FullMask.Row)
    (j : Fin 4 → Fin (D.m + 1))
    (hmask : historicalPrefixProject hk (primeHistoryLogCoordinates N k history) ∈
      FullMask.support r)
    (hcell : historicalPrefixProject hk (primeHistoryLogCoordinates N k history) ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
        Mask.ancestor3Support r ∧
      D.level3 N (rosserAncestor 3 history) =
        N ^ (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 4) j) : ℝ) ∧
      D.level4 N (rosserAncestor 4 history) = N ^ (D.cell4 j : ℝ) := by
  refine ⟨(history_ancestors_mem_same_row N hk history hlen r hmask).2, ?_, ?_⟩
  · unfold HistoricalPrefixCapData.level3
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N
      (by omega : 3 ≤ k) hlen]
    have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) hcell
    rw [historicalPrefixProject_comp] at ht3
    rw [D.exponent3_on_cell hab _ _ ht3]
  · unfold HistoricalPrefixCapData.level4
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N hk hlen,
      D.exponent4_on_cell hab _ _ hcell]

end

end ImbalancedChen.P1AdoptedMaskAncestors
