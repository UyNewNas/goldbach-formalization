import ImbalancedChen.PanProductAggregateBudget
import ImbalancedChen.SelectedGridRanges

/-!
# The dynamic product-coordinate grid for Liu--Pan strips

The existing multiplicative grid partitions the original prime coordinates
`(r,q)`.  A Liu--Pan product strip instead has rectangular coordinates
`(r,m)` with `m = r*q`.  Containment of one signed discrepancy region in the
other is not a valid transfer, so this file constructs the required coordinate
change explicitly.

Each product-coordinate cell is definitionally one of the exact
strict-lower/closed-upper strips from `PanProductStrips`.  Positive prime pairs
with product at most `N` have a unique cell, and different cells are disjoint
before any congruence or analytic estimate is applied.  Thus squares,
endpoints and ordered-pair multiplicity are preserved.
-/

namespace ImbalancedChen

noncomputable section

/-- The coordinate change used by the Pan grid: the second coordinate is the
actual product, not the second prime. -/
def panProductCoordinates (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1, p.1 * p.2)

/-- One exact product-coordinate cell.  Its first side restricts `r`; its
second side restricts the product `r*q`. -/
def panProductGridStrip (κ : ℝ) (ij : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  panProductStripPairs
    (multiplicativeGridIocEndpoint κ ij.1)
    (multiplicativeGridIocEndpoint κ (ij.1 + 1))
    (multiplicativeGridIocEndpoint κ ij.2)
    (multiplicativeGridIocEndpoint κ (ij.2 + 1))

/-- Membership is exactly prime-pair membership together with the two
half-open multiplicative sides in the `(r,r*q)` coordinates. -/
theorem mem_panProductGridStrip {κ : ℝ} (hκ : 1 < κ)
    {ij p : ℕ × ℕ} :
    p ∈ panProductGridStrip κ ij ↔
      Nat.Prime p.1 ∧ Nat.Prime p.2 ∧
        p.1 ∈ multiplicativeGridSide κ ij.1 ∧
        p.1 * p.2 ∈ multiplicativeGridSide κ ij.2 := by
  rw [panProductGridStrip, mem_panProductStripPairs,
    multiplicativeGridSide_eq_Ioc hκ,
    multiplicativeGridSide_eq_Ioc hκ]
  simp only [Finset.mem_Ioc]
  tauto

/-- Equivalent rectangular formulation after the literal coordinate map. -/
theorem mem_panProductGridStrip_iff_coordinates {κ : ℝ} (hκ : 1 < κ)
    {ij p : ℕ × ℕ} :
    p ∈ panProductGridStrip κ ij ↔
      Nat.Prime p.1 ∧ Nat.Prime p.2 ∧
        panProductCoordinates p ∈ multiplicativeGridRectangle κ ij := by
  rw [mem_panProductGridStrip hκ]
  simp only [panProductCoordinates, multiplicativeGridRectangle,
    Finset.product_eq_sprod, Finset.mem_product]

/-- Every positive prime pair below the product cap has one and only one
product-coordinate strip.  This includes the diagonal `r=q`. -/
theorem panProductGrid_existsUnique_strip
    {κ : ℝ} (hκ : 1 < κ) {N r q : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hprod : r * q ≤ N) :
    ∃! ij : ℕ × ℕ,
      ij ∈ multiplicativeGridIndices κ N ∧
        (r, q) ∈ panProductGridStrip κ ij := by
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hproduct1 : 1 ≤ r * q := Nat.mul_pos hr.pos hq.pos
  have hrprod : r ≤ r * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left r hq1
  obtain ⟨ij, hij, hunique⟩ :=
    multiplicativeGrid_existsUnique_rectangle
      (κ := κ) (N := (N : ℝ)) (p := (r, r * q)) hκ
      hr1 hproduct1 (by exact_mod_cast hrprod.trans hprod)
      (by exact_mod_cast hprod)
  refine ⟨ij, ⟨hij.1, ?_⟩, ?_⟩
  · exact (mem_panProductGridStrip_iff_coordinates hκ).mpr
      ⟨hr, hq, hij.2⟩
  · intro kl hkl
    apply hunique kl
    exact ⟨hkl.1,
      ((mem_panProductGridStrip_iff_coordinates hκ).mp hkl.2).2.2⟩

/-- Distinct product-coordinate cells are disjoint as prime-pair sets. -/
theorem panProductGridStrip_disjoint {κ : ℝ} (hκ : 1 < κ)
    {ij kl : ℕ × ℕ} (hne : ij ≠ kl) :
    Disjoint (panProductGridStrip κ ij) (panProductGridStrip κ kl) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpij hpkl
  have hcij := ((mem_panProductGridStrip_iff_coordinates hκ).mp hpij).2.2
  have hckl := ((mem_panProductGridStrip_iff_coordinates hκ).mp hpkl).2.2
  exact Finset.disjoint_left.mp
    (multiplicativeGridRectangle_disjoint hκ hne) hcij hckl

/-- Product-coordinate cells which meet the actual half-product source. -/
def actualPanProductGridIndices
    (num den N : ℕ) (T κ : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (multiplicativeGridIndices κ N).filter fun ij =>
    ∃ p ∈ halfProductPairs num den N T,
      p ∈ panProductGridStrip κ ij

/-- Membership in the dynamically selected product grid records both the
ambient logarithmic index bound and an actual source-pair witness.  This is
the interface used when a rectangle estimate is summed only over nonempty
source cells. -/
@[simp] theorem mem_actualPanProductGridIndices
    {num den N : ℕ} {T κ : ℝ} {ij : ℕ × ℕ} :
    ij ∈ actualPanProductGridIndices num den N T κ ↔
      ij ∈ multiplicativeGridIndices κ N ∧
        ∃ p ∈ halfProductPairs num den N T,
          p ∈ panProductGridStrip κ ij := by
  simp only [actualPanProductGridIndices, Finset.mem_filter]

/-- Selecting precisely the cells meeting the source never introduces an
index outside the finite ambient product grid. -/
theorem actualPanProductGridIndices_subset
    (num den N : ℕ) (T κ : ℝ) :
    actualPanProductGridIndices num den N T κ ⊆
      multiplicativeGridIndices κ N := by
  exact Finset.filter_subset _ _

/-- The actual source cells inherit the proved finite logarithmic rectangle
budget.  No geometric or distribution hypothesis is required for this
combinatorial bound. -/
theorem actualPanProductGridIndices_card_le
    (num den N : ℕ) (T κ : ℝ) :
    (actualPanProductGridIndices num den N T κ).card ≤
      (Nat.floor (Real.log (N : ℝ) / Real.log κ) + 1) ^ 2 := by
  exact multiplicativeGrid_subfamily_card_le
    (actualPanProductGridIndices_subset num den N T κ)

/-- The full prime-pair upper cover supplied by the selected product cells. -/
def actualPanProductGridPairs
    (num den N : ℕ) (T κ : ℝ) : Finset (ℕ × ℕ) :=
  (actualPanProductGridIndices num den N T κ).biUnion
    (panProductGridStrip κ)

/-- Every actual source pair has a unique selected product cell.  Selection
adds no duplicate ownership on top of the ambient grid partition. -/
theorem halfProductPair_existsUnique_actualPanProductGridStrip
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ)
    {p : ℕ × ℕ} (hp : p ∈ halfProductPairs num den N T) :
    ∃! ij : ℕ × ℕ,
      ij ∈ actualPanProductGridIndices num den N T κ ∧
        p ∈ panProductGridStrip κ ij := by
  obtain ⟨hr, hq, _, _, _, hprod⟩ := mem_halfProductPairs.mp hp
  obtain ⟨ij, hij, hunique⟩ :=
    panProductGrid_existsUnique_strip hκ hr hq hprod
  refine ⟨ij, ⟨Finset.mem_filter.mpr
    ⟨hij.1, ⟨p, hp, hij.2⟩⟩, hij.2⟩, ?_⟩
  intro kl hkl
  apply hunique kl
  exact ⟨(Finset.mem_filter.mp hkl.1).1, hkl.2⟩

/-- Every actual half-product pair lies in the selected dynamic Pan grid.
The proof uses the product cap itself as the second coordinate bound. -/
theorem halfProductPairs_subset_actualPanProductGridPairs
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) :
    halfProductPairs num den N T ⊆
      actualPanProductGridPairs num den N T κ := by
  classical
  intro p hp
  obtain ⟨ij, hij, _⟩ :=
    halfProductPair_existsUnique_actualPanProductGridStrip hκ hp
  apply Finset.mem_biUnion.mpr
  exact ⟨ij, hij.1, hij.2⟩

/-- Selected product cells are still pairwise disjoint; selection does not
change the exact multiplicity-one partition. -/
theorem actualPanProductGridStrip_disjoint
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ)
    {ij kl : ℕ × ℕ}
    (hij : ij ∈ actualPanProductGridIndices num den N T κ)
    (hkl : kl ∈ actualPanProductGridIndices num den N T κ)
    (hne : ij ≠ kl) :
    Disjoint (panProductGridStrip κ ij) (panProductGridStrip κ kl) :=
  panProductGridStrip_disjoint hκ hne

end

end ImbalancedChen
