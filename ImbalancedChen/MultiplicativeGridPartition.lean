import ImbalancedChen.BoundaryCellContainment
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# A finite, exact multiplicative grid

For `κ > 1` the side with index `i` is the exact natural restriction of
`[κ ^ i, κ ^ (i + 1))`, namely the natural interval with the two ceiling
endpoints. Every positive integer has exactly one index. To cover all
positive coordinates at most `N`, take `floor (log N / log κ) + 1` sides.
The number of indexed rectangles is exactly the square of this quantity.

The selected rectangles are full rectangles, without intersection with
`[1,N]²` or with the curved source. The last edge lies strictly above `N`
and at most `κ * N`. Thus the construction retains the entire exterior
envelope, including pairs whose product exceeds `N`. Empty integer sides
are harmless, and integer grid endpoints belong to the cell on the right.

This file supplies the finite partition and its exact logarithmic count.
It does not assume or prove a rectangle distribution theorem, or duplicate
the convolution envelopes constructed elsewhere.
-/

namespace ImbalancedChen

noncomputable section

/-- The canonical index of a real coordinate at least one. -/
def multiplicativeGridIndex (κ x : ℝ) : ℕ :=
  Nat.floor (Real.logb κ x)

/-- Exact natural restriction of a real half-open multiplicative side. -/
def multiplicativeGridSide (κ : ℝ) (i : ℕ) : Finset ℕ :=
  Finset.Ico (Nat.ceil (κ ^ i)) (Nat.ceil (κ ^ (i + 1)))

/-- One more than the index of the inclusive upper coordinate cutoff. -/
def multiplicativeGridSideCount (κ N : ℝ) : ℕ :=
  multiplicativeGridIndex κ N + 1

/-- The finite set of rectangle indices, including the cell containing `N`. -/
def multiplicativeGridIndices (κ N : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (multiplicativeGridSideCount κ N)).product
    (Finset.range (multiplicativeGridSideCount κ N))

/-- A full natural rectangle; no coordinate or product cutoff is imposed. -/
def multiplicativeGridRectangle (κ : ℝ) (ij : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (multiplicativeGridSide κ ij.1).product (multiplicativeGridSide κ ij.2)

/-- The entire finite grid carrier, retaining all points of every cell. -/
def multiplicativeGridCarrier (κ N : ℝ) : Finset (ℕ × ℕ) :=
  (multiplicativeGridIndices κ N).biUnion (multiplicativeGridRectangle κ)

/-- Ceiling rounding is exactly equivalent to the original half-open side. -/
theorem mem_multiplicativeGridSide {κ : ℝ} {i n : ℕ} :
    n ∈ multiplicativeGridSide κ i ↔
      κ ^ i ≤ (n : ℝ) ∧ (n : ℝ) < κ ^ (i + 1) := by
  simp only [multiplicativeGridSide, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]

/-- A coordinate at least one lies in its canonical half-open real side. -/
theorem multiplicativeGridIndex_bounds {κ x : ℝ}
    (hκ : 1 < κ) (hx : 1 ≤ x) :
    κ ^ multiplicativeGridIndex κ x ≤ x ∧
      x < κ ^ (multiplicativeGridIndex κ x + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlo : (multiplicativeGridIndex κ x : ℝ) ≤ Real.logb κ x :=
    Nat.floor_le (Real.logb_nonneg hκ hx)
  have hhi : Real.logb κ x < ((multiplicativeGridIndex κ x + 1 : ℕ) : ℝ) := by
    simpa only [multiplicativeGridIndex, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (Real.logb κ x))
  constructor
  · simpa only [Real.rpow_natCast] using
      (Real.le_logb_iff_rpow_le hκ hx0).mp hlo
  · simpa only [Real.rpow_natCast] using
      (Real.logb_lt_iff_lt_rpow hκ hx0).mp hhi

/-- The half-open inequalities determine the index uniquely, even at edges. -/
theorem multiplicativeGridIndex_eq_of_bounds {κ x : ℝ} {i : ℕ}
    (hκ : 1 < κ) (hi : κ ^ i ≤ x ∧ x < κ ^ (i + 1)) :
    multiplicativeGridIndex κ x = i := by
  have hκ0 : 0 < κ := lt_trans zero_lt_one hκ
  have hx0 : 0 < x := (pow_pos hκ0 i).trans_le hi.1
  have hlo : (i : ℝ) ≤ Real.logb κ x :=
    (Real.le_logb_iff_rpow_le hκ hx0).mpr (by
      simpa only [Real.rpow_natCast] using hi.1)
  have hhi : Real.logb κ x < ((i + 1 : ℕ) : ℝ) :=
    (Real.logb_lt_iff_lt_rpow hκ hx0).mpr (by
      simpa only [Real.rpow_natCast] using hi.2)
  apply (Nat.floor_eq_iff ((Nat.cast_nonneg i).trans hlo)).mpr
  exact ⟨hlo, by simpa only [Nat.cast_add, Nat.cast_one] using hhi⟩

/-- At an exact real grid edge, the index is the index on its right.
In particular the first edge `1 = κ ^ 0` belongs to cell zero. -/
theorem multiplicativeGridIndex_pow {κ : ℝ} (hκ : 1 < κ) (i : ℕ) :
    multiplicativeGridIndex κ (κ ^ i) = i := by
  apply multiplicativeGridIndex_eq_of_bounds hκ
  refine ⟨le_rfl, ?_⟩
  rw [pow_succ]
  have hp : 0 < κ ^ i := pow_pos (zero_lt_one.trans hκ) i
  simpa only [mul_one] using (mul_lt_mul_of_pos_left hκ hp)

/-- A finite index cutoff is exactly a strict real grid-edge cutoff. -/
theorem multiplicativeGridIndex_lt_iff {κ x : ℝ} {k : ℕ}
    (hκ : 1 < κ) (hx : 1 ≤ x) :
    multiplicativeGridIndex κ x < k ↔ x < κ ^ k := by
  rw [multiplicativeGridIndex, Nat.floor_lt (Real.logb_nonneg hκ hx)]
  simpa only [Real.rpow_natCast] using
    (Real.logb_lt_iff_lt_rpow hκ (zero_lt_one.trans_le hx)
      (y := (k : ℝ)))

/-- Every positive natural number is in the side with its canonical index. -/
theorem mem_multiplicativeGridSide_index {κ : ℝ} {n : ℕ}
    (hκ : 1 < κ) (hn : 1 ≤ n) :
    n ∈ multiplicativeGridSide κ (multiplicativeGridIndex κ (n : ℝ)) := by
  apply mem_multiplicativeGridSide.mpr
  exact multiplicativeGridIndex_bounds hκ (by exact_mod_cast hn)

/-- Natural side membership recovers the canonical index. -/
theorem multiplicativeGridIndex_eq_of_mem {κ : ℝ} {i n : ℕ}
    (hκ : 1 < κ) (hn : n ∈ multiplicativeGridSide κ i) :
    multiplicativeGridIndex κ (n : ℝ) = i :=
  multiplicativeGridIndex_eq_of_bounds hκ (mem_multiplicativeGridSide.mp hn)

/-- Every natural point of a grid side is positive. -/
theorem multiplicativeGridSide_one_le {κ : ℝ} {i n : ℕ}
    (hκ : 1 < κ) (hn : n ∈ multiplicativeGridSide κ i) : 1 ≤ n := by
  have hpos : (0 : ℝ) < (n : ℝ) :=
    (pow_pos (zero_lt_one.trans hκ) i).trans_le (mem_multiplicativeGridSide.mp hn).1
  have hnpos : 0 < n := by exact_mod_cast hpos
  omega

/-- Distinct side indices have no common natural point. -/
theorem multiplicativeGridSide_disjoint {κ : ℝ} (hκ : 1 < κ)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (multiplicativeGridSide κ i) (multiplicativeGridSide κ j) := by
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  exact hij ((multiplicativeGridIndex_eq_of_mem hκ hni).symm.trans
    (multiplicativeGridIndex_eq_of_mem hκ hnj))

/-- The canonical side index is bounded by the logarithm of the coordinate. -/
theorem multiplicativeGridIndex_le_log {κ x : ℝ}
    (hκ : 1 < κ) (hx : 1 ≤ x) :
    (multiplicativeGridIndex κ x : ℝ) ≤ Real.log x / Real.log κ :=
  Nat.floor_le (Real.logb_nonneg hκ hx)

/-- All coordinates in `[1,N]` have indices in the selected finite range. -/
theorem multiplicativeGridIndex_lt_sideCount {κ x N : ℝ}
    (hκ : 1 < κ) (hx : 1 ≤ x) (hxN : x ≤ N) :
    multiplicativeGridIndex κ x < multiplicativeGridSideCount κ N := by
  have hlog := Real.logb_le_logb_of_le hκ (zero_lt_one.trans_le hx) hxN
  have hf := Nat.floor_mono hlog
  exact Nat.lt_succ_of_le hf

/-- The real-valued side count is at most `log N / log κ + 1`. -/
theorem multiplicativeGridSideCount_le_log_add_one {κ N : ℝ}
    (hκ : 1 < κ) (hN : 1 ≤ N) :
    (multiplicativeGridSideCount κ N : ℝ) ≤ Real.log N / Real.log κ + 1 := by
  have h := multiplicativeGridIndex_le_log hκ hN
  simpa only [multiplicativeGridSideCount, Nat.cast_add, Nat.cast_one] using
    add_le_add h (le_rfl : (1 : ℝ) ≤ 1)

/-- The last edge is strictly above `N`, and extends no farther than `κ * N`.
In particular, the cell containing the inclusive endpoint `N` is not cut. -/
theorem multiplicativeGrid_last_edge {κ N : ℝ}
    (hκ : 1 < κ) (hN : 1 ≤ N) :
    N < κ ^ multiplicativeGridSideCount κ N ∧
      κ ^ multiplicativeGridSideCount κ N ≤ κ * N := by
  obtain ⟨hl, hu⟩ := multiplicativeGridIndex_bounds hκ hN
  refine ⟨hu, ?_⟩
  change κ ^ (multiplicativeGridIndex κ N + 1) ≤ κ * N
  rw [pow_succ, mul_comm (κ ^ multiplicativeGridIndex κ N)]
  exact mul_le_mul_of_nonneg_left hl (lt_trans zero_lt_one hκ).le

/-- Exact rectangle membership in the two original real half-open sides. -/
theorem mem_multiplicativeGridRectangle {κ : ℝ} {ij p : ℕ × ℕ} :
    p ∈ multiplicativeGridRectangle κ ij ↔
      (κ ^ ij.1 ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) < κ ^ (ij.1 + 1)) ∧
      (κ ^ ij.2 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) < κ ^ (ij.2 + 1)) := by
  simp only [multiplicativeGridRectangle, Finset.product_eq_sprod, Finset.mem_product,
    mem_multiplicativeGridSide]

/-- Every full grid rectangle is contained in the closed cell used by the
crossing-collar theorem, with exactly the same lower endpoints and ratio. -/
theorem multiplicativeGridRectangle_mem_boundaryCell {κ : ℝ} {ij p : ℕ × ℕ}
    (hp : p ∈ multiplicativeGridRectangle κ ij) :
    multiplicativeBoundaryCell (κ ^ ij.1) (κ ^ ij.2) κ
      ((p.1 : ℝ), (p.2 : ℝ)) := by
  obtain ⟨hr, hq⟩ := mem_multiplicativeGridRectangle.mp hp
  apply multiplicativeBoundaryCell_of_halfOpen
  refine ⟨hr.1, ?_, hq.1, ?_⟩
  · simpa only [pow_succ, mul_comm] using hr.2
  · simpa only [pow_succ, mul_comm] using hq.2

/-- A natural point in a rectangle determines both of its indices. -/
theorem multiplicativeGridRectangle_index_eq {κ : ℝ} {ij p : ℕ × ℕ}
    (hκ : 1 < κ) (hp : p ∈ multiplicativeGridRectangle κ ij) :
    (multiplicativeGridIndex κ (p.1 : ℝ),
      multiplicativeGridIndex κ (p.2 : ℝ)) = ij := by
  have h := Finset.mem_product.mp hp
  exact Prod.ext (multiplicativeGridIndex_eq_of_mem hκ h.1)
    (multiplicativeGridIndex_eq_of_mem hκ h.2)

/-- All the full rectangles are pairwise disjoint, not only their intersections
with the original source region. -/
theorem multiplicativeGridRectangle_disjoint {κ : ℝ} (hκ : 1 < κ)
    {ij kl : ℕ × ℕ} (hne : ij ≠ kl) :
    Disjoint (multiplicativeGridRectangle κ ij) (multiplicativeGridRectangle κ kl) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hne ((multiplicativeGridRectangle_index_eq hκ hp).symm.trans
    (multiplicativeGridRectangle_index_eq hκ hq))

/-- Exact coverage and uniqueness for all positive natural coordinates at most
`N`. The rectangle in this statement is full, not clipped to these bounds. -/
theorem multiplicativeGrid_existsUnique_rectangle {κ N : ℝ} {p : ℕ × ℕ}
    (hκ : 1 < κ) (hp1 : 1 ≤ p.1) (hp2 : 1 ≤ p.2)
    (hp1N : (p.1 : ℝ) ≤ N) (hp2N : (p.2 : ℝ) ≤ N) :
    ∃! ij : ℕ × ℕ, ij ∈ multiplicativeGridIndices κ N ∧
      p ∈ multiplicativeGridRectangle κ ij := by
  let ij := (multiplicativeGridIndex κ (p.1 : ℝ),
    multiplicativeGridIndex κ (p.2 : ℝ))
  have hi : ij ∈ multiplicativeGridIndices κ N := by
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_range.mpr
        (multiplicativeGridIndex_lt_sideCount hκ (by exact_mod_cast hp1) hp1N)
    · exact Finset.mem_range.mpr
        (multiplicativeGridIndex_lt_sideCount hκ (by exact_mod_cast hp2) hp2N)
  have hp : p ∈ multiplicativeGridRectangle κ ij :=
    Finset.mem_product.mpr ⟨mem_multiplicativeGridSide_index hκ hp1,
      mem_multiplicativeGridSide_index hκ hp2⟩
  refine ⟨ij, ⟨hi, hp⟩, ?_⟩
  intro kl hkl
  exact (multiplicativeGridRectangle_index_eq hκ hkl.2).symm

/-- The full finite carrier contains every positive pair in `[1,N]²`. -/
theorem mem_multiplicativeGridCarrier {κ N : ℝ} {p : ℕ × ℕ}
    (hκ : 1 < κ) (hp1 : 1 ≤ p.1) (hp2 : 1 ≤ p.2)
    (hp1N : (p.1 : ℝ) ≤ N) (hp2N : (p.2 : ℝ) ≤ N) :
    p ∈ multiplicativeGridCarrier κ N := by
  obtain ⟨ij, hij, _⟩ :=
    multiplicativeGrid_existsUnique_rectangle hκ hp1 hp2 hp1N hp2N
  exact Finset.mem_biUnion.mpr ⟨ij, hij.1, hij.2⟩

/-- Exact description of the full exterior carrier. Its upper coordinate
edge is `κ ^ sideCount`, rather than `N`, and there is no product cutoff. -/
theorem mem_multiplicativeGridCarrier_iff {κ N : ℝ} {p : ℕ × ℕ}
    (hκ : 1 < κ) :
    p ∈ multiplicativeGridCarrier κ N ↔
      (1 ≤ p.1 ∧ (p.1 : ℝ) < κ ^ multiplicativeGridSideCount κ N) ∧
      (1 ≤ p.2 ∧ (p.2 : ℝ) < κ ^ multiplicativeGridSideCount κ N) := by
  constructor
  · intro hp
    obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hp
    have hi := Finset.mem_product.mp hij
    have hpi := Finset.mem_product.mp hpij
    have hp1 := multiplicativeGridSide_one_le hκ hpi.1
    have hp2 := multiplicativeGridSide_one_le hκ hpi.2
    refine ⟨⟨hp1, ?_⟩, ⟨hp2, ?_⟩⟩
    · apply (multiplicativeGridIndex_lt_iff hκ (by exact_mod_cast hp1)).mp
      rw [multiplicativeGridIndex_eq_of_mem hκ hpi.1]
      exact Finset.mem_range.mp hi.1
    · apply (multiplicativeGridIndex_lt_iff hκ (by exact_mod_cast hp2)).mp
      rw [multiplicativeGridIndex_eq_of_mem hκ hpi.2]
      exact Finset.mem_range.mp hi.2
  · rintro ⟨⟨hp1, hp1u⟩, ⟨hp2, hp2u⟩⟩
    let ij := (multiplicativeGridIndex κ (p.1 : ℝ),
      multiplicativeGridIndex κ (p.2 : ℝ))
    apply Finset.mem_biUnion.mpr
    refine ⟨ij, ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr
          ((multiplicativeGridIndex_lt_iff hκ (by exact_mod_cast hp1)).mpr hp1u)
      · exact Finset.mem_range.mpr
          ((multiplicativeGridIndex_lt_iff hκ (by exact_mod_cast hp2)).mpr hp2u)
    · exact Finset.mem_product.mpr ⟨mem_multiplicativeGridSide_index hκ hp1,
        mem_multiplicativeGridSide_index hκ hp2⟩

/-- Exact number of indexed rectangles. Empty natural rectangles need not be
removed: retaining them preserves this equality and gives an upper count. -/
theorem multiplicativeGridIndices_card (κ N : ℝ) :
    (multiplicativeGridIndices κ N).card =
      (Nat.floor (Real.log N / Real.log κ) + 1) ^ 2 := by
  simp only [multiplicativeGridIndices, Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
    multiplicativeGridSideCount, multiplicativeGridIndex, Real.logb, pow_two]

/-- The exact floor count is bounded by the requested ceiling count. -/
theorem multiplicativeGridIndices_card_le_ceil (κ N : ℝ) :
    (multiplicativeGridIndices κ N).card ≤
      (Nat.ceil (Real.log N / Real.log κ) + 1) ^ 2 := by
  rw [multiplicativeGridIndices_card, pow_two, pow_two]
  have h := Nat.add_le_add_right (Nat.floor_le_ceil (Real.log N / Real.log κ)) 1
  exact Nat.mul_le_mul h h

/-- Any selected subfamily, in particular the cells intersecting a curved
region, obeys the same rectangle budget. -/
theorem multiplicativeGrid_subfamily_card_le {κ N : ℝ} {s : Finset (ℕ × ℕ)}
    (hs : s ⊆ multiplicativeGridIndices κ N) :
    s.card ≤ (Nat.floor (Real.log N / Real.log κ) + 1) ^ 2 := by
  calc
    s.card ≤ (multiplicativeGridIndices κ N).card := Finset.card_le_card hs
    _ = _ := multiplicativeGridIndices_card κ N

end

end ImbalancedChen
