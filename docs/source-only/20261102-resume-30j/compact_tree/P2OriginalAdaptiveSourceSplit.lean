import ImbalancedChen.P2OriginalInitialClosedTree

/-!
SOURCEONLY / UNCOMPILED / BROAD P2.4 OPEN.

Literal split-axis scan, integer midpoint, and side order from the original
`certify_extended_prefix.py:main`. These operations use the RAW current
producer rectangle, including the seed's z0 lower endpoints. A strict
comparison preserves the incumbent on ties, exactly as the original loop.
The uncertainty heap chooses WHICH parent is split; it does not change this
per-parent transition. Its missing 2M selection history is not reconstructed.
-/

namespace ImbalancedChen.P2OriginalAdaptiveSourceSplitSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly

/-- Exact source cross-product comparison; no floating widths. -/
def chooseWider (c : SeedCell) (incumbent candidate : Fin 3) : Fin 3 :=
  if (c.2 candidate - c.1 candidate) * c.1 incumbent >
      (c.2 incumbent - c.1 incumbent) * c.1 candidate
  then candidate else incumbent

/-- Literal source loop: axis=0, then candidates 1 and 2. -/
def originalAxis (c : SeedCell) : Fin 3 :=
  chooseWider c (chooseWider c 0 1) 2

/-- Exact rational interpretation used by the historical independent driver. -/
def relativeSpan (c : SeedCell) (i : Fin 3) : ℚ :=
  ((c.2 i - c.1 i : ℤ) : ℚ) / (c.1 i : ℚ)

/-- Positivity of the actual lower coordinates licenses precisely the source
cross multiplication. No order of upper coordinates is needed here. -/
theorem relativeSpan_lt_iff (c : SeedCell) (i j : Fin 3)
    (hi : 0 < c.1 i) (hj : 0 < c.1 j) :
    relativeSpan c i < relativeSpan c j ↔
      (c.2 j - c.1 j) * c.1 i > (c.2 i - c.1 i) * c.1 j := by
  have hiq : (0 : ℚ) < (c.1 i : ℚ) := by exact_mod_cast hi
  have hjq : (0 : ℚ) < (c.1 j : ℚ) := by exact_mod_cast hj
  unfold relativeSpan
  rw [div_lt_div_iff₀ hiq hjq]
  constructor <;> intro h <;> exact_mod_cast h

theorem chooseWider_eq_relativeSpan (c : SeedCell) (i j : Fin 3)
    (hi : 0 < c.1 i) (hj : 0 < c.1 j) :
    chooseWider c i j =
      if relativeSpan c i < relativeSpan c j then j else i := by
  unfold chooseWider
  rw [← relativeSpan_lt_iff c i j hi hj]

/-- The equality case keeps the earlier axis, rather than changing priority. -/
theorem chooseWider_keeps_tie (c : SeedCell) (i j : Fin 3)
    (hi : 0 < c.1 i) (hj : 0 < c.1 j)
    (htie : relativeSpan c i = relativeSpan c j) :
    chooseWider c i j = i := by
  rw [chooseWider_eq_relativeSpan c i j hi hj,htie,if_neg (lt_irrefl _)]

private theorem chooseWider_span (c : SeedCell) (i j : Fin 3)
    (hi : 0 < c.1 i) (hj : 0 < c.1 j) :
    relativeSpan c (chooseWider c i j) =
      max (relativeSpan c i) (relativeSpan c j) := by
  rw [chooseWider_eq_relativeSpan c i j hi hj]
  by_cases h : relativeSpan c i < relativeSpan c j
  · rw [if_pos h,max_eq_right h.le]
  · rw [if_neg h,max_eq_left (le_of_not_gt h)]

/-- The original strict scan and the independently written rational-width
max use the same largest span; the tie behavior is fixed above. -/
theorem originalAxis_span (c : SeedCell) (hpos : ∀ i, 0 < c.1 i) :
    relativeSpan c (originalAxis c) =
      max (max (relativeSpan c 0) (relativeSpan c 1)) (relativeSpan c 2) := by
  unfold originalAxis
  rw [chooseWider_span c _ _ (hpos _) (hpos _),
    chooseWider_span c _ _ (hpos _) (hpos _)]

theorem originalAxis_span_maximal (c : SeedCell) (hpos : ∀ i, 0 < c.1 i)
    (i : Fin 3) : relativeSpan c i ≤ relativeSpan c (originalAxis c) := by
  rw [originalAxis_span c hpos]
  fin_cases i
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- Python integer floor midpoint, at the exact original integer coordinates.
All actual coordinates are positive, and Lean's Int division agrees here. -/
def originalMidpoint (c : SeedCell) : ℤ :=
  (c.1 (originalAxis c) + c.2 (originalAxis c)) / 2

/-- The producer asserts strict interior before creating these two children.
An integer width of at least two proves that assertion, including odd widths. -/
theorem originalMidpoint_interior (c : SeedCell)
    (hwidth : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)) :
    c.1 (originalAxis c) < originalMidpoint c ∧
      originalMidpoint c < c.2 (originalAxis c) := by
  unfold originalMidpoint
  omega

/-- `side==0` updates the upper endpoint; it is emitted BEFORE side==1. -/
def sourceLeft (c : SeedCell) : SeedCell :=
  (c.1,Function.update c.2 (originalAxis c) (originalMidpoint c))

/-- `side==1` updates the lower endpoint; all other coordinates are retained. -/
def sourceRight (c : SeedCell) : SeedCell :=
  (Function.update c.1 (originalAxis c) (originalMidpoint c),c.2)

def sourceChildren (c : SeedCell) : List SeedCell := [sourceLeft c,sourceRight c]

def sourceSplitTree (c : SeedCell) : ClosedCutTree :=
  .split (originalAxis c) (originalMidpoint c) .leaf .leaf

/-- The closed-tree min/max updates are EXACTLY the original raw assignments
on a genuine source midpoint; this is not merely equality of covered unions. -/
theorem integerLeafBoxes_sourceSplitTree (c : SeedCell)
    (hwidth : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)) :
    integerLeafBoxes (sourceSplitTree c) c.1 c.2 = sourceChildren c := by
  have hmid := originalMidpoint_interior c hwidth
  simp only [sourceSplitTree,integerLeafBoxes,sourceChildren,sourceLeft,sourceRight,
    leftIntegerUpper,rightIntegerLower,min_eq_right hmid.2.le,max_eq_right hmid.1.le]
  rfl

/-- Original side order and every closed-domain portion are identified, with
neither an assumed cover nor any hypothesis on the kernel's leaf integral. -/
theorem closedLeaves_sourceSplitTree (c : SeedCell)
    (hwidth : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)) :
    closedLeaves (sourceSplitTree c) (rootCell c) =
      (sourceChildren c).map rootCell := by
  rw [compact_closedLeaves_eq_integer_boxes,
    integerLeafBoxes_sourceSplitTree c hwidth]

/-- Exact source parent-removal/two-child integral identity for the literal
source split. It does not pay either child's numerical upper charge. -/
theorem source_split_integral_identity (c : SeedCell)
    (hwidth : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c)) :
    (∫ t in rootCell c, compactKernel t) =
      (((sourceChildren c).map rootCell).map
        (fun s => ∫ t in s, compactKernel t)).sum := by
  have hmeas : MeasurableSet (rootCell c) :=
    measurableSet_compactRegion.inter measurableSet_Icc
  have hsub : rootCell c ⊆ compactRegion := inter_subset_left
  rw [integral_eq_sum_closedLeaves (sourceSplitTree c) hmeas hsub,
    closedLeaves_sourceSplitTree c hwidth]

end
end ImbalancedChen.P2OriginalAdaptiveSourceSplitSourceOnly
