import ImbalancedChen.P5OldFifthOneCoordinateVertexChord

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED / ZERO FORMAL CREDIT.

The exact five-coordinate barycentric chord is expanded as a 32-leaf
recursive tree over the actual grid1600 Phase5 child. We work on its
CLOSED closure because endpoint replacement reaches right-hand faces;
the original half-open child is a subset. No vertex integral, 1/32
tensor moment, or archived d value is asserted by this file.
-/

namespace ImbalancedChen.P5OldFifthFiveCoordinateTree

noncomputable section
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord

abbrev Point := Fin 5 → ℝ

def closedChildBox (raw : FifthWireRow) (c : ChildIndex) : Set Point :=
  {t | ∀ i : Fin 5,
    childLeft raw c i ≤ t i ∧ t i ≤ childRight raw c i}

theorem childBox_subset_closed (raw : FifthWireRow) (c : ChildIndex) :
    childBox raw c ⊆ closedChildBox raw c := by
  intro t ht i
  have hi : childLeft raw c i ≤ t i ∧ t i < childRight raw c i := ht i
  exact ⟨hi.1, hi.2.le⟩

theorem coordinateFraction_bounds_closed (raw : FifthWireRow)
    (c : ChildIndex) (i : Fin 5) (t : Point)
    (ht : t ∈ closedChildBox raw c) :
    0 ≤ coordinateFraction raw c i ∧ coordinateFraction raw c i ≤ 1 := by
  have hi := ht i
  have hs := child_span_pos raw c i
  constructor
  · exact div_nonneg (sub_nonneg.mpr hi.1) hs.le
  · exact (div_le_one hs).2 (by linarith [hi.2])

theorem lowerEndpointPoint_mem_closed (raw : FifthWireRow)
    (c : ChildIndex) (i : Fin 5) (t : Point)
    (ht : t ∈ closedChildBox raw c) :
    lowerEndpointPoint raw c i t ∈ closedChildBox raw c := by
  intro k
  by_cases hk : k = i
  · subst k
    simp only [lowerEndpointPoint, Function.update_same]
    exact ⟨le_rfl, sub_nonneg.mp ((child_span_pos raw c i).le)⟩
  · simpa [lowerEndpointPoint, hk, Ne.symm hk] using ht k

theorem upperEndpointPoint_mem_closed (raw : FifthWireRow)
    (c : ChildIndex) (i : Fin 5) (t : Point)
    (ht : t ∈ closedChildBox raw c) :
    upperEndpointPoint raw c i t ∈ closedChildBox raw c := by
  intro k
  by_cases hk : k = i
  · subst k
    simp only [upperEndpointPoint, Function.update_same]
    exact ⟨sub_nonneg.mp ((child_span_pos raw c i).le), le_rfl⟩
  · simpa [upperEndpointPoint, hk, Ne.symm hk] using ht k

/-- The Phase9 coordinate chord extends to both closure endpoints. -/
theorem frozenGap_oneCoordinateChord_closed (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5)
    (t : Point) (ht : t ∈ closedChildBox raw c) :
    (1 - coordinateFraction raw c i t) *
        frozenGap picks raw (lowerEndpointPoint raw c i t) +
      coordinateFraction raw c i t *
        frozenGap picks raw (upperEndpointPoint raw c i t) ≤
          frozenGap picks raw t := by
  have hq := coordinateFraction_bounds_closed raw c i t ht
  have h := frozenGap_concave_pair picks raw
    (coordinateFraction raw c i t) hq.1 hq.2
    (lowerEndpointPoint raw c i t) (upperEndpointPoint raw c i t)
  rw [coordinate_mix_endpoints raw c i t] at h
  exact h

/-- Every recursive branch fixes one actual child coordinate at its left
or right closure endpoint; the full five-element list has 32 leaves. -/
def weightedVertexTree (picks : ParentPicks) (raw : FifthWireRow)
    (c : ChildIndex) : List (Fin 5) → Point → ℝ
  | [], t => frozenGap picks raw t
  | i :: rest, t =>
      (1 - coordinateFraction raw c i t) *
          weightedVertexTree picks raw c rest (lowerEndpointPoint raw c i t) +
        coordinateFraction raw c i t *
          weightedVertexTree picks raw c rest (upperEndpointPoint raw c i t)

theorem weightedVertexTree_le_gap (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) (coords : List (Fin 5))
    (t : Point) (ht : t ∈ closedChildBox raw c) :
    weightedVertexTree picks raw c coords t ≤ frozenGap picks raw t := by
  induction coords generalizing t with
  | nil => rfl
  | cons i rest ih =>
      have hq := coordinateFraction_bounds_closed raw c i t ht
      have hl := ih (lowerEndpointPoint raw c i t)
        (lowerEndpointPoint_mem_closed raw c i t ht)
      have hu := ih (upperEndpointPoint raw c i t)
        (upperEndpointPoint_mem_closed raw c i t ht)
      have hweight :
          (1 - coordinateFraction raw c i t) *
              weightedVertexTree picks raw c rest (lowerEndpointPoint raw c i t) +
            coordinateFraction raw c i t *
              weightedVertexTree picks raw c rest (upperEndpointPoint raw c i t) ≤
          (1 - coordinateFraction raw c i t) *
              frozenGap picks raw (lowerEndpointPoint raw c i t) +
            coordinateFraction raw c i t *
              frozenGap picks raw (upperEndpointPoint raw c i t) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hq.2))
          (mul_le_mul_of_nonneg_left hu hq.1)
      exact hweight.trans (frozenGap_oneCoordinateChord_closed picks raw c i t ht)

def allFiveCoordinates : List (Fin 5) := [0, 1, 2, 3, 4]

theorem allFiveCoordinates_nodup : allFiveCoordinates.Nodup := by decide
theorem allFiveCoordinates_length : allFiveCoordinates.length = 5 := rfl

/-- The exact 32 closure vertices and their product barycentric weights.
The `true` branch uses the right closure endpoint. -/
abbrev VertexChoice := Fin 5 → Bool

def vertexPoint (raw : FifthWireRow) (c : ChildIndex)
    (ε : VertexChoice) : Point :=
  fun i => if ε i then childRight raw c i else childLeft raw c i

def vertexWeight (raw : FifthWireRow) (c : ChildIndex)
    (ε : VertexChoice) (t : Point) : ℝ :=
  ∏ i : Fin 5,
    if ε i then coordinateFraction raw c i t
    else 1 - coordinateFraction raw c i t

theorem vertexChoice_card : Fintype.card VertexChoice = 32 := by decide

theorem vertexPoint_mem_closed (raw : FifthWireRow) (c : ChildIndex)
    (ε : VertexChoice) : vertexPoint raw c ε ∈ closedChildBox raw c := by
  intro i
  by_cases hi : ε i
  · simp only [vertexPoint, hi, ite_true]
    exact ⟨sub_nonneg.mp ((child_span_pos raw c i).le), le_rfl⟩
  · simp only [vertexPoint, hi, ite_false]
    exact ⟨le_rfl, sub_nonneg.mp ((child_span_pos raw c i).le)⟩

theorem vertexWeight_nonneg (raw : FifthWireRow) (c : ChildIndex)
    (ε : VertexChoice) (t : Point) (ht : t ∈ closedChildBox raw c) :
    0 ≤ vertexWeight raw c ε t := by
  unfold vertexWeight
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : ε i
  · simpa [hi] using (coordinateFraction_bounds_closed raw c i t ht).1
  · simpa [hi] using sub_nonneg.mpr
      (coordinateFraction_bounds_closed raw c i t ht).2

theorem fiveCoordinateTree_le_gap (picks : ParentPicks)
    (raw : FifthWireRow) (c : ChildIndex) (t : Point)
    (ht : t ∈ childBox raw c) :
    weightedVertexTree picks raw c allFiveCoordinates t ≤
      frozenGap picks raw t :=
  weightedVertexTree_le_gap picks raw c allFiveCoordinates t
    (childBox_subset_closed raw c ht)

end
end ImbalancedChen.P5OldFifthFiveCoordinateTree
