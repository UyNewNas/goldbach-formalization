import ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation

/-!
SOURCE_WRITTEN / UNCOMPILED / MAIN OPEN30.

The exact coordinate dictionary for the original `ClosedCutTree`. The cut is
the original integer divided by the original coordinateDenominator. Closed
faces belong to both children. Endpoint updates use min/max, so the set
identities remain valid for cuts outside the box and for empty children.
No serialized historical tree, integral estimate, or target K is assumed.
-/
namespace ImbalancedChen.P4AClosedTreeCoordinatePropagationSourceOnly

noncomputable section
open Set OriginalThirdCompactPartitionSourceOnly

/-- Literal original left-child upper-coordinate update. -/
def leftUpper (b : Point) (axis : Fin 3) (cut : ℤ) : Point :=
  Function.update b axis (min (b axis) ((cut : ℝ) / coordinateDenominator))

/-- Literal original right-child lower-coordinate update. -/
def rightLower (a : Point) (axis : Fin 3) (cut : ℤ) : Point :=
  Function.update a axis (max (a axis) ((cut : ℝ) / coordinateDenominator))

theorem leftUpper_at_axis (b : Point) (axis : Fin 3) (cut : ℤ) :
    leftUpper b axis cut axis = min (b axis) ((cut : ℝ) / coordinateDenominator) := by
  simp [leftUpper]

theorem rightLower_at_axis (a : Point) (axis : Fin 3) (cut : ℤ) :
    rightLower a axis cut axis = max (a axis) ((cut : ℝ) / coordinateDenominator) := by
  simp [rightLower]

theorem leftUpper_other (b : Point) (axis i : Fin 3) (cut : ℤ) (hi : i ≠ axis) :
    leftUpper b axis cut i = b i := by
  simp [leftUpper, hi]

theorem rightLower_other (a : Point) (axis i : Fin 3) (cut : ℤ) (hi : i ≠ axis) :
    rightLower a axis cut i = a i := by
  simp [rightLower, hi]

/-- Exact left closed half-space intersection, including a cut below a_j. -/
theorem left_box_exact (a b : Point) (axis : Fin 3) (cut : ℤ) :
    Icc a b ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator} =
      Icc a (leftUpper b axis cut) := by
  ext t
  constructor
  · rintro ⟨⟨ha, hb⟩, hcut⟩
    refine ⟨ha, ?_⟩
    intro i
    by_cases hi : i = axis
    · subst i
      simpa only [leftUpper_at_axis] using le_min (hb axis) hcut
    · simpa only [leftUpper_other b axis i cut hi] using hb i
  · intro ht
    have hj : t axis ≤ min (b axis) ((cut : ℝ) / coordinateDenominator) := by
      simpa only [leftUpper_at_axis] using ht.2 axis
    refine ⟨⟨ht.1, ?_⟩, (le_min_iff.mp hj).2⟩
    intro i
    by_cases hi : i = axis
    · subst i
      exact (le_min_iff.mp hj).1
    · simpa only [leftUpper_other b axis i cut hi] using ht.2 i

/-- Exact right closed half-space intersection, including a cut above b_j. -/
theorem right_box_exact (a b : Point) (axis : Fin 3) (cut : ℤ) :
    Icc a b ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis} =
      Icc (rightLower a axis cut) b := by
  ext t
  constructor
  · rintro ⟨⟨ha, hb⟩, hcut⟩
    refine ⟨?_, hb⟩
    intro i
    by_cases hi : i = axis
    · subst i
      simpa only [rightLower_at_axis] using max_le (ha axis) hcut
    · simpa only [rightLower_other a axis i cut hi] using ha i
  · intro ht
    have hj : max (a axis) ((cut : ℝ) / coordinateDenominator) ≤ t axis := by
      simpa only [rightLower_at_axis] using ht.1 axis
    refine ⟨⟨?_, ht.2⟩, (max_le_iff.mp hj).2⟩
    intro i
    by_cases hi : i = axis
    · subst i
      exact (max_le_iff.mp hj).1
    · simpa only [rightLower_other a axis i cut hi] using ht.1 i

theorem left_domain_box_exact (domain : Set Point) (a b : Point)
    (axis : Fin 3) (cut : ℤ) :
    (domain ∩ Icc a b) ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator} =
      domain ∩ Icc a (leftUpper b axis cut) := by
  rw [inter_assoc, left_box_exact]

theorem right_domain_box_exact (domain : Set Point) (a b : Point)
    (axis : Fin 3) (cut : ℤ) :
    (domain ∩ Icc a b) ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis} =
      domain ∩ Icc (rightLower a axis cut) b := by
  rw [inter_assoc, right_box_exact]

/-- The endpoint-pair list follows the original tree, preserving leaf order,
repeated leaves, empty children, and both copies of every closed cut face. -/
def leafBoxes : ClosedCutTree → Point → Point → List (Point × Point)
  | .leaf, a, b => [(a, b)]
  | .split axis cut left right, a, b =>
      leafBoxes left a (leftUpper b axis cut) ++
        leafBoxes right (rightLower a axis cut) b

/-- Proved equality with the actual source leaf list, not a covering premise.
The arbitrary fixed domain can be the actual compactRegion or a coarse-cell
ordered portion. No rectangular approximation of that domain is introduced. -/
theorem closedLeaves_eq_map_leafBoxes (tree : ClosedCutTree) (domain : Set Point)
    (a b : Point) :
    closedLeaves tree (domain ∩ Icc a b) =
      (leafBoxes tree a b).map (fun bounds => domain ∩ Icc bounds.1 bounds.2) := by
  induction tree generalizing a b with
  | leaf => simp [closedLeaves, leafBoxes]
  | split axis cut left right ihL ihR =>
      change closedLeaves left
        ((domain ∩ Icc a b) ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}) ++
        closedLeaves right
        ((domain ∩ Icc a b) ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis}) =
        (leafBoxes left a (leftUpper b axis cut) ++
          leafBoxes right (rightLower a axis cut) b).map
            (fun bounds => domain ∩ Icc bounds.1 bounds.2)
      rw [List.map_append, left_domain_box_exact, right_domain_box_exact, ihL, ihR]

/-- The requested actual compact-region dictionary is an exact list equality,
so saved leaf indices can use it without forgetting original traversal order. -/
theorem compact_closedLeaves_eq_map_leafBoxes (tree : ClosedCutTree) (a b : Point) :
    closedLeaves tree (compactRegion ∩ Icc a b) =
      (leafBoxes tree a b).map (fun bounds => compactRegion ∩ Icc bounds.1 bounds.2) := by
  exact closedLeaves_eq_map_leafBoxes tree compactRegion a b

theorem mem_compact_closedLeaves_iff (tree : ClosedCutTree) (a b : Point)
    (leaf : Set Point) :
    leaf ∈ closedLeaves tree (compactRegion ∩ Icc a b) ↔
      ∃ bounds ∈ leafBoxes tree a b,
        leaf = compactRegion ∩ Icc bounds.1 bounds.2 := by
  rw [compact_closedLeaves_eq_map_leafBoxes]
  constructor
  · intro h
    obtain ⟨bounds, hbounds, heq⟩ := List.mem_map.mp h
    exact ⟨bounds, hbounds, heq.symm⟩
  · rintro ⟨bounds, hbounds, heq⟩
    exact List.mem_map.mpr ⟨bounds, hbounds, heq.symm⟩

/-- Decoding uses precisely the original physical coordinate denominator. -/
def decodeCoordinates (v : Fin 3 → ℤ) : Point :=
  fun i => (v i : ℝ) / coordinateDenominator

def leftIntegerUpper (b : Fin 3 → ℤ) (axis : Fin 3) (cut : ℤ) : Fin 3 → ℤ :=
  Function.update b axis (min (b axis) cut)

def rightIntegerLower (a : Fin 3 → ℤ) (axis : Fin 3) (cut : ℤ) : Fin 3 → ℤ :=
  Function.update a axis (max (a axis) cut)

theorem original_coordinateDenominator_pos : 0 < coordinateDenominator := by
  norm_num [coordinateDenominator]

/-- Integer min at the original cut commutes exactly with physical decoding. -/
theorem decode_leftIntegerUpper (b : Fin 3 → ℤ) (axis : Fin 3) (cut : ℤ) :
    decodeCoordinates (leftIntegerUpper b axis cut) =
      leftUpper (decodeCoordinates b) axis cut := by
  ext i
  by_cases hi : i = axis
  · subst i
    simp only [decodeCoordinates, leftIntegerUpper, leftUpper, Function.update_same]
    by_cases hb : b axis ≤ cut
    · have hbr : (b axis : ℝ) ≤ (cut : ℝ) := by exact_mod_cast hb
      rw [min_eq_left hb, min_eq_left
        (div_le_div_of_nonneg_right hbr original_coordinateDenominator_pos.le)]
    · have hb' : cut ≤ b axis := le_of_not_ge hb
      have hbr : (cut : ℝ) ≤ (b axis : ℝ) := by exact_mod_cast hb'
      rw [min_eq_right hb', min_eq_right
        (div_le_div_of_nonneg_right hbr original_coordinateDenominator_pos.le)]
  · simp [decodeCoordinates, leftIntegerUpper, leftUpper, hi]

/-- Integer max at the original cut commutes exactly with physical decoding. -/
theorem decode_rightIntegerLower (a : Fin 3 → ℤ) (axis : Fin 3) (cut : ℤ) :
    decodeCoordinates (rightIntegerLower a axis cut) =
      rightLower (decodeCoordinates a) axis cut := by
  ext i
  by_cases hi : i = axis
  · subst i
    simp only [decodeCoordinates, rightIntegerLower, rightLower, Function.update_same]
    by_cases ha : a axis ≤ cut
    · have har : (a axis : ℝ) ≤ (cut : ℝ) := by exact_mod_cast ha
      rw [max_eq_right ha, max_eq_right
        (div_le_div_of_nonneg_right har original_coordinateDenominator_pos.le)]
    · have ha' : cut ≤ a axis := le_of_not_ge ha
      have har : (cut : ℝ) ≤ (a axis : ℝ) := by exact_mod_cast ha'
      rw [max_eq_left ha', max_eq_left
        (div_le_div_of_nonneg_right har original_coordinateDenominator_pos.le)]
  · simp [decodeCoordinates, rightIntegerLower, rightLower, hi]

/-- The integer-coordinate counterpart keeps the exact same original tree. -/
def integerLeafBoxes : ClosedCutTree → (Fin 3 → ℤ) → (Fin 3 → ℤ) →
    List ((Fin 3 → ℤ) × (Fin 3 → ℤ))
  | .leaf, a, b => [(a, b)]
  | .split axis cut left right, a, b =>
      integerLeafBoxes left a (leftIntegerUpper b axis cut) ++
        integerLeafBoxes right (rightIntegerLower a axis cut) b

/-- Every recursive integer endpoint update decodes to the exact real update;
this list identity also preserves the original left-before-right ordering. -/
theorem leafBoxes_decode_eq (tree : ClosedCutTree) (a b : Fin 3 → ℤ) :
    leafBoxes tree (decodeCoordinates a) (decodeCoordinates b) =
      (integerLeafBoxes tree a b).map
        (fun bounds => (decodeCoordinates bounds.1, decodeCoordinates bounds.2)) := by
  induction tree generalizing a b with
  | leaf => simp [leafBoxes, integerLeafBoxes]
  | split axis cut left right ihL ihR =>
      change leafBoxes left (decodeCoordinates a) (leftUpper (decodeCoordinates b) axis cut) ++
        leafBoxes right (rightLower (decodeCoordinates a) axis cut) (decodeCoordinates b) =
        (integerLeafBoxes left a (leftIntegerUpper b axis cut) ++
          integerLeafBoxes right (rightIntegerLower a axis cut) b).map
            (fun bounds => (decodeCoordinates bounds.1, decodeCoordinates bounds.2))
      rw [← decode_leftIntegerUpper, ← decode_rightIntegerLower, ihL, ihR, List.map_append]

/-- Direct public dictionary for original integer-coordinate tree data.
No leaf-set equality is supplied as an input, even for degenerate leaves. -/
theorem compact_closedLeaves_eq_integer_boxes (tree : ClosedCutTree)
    (a b : Fin 3 → ℤ) :
    closedLeaves tree (compactRegion ∩ Icc (decodeCoordinates a) (decodeCoordinates b)) =
      (integerLeafBoxes tree a b).map (fun bounds =>
        compactRegion ∩ Icc (decodeCoordinates bounds.1) (decodeCoordinates bounds.2)) := by
  rw [compact_closedLeaves_eq_map_leafBoxes, leafBoxes_decode_eq, List.map_map]
  rfl

end
end ImbalancedChen.P4AClosedTreeCoordinatePropagationSourceOnly
