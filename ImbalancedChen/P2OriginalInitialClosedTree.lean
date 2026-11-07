import ImbalancedChen.P4AOriginalInitialSeedInventory
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original `certify_extended_prefix.py` fully specifies its initial mesh in
source: six z strips and the x-outer/y-inner mu cuts. This module constructs
that initial mesh as one actual ClosedCutTree and identifies its entire
ordered closed-leaf list with the 21 original seed cells. Raising the x/y
lower endpoints from h to the strip's z0 is justified by the actual ordered
domain, rather than by silently changing a closed child.

This is only the original INITIAL tree. Neither the later adaptive split
history, its saved charges, nor the compact numerical allowance is asserted.
No numerical producer or certificate replay is used.
-/

namespace ImbalancedChen.P2OriginalInitialClosedTreeSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly

/-- The original x-outer, y-inner enumeration at a fixed z strip. -/
def xyTree : ClosedCutTree :=
  .split 0 M (.split 1 M .leaf .leaf) (.split 1 M .leaf .leaf)

/-- The actual source cut list h,2h,4h,8h,16h,mu,rho. The last strip
has no extra x/y cut because its lower endpoint is already mu. -/
def initialTree : ClosedCutTree :=
  .split 2 (2*H) xyTree
    (.split 2 (4*H) xyTree
      (.split 2 (8*H) xyTree
        (.split 2 (16*H) xyTree (.split 2 M xyTree .leaf))))

def initialLower : Fin 3 → ℤ := ![H,H,H]
def initialUpper : Fin 3 → ℤ := ![R,R,R]

/-- A strip lower bound on z also bounds x and y on the ordered domain. -/
def orderedLower (a : Point) : Point :=
  ![max (a 0) (a 2), max (a 1) (a 2), a 2]

def orderedIntegerLower (a : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![max (a 0) (a 2), max (a 1) (a 2), a 2]

def normalizeRoot (c : SeedCell) : SeedCell :=
  (orderedIntegerLower c.1,c.2)

/-- Ordered clipping preserves the exact domain portion, including empty
cells and closed order faces. -/
theorem compact_box_orderedLower (a b : Point) :
    compactRegion ∩ Icc a b = compactRegion ∩ Icc (orderedLower a) b := by
  ext t
  constructor
  · rintro ⟨ht,ha,hb⟩
    have hzy : t 2 ≤ t 1 := ht.1.1.2.2.1
    have hyx : t 1 ≤ t 0 := ht.1.1.2.2.2.1
    refine ⟨ht,?_,hb⟩
    intro i
    fin_cases i
    · exact max_le (ha 0) ((ha 2).trans (hzy.trans hyx))
    · exact max_le (ha 1) ((ha 2).trans hzy)
    · exact ha 2
  · rintro ⟨ht,ha,hb⟩
    refine ⟨ht,?_,hb⟩
    intro i
    fin_cases i
    · exact (le_max_left (a 0) (a 2)).trans (ha 0)
    · exact (le_max_left (a 1) (a 2)).trans (ha 1)
    · exact ha 2

theorem decode_orderedIntegerLower (a : Fin 3 → ℤ) :
    decodeCoordinates (orderedIntegerLower a) = orderedLower (decodeCoordinates a) := by
  ext i
  fin_cases i <;>
    simp [orderedIntegerLower,orderedLower,decodeCoordinates,Int.cast_max,
      max_div_div_right original_coordinateDenominator_pos.le]

theorem compact_box_normalizeRoot (c : SeedCell) :
    compactRegion ∩ Icc (decodeCoordinates c.1) (decodeCoordinates c.2) =
      rootCell (normalizeRoot c) := by
  rw [compact_box_orderedLower,← decode_orderedIntegerLower]
  rfl

/-- This complete list computation is a source-level equality of the
literal initial cuts. It never evaluates a sieve, logarithm or saved cost. -/
theorem normalized_initial_boxes :
    (integerLeafBoxes initialTree initialLower initialUpper).map normalizeRoot =
      initialSeeds := by
  rw [initialSeeds_eq_records]
  norm_num [initialTree,xyTree,integerLeafBoxes,leftIntegerUpper,rightIntegerLower,
    initialLower,initialUpper,normalizeRoot,orderedIntegerLower,records,H,M,R,
    Function.update,funext_iff,Fin.forall_fin_succ]

theorem compactRegion_subset_initial_box :
    compactRegion ⊆ Icc (decodeCoordinates initialLower)
      (decodeCoordinates initialUpper) := by
  intro t ht
  have hzy : t 2 ≤ t 1 := ht.1.1.2.2.1
  have hyx : t 1 ≤ t 0 := ht.1.1.2.2.2.1
  have hxr : t 0 ≤ thirdPrefixRho := ht.1.1.2.2.2.2
  have hhz : (1/100:ℝ) ≤ t 2 := ht.2
  have hlo : decodeCoordinates initialLower = fun _ => (1/100:ℝ) := by
    ext i
    fin_cases i <;> norm_num [decodeCoordinates,initialLower,H,coordinateDenominator]
  have hhi : decodeCoordinates initialUpper = fun _ => thirdPrefixRho := by
    ext i
    fin_cases i <;> norm_num [decodeCoordinates,initialUpper,R,
      coordinateDenominator,thirdPrefixRho]
  rw [hlo,hhi]
  constructor
  · intro i
    fin_cases i
    · exact hhz.trans (hzy.trans hyx)
    · exact hhz.trans hzy
    · exact hhz
  · intro i
    fin_cases i
    · exact hxr
    · exact hyx.trans hxr
    · exact hzy.trans (hyx.trans hxr)

/-- Full positional identification, rather than just a cover or matching
cardinality. Empty source roots and shared closed faces are retained. -/
theorem closedLeaves_initialTree_eq_original_seedCells :
    closedLeaves initialTree compactRegion = initialSeeds.map rootCell := by
  have hroot : compactRegion = compactRegion ∩
      Icc (decodeCoordinates initialLower) (decodeCoordinates initialUpper) := by
    exact (inter_eq_left.mpr compactRegion_subset_initial_box).symm
  conv_lhs => rw [hroot]
  rw [compact_closedLeaves_eq_integer_boxes]
  calc
    (integerLeafBoxes initialTree initialLower initialUpper).map
        (fun c => compactRegion ∩ Icc (decodeCoordinates c.1) (decodeCoordinates c.2)) =
      ((integerLeafBoxes initialTree initialLower initialUpper).map normalizeRoot).map rootCell := by
        rw [List.map_map]
        apply List.map_congr_left
        intro c _
        exact compact_box_normalizeRoot c
    _ = initialSeeds.map rootCell := by rw [normalized_initial_boxes]

/-- The actual compact correction is the sum over ALL 21 original seed
portions. This is an exact initial-mesh identity, with no charge premise. -/
theorem originalCompactThirdCorrection_eq_original_seed_integrals :
    originalCompactThirdCorrection =
      ((initialSeeds.map rootCell).map (fun c => ∫ t in c, compactKernel t)).sum := by
  rw [originalCompactThirdCorrection_eq_sum_closedLeaves initialTree,
    closedLeaves_initialTree_eq_original_seedCells]

theorem closedLeaves_initialTree_length :
    (closedLeaves initialTree compactRegion).length = 21 := by
  rw [closedLeaves_initialTree_eq_original_seedCells,List.length_map,
    initialSeeds_eq_records,records_length]

end
end ImbalancedChen.P2OriginalInitialClosedTreeSourceOnly
