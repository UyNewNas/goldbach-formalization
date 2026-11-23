-- PHASE9 literal adopted ascending mask129 patterns and chronological 42 eighth actions
-- SOURCE ONLY / UNCOMPILED / ready=false / zero credit.
-- Receipt SHA256 a2fcda891b80437ee179a8d27b22372b0ab3fc18bc43df68cf7fc1a417b95389.
-- Fourteen source cell JSON files, each immutable and individually hashed:
-- eighth-prefix-family-20261009-cell-00.json SHA256 fc05fae978c2f49a7d94a0b84335baace201120e5c1adb265dc49a495d2a4154
-- eighth-prefix-family-20261009-cell-01.json SHA256 9635adfba9d7a140849159de80a8ea174e3da3321a44041f26a70fad0811378c
-- eighth-prefix-family-20261009-cell-02.json SHA256 5520a264d435c4af8f8ff913dc7ddae7ea5374a07a92514ebda2a795d1d21ca6
-- eighth-prefix-family-20261009-cell-03.json SHA256 fc8818500699d821b15d531818e7ae30370ea5a7cf9fd4e5e439897718195a72
-- eighth-prefix-family-20261009-cell-04.json SHA256 6275b2444a3d579f4451091528c36d83ec33d116b50723a6241362deab205a4d
-- eighth-prefix-family-20261009-cell-05.json SHA256 acd062113d64689d830990485867e4aec18b3067613d01dc1c3289bf739c8dc4
-- eighth-prefix-family-20261009-cell-06.json SHA256 1ea79605405680709a2d147f27342c9aa9210e033200432ebeb8540b54238cb2
-- eighth-prefix-family-20261009-cell-08.json SHA256 359878be5ab4eb25c78fd31ad7bf50f2b6ea04892d5d5693f122d26665731fd3
-- eighth-prefix-family-20261009-cell-09.json SHA256 2d531e6c9c9cb1485f9f48cb3c4d2a19d2204665a854f80f3fc8d8a99e5666f5
-- eighth-prefix-family-20261009-cell-10.json SHA256 e96d1c9a229973ab0b15cb5ca589cc75c9a625aa7adc0614c2c29bc220a01be9
-- eighth-prefix-family-20261009-cell-11.json SHA256 b5499ace42ead23e89a1a2ce1478fd46d02911a4d8563f7fc70a5d25ebfbb365
-- eighth-prefix-family-20261009-cell-12.json SHA256 06dbd2f7035fe9958cab1f826dc4bb54fc06f0e4c0236aae205af1e30bd9c123
-- eighth-prefix-family-20261009-cell-13.json SHA256 c8f04859f87d13b22c127a1f29e7d38dd8c0a433d43628c6d9b5596d5d852677
-- eighth-prefix-family-20261009-cell-14.json SHA256 f3c60bdd6bd3dcbe742ff56b368e9a9d1ad7f95ae6f66c8d1181f43eca23e948

-- On each source cell, left_masks use A and right_masks use C.
-- The two lists are disjoint and cover 1..63 in every parsed source JSON.
-- Cell 7 is excluded: its already-adopted literal pattern is not supplied
-- by this verified 142-file extraction. This candidate does not claim
-- a complete 30 equal-parent literal selector.

import ImbalancedChen.P2OriginalAscendingEighthCapDictionary
import ImbalancedChen.OriginalDescendingFifteenCellOwnership
import ImbalancedChen.OriginalAscendingThirteenCellOwnership
import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger

namespace ImbalancedChen.P4AOriginalAscending14Literal42
noncomputable section
open scoped Classical
open ImbalancedChen.P2OriginalAscendingEighthCapDictionary

/-- Exact 14 source left-plane arrays; index 7 is deliberately empty. -/
def literalLeftMasks : Fin 15 → Finset ℕ :=
  ![
    {1,2,4,8,10,12,16,18,20,24,26,28,32,34,36,40,42,44,48,50,52,56,58,60},
    {1,2,4,8,10,12,16,18,20,24,26,28,32,34,36,40,42,44,48,50,52,56,60},
    {1,2,4,8,10,12,16,18,20,24,26,28,32,34,36,40,42,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,42,44,48,50,52,56,60},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,42,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,42,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,50,52,56,60},
    {},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,52,56,60},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,44,48,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,48,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,48,56}
  ]

def sixMask (I : Finset (Fin 6)) : ℕ := ∑ j ∈ I, 2 ^ j.val

/-- Source `chosenOldPlane` is A for left and C for its complement. -/
def literalPattern (i : Fin 15) (I : Finset (Fin 6)) : Bool :=
  decide (sixMask I ∉ literalLeftMasks i)

def ascending14Owns (t : Point) : Prop :=
  SelectedFamilyGuard literalPattern t

theorem literal_adopted_excluded {t : Point} (h : ascending14Owns t) :
    ∃ i : Fin 15, i ≠ 7 ∧ CellGuard (literalPattern i) t :=
  SelectedFamilyGuard.adopted_excluded h

/-- Original slot16 source action, now with no abstract pattern argument. -/
def literal16Exponent (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  familyNextExponent N lambda6 literalPattern pre

def literal16Policy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  familySourcePolicy N lambda6 literalPattern
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 base)

/-- Slot16 is followed by the established slot17 descending15 and slot19
ascending13 actions. Their source guards have opposite old/new winner sides,
so the later branch may retain the earlier level on its own complement. -/
def chronological42Exponent (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 8 pre
  if ∃ j : Fin 13, OriginalAscendingThirteenCellOwnership.StrictRows j t then
    OriginalAscendingThirteenCellOwnership.ownedRaisedExponent N lambda6 pre
  else if ∃ i : Fin 15, OriginalDescendingFifteenCellOwnership.StrictRows i t then
    OriginalDescendingFifteenCellOwnership.ownedRaisedExponent N lambda6 pre
  else literal16Exponent N lambda6 pre

def chronological42Policy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 base)
    (frozenParityRosserPolicy false 8
      (fun pre => N ^ chronological42Exponent N lambda6 pre))

/-- The new ascending129 cells cannot meet the original descending129
cells: their selected mask129 lies on opposite sides of the tent cusp. -/
theorem ascending14_disjoint_descending15 (t : Point)
    (ha : ascending14Owns t)
    (i : Fin 15) (hd : OriginalDescendingFifteenCellOwnership.StrictRows i t) :
    False := by
  obtain ⟨j, _hj, hj⟩ := ha
  have hsmall := (ascending_half_iff t).mp hj.new_ascending
  have hlarge := hd.descending
  dsimp [selectedSum,
    P2OriginalDescendingEighthLogSemantics.selectedSum] at hsmall hlarge
  linarith

/-- The ascending13 minorant cells are on the other side of the old
winner6 cusp from these fourteen equal-parent cells. -/
theorem ascending14_disjoint_ascending13 (t : Point)
    (ha : ascending14Owns t)
    (j : Fin 13) (hj : OriginalAscendingThirteenCellOwnership.StrictRows j t) :
    False := by
  obtain ⟨i, _hi, hi⟩ := ha
  have hlarge := hi.old_descending
  have hsmall := hj.ascendingThird
  dsimp [d] at hlarge
  linarith

theorem chronological42_on_ascending14 (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ)
    (ha : ascending14Owns (primeHistoryLogCoordinates N 8 pre)) :
    chronological42Exponent N lambda6 pre = literal16Exponent N lambda6 pre := by
  have hnot13 : ¬ ∃ j : Fin 13,
      OriginalAscendingThirteenCellOwnership.StrictRows j
        (primeHistoryLogCoordinates N 8 pre) := by
    rintro ⟨j, hj⟩
    exact ascending14_disjoint_ascending13 _ ha j hj
  have hnot15 : ¬ ∃ i : Fin 15,
      OriginalDescendingFifteenCellOwnership.StrictRows i
        (primeHistoryLogCoordinates N 8 pre) := by
    rintro ⟨i, hi⟩
    exact ascending14_disjoint_descending15 _ ha i hi
  simp [chronological42Exponent, hnot13, hnot15]

theorem chronological42_through_eight (N : ℝ) (lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (b : Bool) (pre : List ℕ)
    (h : pre.length ≤ 8) :
    chronological42Policy N lambda6 base b pre =
      P4AOriginalEighthParentPhysicalLedger.parentPolicy N lambda6 base b pre := by
  simp [chronological42Policy, firstExitDepthSplicePolicy, h]

end
end ImbalancedChen.P4AOriginalAscending14Literal42
