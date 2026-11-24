import ImbalancedChen.P5OriginalEighthRecoveredAffinePatterns
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal remaining 33 old first-six affine plane patterns from the verified
release navigation records. The first-failure navigation JSON has SHA-256
362b4986e7f7fd45f0a881fe2907b4f6581824f32d720e44d763ab0b95c1166d.
Its H1 group is empty; H3/H5/H7 have 12/7/10 strict cells in recorded
cell_id order. The winner50 producers define bit 0 as A (line 32 in
both navigation.py files). The pilot's bit 0 set also equals ascending
seed cell07's explicit left_masks.

This is a physical row map, not an affine feasibility certificate or a
common causal third/sixth ancestor certificate. No producer, integrator,
linear program, or numerical verifier was run here.
-/

namespace ImbalancedChen.P5OriginalEighthNavigationMap

noncomputable section
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalEighthAffineRowRecipe
open P5OriginalEighthRecoveredAffinePatterns

def ascendingSeedLeftCodes : Finset ℕ := {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 50, 52, 56}
def winner9SeedLeftCodes : Finset ℕ := {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 56}
def winner50ALeftCodes : Finset ℕ := {1, 2, 4, 6, 8, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 50, 52, 56}
def winner50DLeftCodes : Finset ℕ := {1, 2, 4, 6, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56}

def firstFailureH3LeftCodes : Fin 12 → Finset ℕ := ![
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 49, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56, 60},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56, 60},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 49, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 49, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 56}
]

def firstFailureH5LeftCodes : Fin 7 → Finset ℕ := ![
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 56}
]

def firstFailureH7LeftCodes : Fin 10 → Finset ℕ := ![
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56, 60},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56, 60},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 49, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 50, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 52, 56},
  {1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 56}
]

/-- Exactly the four seed/winner50 slots and the 29 first-failure slots
newly supplied by the navigation records, in the published global order. -/
def navigationOldPlanes (i : Cell) : Option (Finset ℕ) :=
  if i.val = 7 then some ascendingSeedLeftCodes
  else if i.val = 41 then some winner9SeedLeftCodes
  else if i.val = 43 then some winner50ALeftCodes
  else if i.val = 44 then some winner50DLeftCodes
  else if h : 58 ≤ i.val ∧ i.val < 70 then
    some (firstFailureH3LeftCodes ⟨i.val - 58, by omega⟩)
  else if h : 70 ≤ i.val ∧ i.val < 77 then
    some (firstFailureH5LeftCodes ⟨i.val - 70, by omega⟩)
  else if h : 77 ≤ i.val then
    some (firstFailureH7LeftCodes ⟨i.val - 77, by omega⟩)
  else none

/-- Phase6's 54 literal patterns and the 33 navigation patterns are
combined without assigning a default pattern to an absent source. -/
def adoptedOldPlanes (i : Cell) : Option (Finset ℕ) :=
  navigationOldPlanes i <|> recoveredOldPlanes i

theorem navigation_pattern_count :
    (Finset.univ.filter (fun i : Cell => (navigationOldPlanes i).isSome)).card = 33 := by
  decide

theorem adopted_old_planes_all (i : Cell) : (adoptedOldPlanes i).isSome := by
  fin_cases i <;> decide

/-- The literal old-plane, complete-square and selected-complement-square
rows for each published physical cell. Row satisfaction and positive
volume require separate exact affine certificates. -/
def adoptedPhysicalSquareAndPlaneRows (i : Cell) (t : Point) : Prop :=
  match adoptedOldPlanes i with
  | none => False
  | some leftCodes =>
      oldPlaneRows i leftCodes t ∧ fullSquareRows i t ∧
        selectedComplementRows i t

end
end ImbalancedChen.P5OriginalEighthNavigationMap
