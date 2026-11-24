import ImbalancedChen.P5OriginalEighthAffineRowRecipe
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal selected eighth old-plane assignments recovered from the public
release, matched by the evidence locator to the pinned source manifest.
The old adopted ascending cell 07 and winner9 cell 11 are seed
duplicates, not missing new domains. Their pattern records are not
included in this extract. The first-failure cell/witness summaries
also omit the navigation old-plane assignments. No numerical replay,
physical row satisfaction, ancestor selection, or density is claimed.
-/

namespace ImbalancedChen.P5OriginalEighthRecoveredAffinePatterns

noncomputable section
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalEighthAffineRowRecipe

def ascendingLeftCodes : Fin 15 → Option (Finset ℕ) := ![
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 58, 60} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 60} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 60} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 50, 52, 56, 60} : Finset ℕ),
  none,
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56, 60} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 44, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 44, 48, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 56} : Finset ℕ)
]

def winner9LeftCodes : Fin 13 → Option (Finset ℕ) := ![
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 49, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56, 60} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56, 60} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 49, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 49, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 50, 52, 56} : Finset ℕ),
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 52, 56} : Finset ℕ),
  none,
  some ({1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48} : Finset ℕ)
]

def thirdMinorantLeftCodes : Fin 13 → Finset ℕ := ![
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 49, 50, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56, 60},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56, 60},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 49, 50, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 49, 50, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 50, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 44, 48, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 50, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 52, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48, 56},
  {1, 2, 4, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48}
]

/-! The global indices follow the published 30 + 13 + 1 + 1 + 13
  + 12 + 7 + 10 partition. The two seed slots and both winner50 slots
  stay empty until their literal pattern records are bound. -/
def recoveredOldPlanes (i : Cell) : Option (Finset ℕ) :=
  if h0 : i.val < 15 then
    ascendingLeftCodes ⟨i.val, h0⟩
  else if h1 : i.val < 30 then
    compactPackageOldPlanes i
  else if h2 : i.val < 43 then
    winner9LeftCodes ⟨i.val - 30, by omega⟩
  else if h3 : i.val < 45 then
    none
  else if h4 : i.val < 58 then
    some (thirdMinorantLeftCodes ⟨i.val - 45, by omega⟩)
  else none

theorem ascending_seed_held :
    recoveredOldPlanes (⟨7, by omega⟩ : Cell) = none := by decide

theorem winner9_seed_held :
    recoveredOldPlanes (⟨41, by omega⟩ : Cell) = none := by decide

theorem recovered_old_plane_count :
    (Finset.univ.filter (fun i : Cell => (recoveredOldPlanes i).isSome)).card = 54 := by
  decide

def recoveredPhysicalSquareAndPlaneRows (i : Cell) (t : Point) : Prop :=
  match recoveredOldPlanes i with
  | none => False
  | some leftCodes =>
      oldPlaneRows i leftCodes t ∧
      fullSquareRows i t ∧ selectedComplementRows i t

theorem ascending_new_count :
    (Finset.univ.filter (fun j : Fin 15 => (ascendingLeftCodes j).isSome)).card = 14 := by
  decide

theorem winner9_new_count :
    (Finset.univ.filter (fun j : Fin 13 => (winner9LeftCodes j).isSome)).card = 12 := by
  decide

theorem recovered_pattern_count : 14 + 15 + 12 + 13 = 54 := by
  omega

theorem held_pattern_count : 87 - 54 = 33 := by
  omega

end
end ImbalancedChen.P5OriginalEighthRecoveredAffinePatterns
