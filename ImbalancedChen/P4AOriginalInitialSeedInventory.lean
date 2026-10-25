import ImbalancedChen.P4AClosedTreeCoordinatePropagation
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original `certify_extended_prefix.py` initial_cells generator, with
its original h-doubling and x-outer/y-inner order. This file binds all
21 first-generation integer rectangles to a Fin-indexed table and proves
the actual closed compact-domain overlap classification. It does not
assign a cost to any overlapping root or replay a later subdivision.
-/

namespace ImbalancedChen.P4AOriginalInitialSeedInventorySourceOnly

noncomputable section
open Set
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly

def H : ℤ := 8053063680
def M : ℤ := 157286400000
def R : ℤ := 159383552000
abbrev SeedCell := (Fin 3 → ℤ) × (Fin 3 → ℤ)

def axisPairs (z0 : ℤ) : List (ℤ × ℤ) :=
  if z0 < M then [(z0,M),(M,R)] else [(z0,R)]

def seedStrip (z0 z1 : ℤ) : List SeedCell :=
  (axisPairs z0).flatMap fun x =>
    (axisPairs z0).map fun y =>
      (![x.1,y.1,z0], ![x.2,y.2,z1])

/-- Direct transcription of `initial_cells` after the exact cut list is
resolved: h, 2h, 4h, 8h, 16h, mu, rho. -/
def initialSeeds : List SeedCell :=
  seedStrip H (2*H) ++ seedStrip (2*H) (4*H) ++
  seedStrip (4*H) (8*H) ++ seedStrip (8*H) (16*H) ++
  seedStrip (16*H) M ++ seedStrip M R

/-- Explicit producer-order records. Index 4k+r uses the kth doubling
strip and x-outer/y-inner rectangle r; index 20 is the last strip. -/
def records : List SeedCell :=
  [(![H,H,H], ![M,M,2*H]),
   (![H,M,H], ![M,R,2*H]),
   (![M,H,H], ![R,M,2*H]),
   (![M,M,H], ![R,R,2*H]),
   (![2*H,2*H,2*H], ![M,M,4*H]),
   (![2*H,M,2*H], ![M,R,4*H]),
   (![M,2*H,2*H], ![R,M,4*H]),
   (![M,M,2*H], ![R,R,4*H]),
   (![4*H,4*H,4*H], ![M,M,8*H]),
   (![4*H,M,4*H], ![M,R,8*H]),
   (![M,4*H,4*H], ![R,M,8*H]),
   (![M,M,4*H], ![R,R,8*H]),
   (![8*H,8*H,8*H], ![M,M,16*H]),
   (![8*H,M,8*H], ![M,R,16*H]),
   (![M,8*H,8*H], ![R,M,16*H]),
   (![M,M,8*H], ![R,R,16*H]),
   (![16*H,16*H,16*H], ![M,M,M]),
   (![16*H,M,16*H], ![M,R,M]),
   (![M,16*H,16*H], ![R,M,M]),
   (![M,M,16*H], ![R,R,M]),
   (![M,M,M], ![R,R,R])]

theorem records_length : records.length = 21 := by rfl

/-- Full source-order equality, stronger than any selected suffix claim. -/
theorem initialSeeds_eq_records : initialSeeds = records := by
  norm_num [initialSeeds,records,seedStrip,axisPairs,H,M,R]

def recordAt (i : Fin 21) : SeedCell :=
  records[i.1]'(by rw [records_length]; exact i.isLt)

/-- Fin-indexed inventory lookup into the original reconstructed list. -/
theorem initialSeeds_index (i : Fin 21) :
    initialSeeds[i.1]'(by rw [initialSeeds_eq_records,records_length]; exact i.isLt) =
      recordAt i := by
  rw [initialSeeds_eq_records]
  rfl

/-- The source's three distinguished integer cuts are exactly its stated
physical h, mu and rho at the original denominator. -/
theorem source_cut_coordinates :
    (H:ℝ)/coordinateDenominator = 1/100 ∧
    (M:ℝ)/coordinateDenominator = 25/128 ∧
    (R:ℝ)/coordinateDenominator = 19/96 := by
  norm_num [H,M,R,coordinateDenominator]

/-- Exact physical coordinate formula for every indexed integer record. -/
theorem recordAt_coordinates (i : Fin 21) (j : Fin 3) :
    (decodeCoordinates (recordAt i).1) j =
        ((recordAt i).1 j : ℝ) / 805306368000 ∧
    (decodeCoordinates (recordAt i).2) j =
        ((recordAt i).2 j : ℝ) / 805306368000 := by
  constructor <;> norm_num [decodeCoordinates,coordinateDenominator]

def rootCell (c : SeedCell) : Set Point :=
  compactRegion ∩ Icc (decodeCoordinates c.1) (decodeCoordinates c.2)

/-- The natural closed-domain witness chooses x=max(x0,y0), y=y0,
z=z0. For all records except the low/high fourth-strip crossing,
the strict old-cube inequality holds at this point. -/
def witness (c : SeedCell) : Point :=
  ![max ((decodeCoordinates c.1) 0) ((decodeCoordinates c.1) 1),
    (decodeCoordinates c.1) 1,(decodeCoordinates c.1) 2]

private theorem witness_mem_of_geometry (c : SeedCell)
    (horder : 0 < (witness c) 2 ∧ (witness c) 2 ≤ thirdPrefixRho ∧
      (witness c) 2 ≤ (witness c) 1 ∧
      (witness c) 1 ≤ (witness c) 0 ∧
      (witness c) 0 ≤ thirdPrefixRho)
    (hcube : (witness c) 0 + (witness c) 1 + 3*(witness c) 2 ≤
      thirdPrefixTheta)
    (hcutoff : (1/100:ℝ) ≤ (witness c) 2)
    (hlo : ∀ j, (decodeCoordinates c.1) j ≤ (witness c) j)
    (hhi : ∀ j, (witness c) j ≤ (decodeCoordinates c.2) j) :
    witness c ∈ rootCell c := by
  exact ⟨⟨⟨horder,by simpa only [sub_zero,mul_zero] using hcube⟩,hcutoff⟩,
    ⟨hlo,hhi⟩⟩

/-- Exactly indices 0..12 and 14 have a point in their closed actual
compact-domain intersection. No charge or positivity of the integral is
inferred from this geometric nonemptiness. -/
theorem roots0_to14_overlap (i : Fin 21)
    (hi : i.1 ≤ 12 ∨ i.1 = 14) : (rootCell (recordAt i)).Nonempty := by
  refine ⟨witness (recordAt i), ?_⟩
  apply witness_mem_of_geometry
  all_goals
    try (intro j; fin_cases j)
    fin_cases i <;>
      norm_num [witness,recordAt,records,decodeCoordinates,
        coordinateDenominator,thirdPrefixTheta,thirdPrefixRho,H,M,R] at hi ⊢

/-- Root 13 has only x≤mu≤y, whereas the ordered domain requires y≤x.
The forced equality x=y=mu violates the old-cube test already at z=8h. -/
theorem root13_empty : rootCell (recordAt ⟨13,by omega⟩) = ∅ := by
  ext t
  constructor
  · intro ht
    have hcube : t 0 + t 1 + 3*t 2 ≤ thirdPrefixTheta := by
      simpa only [sub_zero,mul_zero] using ht.1.1.2
    have horder : t 1 ≤ t 0 := ht.1.1.1.2.2.2.1
    have hx : t 0 ≤ (M:ℝ)/coordinateDenominator := by
      simpa [rootCell,recordAt,records,decodeCoordinates] using ht.2.2 0
    have hy : (M:ℝ)/coordinateDenominator ≤ t 1 := by
      simpa [rootCell,recordAt,records,decodeCoordinates] using ht.2.1 1
    have hz : (8*H:ℝ)/coordinateDenominator ≤ t 2 := by
      simpa [rootCell,recordAt,records,decodeCoordinates] using ht.2.1 2
    norm_num [thirdPrefixTheta,coordinateDenominator,H,M] at hx hy hz hcube
    linarith
  · intro ht
    simp at ht

/-- The complete geometric classification of the first fifteen roots.
Root 13 is empty; the other fourteen have the explicit witness above. -/
theorem initial15_overlap_iff (i : Fin 21) (hi : i.1 < 15) :
    (rootCell (recordAt i)).Nonempty ↔ i.1 ≠ 13 := by
  constructor
  · intro hn h13
    have heq : i = ⟨13,by omega⟩ := Fin.ext h13
    subst i
    rcases hn with ⟨t,ht⟩
    simp [root13_empty] at ht
  · intro h13
    apply roots0_to14_overlap i
    omega

end
end ImbalancedChen.P4AOriginalInitialSeedInventorySourceOnly
