import ImbalancedChen.P4AClosedTreeCoordinatePropagation
import ImbalancedChen.ClosedLeafStoredChargeAggregation
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The original `certify_extended_prefix.py` initial_cells generator begins at
h=1/100, doubles through 16h, inserts mu=25/128, and splits each x/y strip
at mu. The fifth strip's first root is zero-based root 16. Its three lower
coordinates are 16h=4/25, its three upper coordinates are mu. The original
enclosure returns `(0,0,'outside')` before any table query because
x0+y0+3z0 = 4/5 > Theta=299/500. The producer inserts a cell into its heap
only if `hi>lo`, so this zero root is never split. This module binds that
actual source root and its positional zero charge to one closed leaf.

There is no claim about the other 20 initial roots, their descendants, or
the final saved compact integer sum.
-/

namespace ImbalancedChen.P4AOriginalSeed16OutsideLeafSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly

def H : ℤ := 8053063680
def M : ℤ := 157286400000
def R : ℤ := 159383552000

abbrev SeedCell := (Fin 3 → ℤ) × (Fin 3 → ℤ)

/-- The original producer's `axis_cuts` pair list for a fixed z-strip. -/
def axisPairs (z0 : ℤ) : List (ℤ × ℤ) :=
  if z0 < M then [(z0,M),(M,R)] else [(z0,R)]

/-- Same x-outer, y-inner enumeration and coordinate order as `initial_cells`. -/
def seedStrip (z0 z1 : ℤ) : List SeedCell :=
  (axisPairs z0).flatMap fun x =>
    (axisPairs z0).map fun y =>
      (![x.1,y.1,z0], ![x.2,y.2,z1])

/-- The exact six z-strips of the original source initial mesh. -/
def initialSeeds : List SeedCell :=
  seedStrip H (2*H) ++ seedStrip (2*H) (4*H) ++
  seedStrip (4*H) (8*H) ++ seedStrip (8*H) (16*H) ++
  seedStrip (16*H) M ++ seedStrip M R

def seed16Lo : Fin 3 → ℤ := ![16*H,16*H,16*H]
def seed16Hi : Fin 3 → ℤ := ![M,M,M]

/-- Zero-based root 16 is the first x/y rectangle in the fifth z-strip. -/
theorem initialSeeds_root16 : initialSeeds[16]? = some (seed16Lo,seed16Hi) := by
  norm_num [initialSeeds,seedStrip,axisPairs,seed16Lo,seed16Hi,H,M,R]

theorem seed16_coordinates :
    decodeCoordinates seed16Lo = ![(4:ℝ)/25,4/25,4/25] ∧
    decodeCoordinates seed16Hi = ![(25:ℝ)/128,25/128,25/128] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [decodeCoordinates,seed16Lo,seed16Hi,H,M,coordinateDenominator]

/-- This is the original producer's first outside test, with strict margin. -/
theorem seed16_oldCube_excluded :
    thirdPrefixTheta < (decodeCoordinates seed16Lo) 0 +
      (decodeCoordinates seed16Lo) 1 + 3*(decodeCoordinates seed16Lo) 2 := by
  norm_num [decodeCoordinates,seed16Lo,H,coordinateDenominator,thirdPrefixTheta]

def seed16Cell : Set Point :=
  compactRegion ∩ Icc (decodeCoordinates seed16Lo) (decodeCoordinates seed16Hi)

/-- The actual compact domain gives zero volume and zero kernel integral on
this root. No arbitrary enclosure or query value appears in the proof. -/
theorem seed16Cell_empty : seed16Cell = ∅ := by
  ext t
  constructor
  · intro ht
    have hcube : t 0 + t 1 + 3*t 2 ≤ thirdPrefixTheta := by
      simpa only [sub_zero, mul_zero] using ht.1.1.2
    have hx : (decodeCoordinates seed16Lo) 0 ≤ t 0 := ht.2.1 0
    have hy : (decodeCoordinates seed16Lo) 1 ≤ t 1 := ht.2.1 1
    have hz : (decodeCoordinates seed16Lo) 2 ≤ t 2 := ht.2.1 2
    have h := seed16_oldCube_excluded
    linarith
  · intro ht
    simp at ht

def seed16StoredEntry : ℝ × ℤ := (0,0)

/-- A genuine one-leaf positional list at original root 16. The stored
integer charge is exactly the producer's outside-branch zero; every local
integral premise is proved from the actual compact domain. -/
theorem seed16_positional_local_charge :
    List.Forall₂ (fun c entry =>
      (∫ t in c, compactKernel t) ≤ entry.1 ∧
        entry.1 ≤ (entry.2 : ℝ) / 2^80)
      (closedLeaves ClosedCutTree.leaf seed16Cell) [seed16StoredEntry] := by
  simp [closedLeaves,seed16StoredEntry,seed16Cell_empty]

theorem seed16_charge_sum :
    (([seed16StoredEntry].map Prod.snd).sum : ℤ) = 0 := by
  rfl

end
end ImbalancedChen.P4AOriginalSeed16OutsideLeafSourceOnly
