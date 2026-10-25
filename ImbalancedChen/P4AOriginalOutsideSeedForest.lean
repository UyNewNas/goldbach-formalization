import ImbalancedChen.P4AClosedTreeCoordinatePropagation
import ImbalancedChen.ClosedLeafStoredChargeAggregation
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Exact first-generation source records 15..20 from the original
`certify_extended_prefix.py` `initial_cells`, not the later independent
compact producer. These six records take the original `enclosure`'s
strict old-cube `outside` branch before any stored query. Each contributes
the exact `(lower,upper)=(0,0)` and fails the producer's `hi>lo` heap guard;
therefore none is subdivided. No positive-cost saved leaf or whole compact
bound is asserted here.
-/

namespace ImbalancedChen.P4AOriginalOutsideSeedForestSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly

def H : ℤ := 8053063680
def M : ℤ := 157286400000
def R : ℤ := 159383552000

abbrev SeedCell := (Fin 3 → ℤ) × (Fin 3 → ℤ)

/-- Literal x/y pair construction from `axis_cuts` in the original producer. -/
def axisPairs (z0 : ℤ) : List (ℤ × ℤ) :=
  if z0 < M then [(z0,M),(M,R)] else [(z0,R)]

def seedStrip (z0 z1 : ℤ) : List SeedCell :=
  (axisPairs z0).flatMap fun x =>
    (axisPairs z0).map fun y =>
      (![x.1,y.1,z0], ![x.2,y.2,z1])

/-- All six original z strips, in Python generator order. -/
def initialSeeds : List SeedCell :=
  seedStrip H (2*H) ++ seedStrip (2*H) (4*H) ++
  seedStrip (4*H) (8*H) ++ seedStrip (8*H) (16*H) ++
  seedStrip (16*H) M ++ seedStrip M R

def root15 : SeedCell := (![M,M,8*H], ![R,R,16*H])
def root16 : SeedCell := (![16*H,16*H,16*H], ![M,M,M])
def root17 : SeedCell := (![16*H,M,16*H], ![M,R,M])
def root18 : SeedCell := (![M,16*H,16*H], ![R,M,M])
def root19 : SeedCell := (![M,M,16*H], ![R,R,M])
def root20 : SeedCell := (![M,M,M], ![R,R,R])

def outsideSeedRecords : List SeedCell :=
  [root15,root16,root17,root18,root19,root20]

/-- The positional binding is to the producer's generator, not a selected
geometric list assembled after observing the desired result. -/
theorem initialSeeds_drop15 : initialSeeds.drop 15 = outsideSeedRecords := by
  norm_num [initialSeeds,seedStrip,axisPairs,outsideSeedRecords,
    root15,root16,root17,root18,root19,root20,H,M,R]

/-- Decoded physical endpoints, preserving the six-source-record order.
The integer records above are the primary frozen data. -/
theorem decoded_outside_roots :
    outsideSeedRecords.map (fun c =>
      (decodeCoordinates c.1,decodeCoordinates c.2)) =
      [(![(25:ℝ)/128,25/128,2/25], ![(19:ℝ)/96,19/96,4/25]),
       (![(4:ℝ)/25,4/25,4/25], ![(25:ℝ)/128,25/128,25/128]),
       (![(4:ℝ)/25,25/128,4/25], ![(25:ℝ)/128,19/96,25/128]),
       (![(25:ℝ)/128,4/25,4/25], ![(19:ℝ)/96,25/128,25/128]),
       (![(25:ℝ)/128,25/128,4/25], ![(19:ℝ)/96,19/96,25/128]),
       (![(25:ℝ)/128,25/128,25/128], ![(19:ℝ)/96,19/96,19/96])] := by
  simp only [outsideSeedRecords,List.map_cons,List.map_nil,
    List.cons.injEq,Prod.mk.injEq,and_true]
  repeat' constructor
  all_goals
    funext i
    fin_cases i <;>
      norm_num [root15,root16,root17,root18,root19,root20,
        decodeCoordinates,coordinateDenominator,H,M,R]

def rootCell (c : SeedCell) : Set Point :=
  compactRegion ∩ Icc (decodeCoordinates c.1) (decodeCoordinates c.2)

def oldCubeLower (c : SeedCell) : ℝ :=
  (decodeCoordinates c.1) 0 + (decodeCoordinates c.1) 1 +
    3*(decodeCoordinates c.1) 2

/-- The literal first outside test in `enclosure`: strict inequality. -/
theorem roots15_to20_outside :
    ∀ c ∈ outsideSeedRecords, thirdPrefixTheta < oldCubeLower c := by
  intro c hc
  simp only [outsideSeedRecords,List.mem_cons,List.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h
  all_goals subst c <;>
    norm_num [oldCubeLower,root15,root16,root17,root18,root19,root20,
      decodeCoordinates,coordinateDenominator,thirdPrefixTheta,H,M,R]

/-- Each original outside root has empty intersection with the actual
compact ordered domain, even with its closed boundary convention. -/
theorem rootCell_empty_of_oldCube {c : SeedCell}
    (hc : thirdPrefixTheta < oldCubeLower c) : rootCell c = ∅ := by
  ext t
  constructor
  · intro ht
    have hcube : t 0 + t 1 + 3*t 2 ≤ thirdPrefixTheta := by
      simpa only [sub_zero,mul_zero] using ht.1.1.2
    have hx : (decodeCoordinates c.1) 0 ≤ t 0 := ht.2.1 0
    have hy : (decodeCoordinates c.1) 1 ≤ t 1 := ht.2.1 1
    have hz : (decodeCoordinates c.1) 2 ≤ t 2 := ht.2.1 2
    unfold oldCubeLower at hc
    linarith
  · intro ht
    simp at ht

theorem roots15_to20_empty : ∀ c ∈ outsideSeedRecords, rootCell c = ∅ := by
  intro c hc
  exact rootCell_empty_of_oldCube (roots15_to20_outside c hc)

def zeroEntry : ℝ × ℤ := (0,0)
def outsideRootCells : List (Set Point) := outsideSeedRecords.map rootCell
def outsideRootEntries : List (ℝ × ℤ) := outsideSeedRecords.map (fun _ => zeroEntry)

/-- Six exact zero entries, positionally aligned with the six original
seed records. No leaf relation, integral bound, or cost equality is assumed. -/
theorem outsideRoots_positional_local_charge :
    List.Forall₂ (fun c entry =>
      (∫ t in c, compactKernel t) ≤ entry.1 ∧
        entry.1 ≤ (entry.2 : ℝ) / 2^80)
      outsideRootCells outsideRootEntries := by
  have h15 : rootCell root15 = ∅ := roots15_to20_empty root15 (by simp [outsideSeedRecords])
  have h16 : rootCell root16 = ∅ := roots15_to20_empty root16 (by simp [outsideSeedRecords])
  have h17 : rootCell root17 = ∅ := roots15_to20_empty root17 (by simp [outsideSeedRecords])
  have h18 : rootCell root18 = ∅ := roots15_to20_empty root18 (by simp [outsideSeedRecords])
  have h19 : rootCell root19 = ∅ := roots15_to20_empty root19 (by simp [outsideSeedRecords])
  have h20 : rootCell root20 = ∅ := roots15_to20_empty root20 (by simp [outsideSeedRecords])
  simp [outsideRootCells,outsideRootEntries,outsideSeedRecords,
    zeroEntry,h15,h16,h17,h18,h19,h20]

/-- The same positional assertion directly on the original seed suffix. -/
theorem initialSeedSuffix_positional_local_charge :
    List.Forall₂ (fun c entry =>
      (∫ t in c, compactKernel t) ≤ entry.1 ∧
        entry.1 ≤ (entry.2 : ℝ) / 2^80)
      ((initialSeeds.drop 15).map rootCell)
      ((initialSeeds.drop 15).map (fun _ => zeroEntry)) := by
  simp only [initialSeeds_drop15]
  exact outsideRoots_positional_local_charge

theorem outsideRoots_charge_sum :
    ((outsideRootEntries.map Prod.snd).sum : ℤ) = 0 := by
  rfl

end
end ImbalancedChen.P4AOriginalOutsideSeedForestSourceOnly
