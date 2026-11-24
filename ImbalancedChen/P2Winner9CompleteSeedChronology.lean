import ImbalancedChen.P2Winner9CompleteSeedData
import ImbalancedChen.P2OriginalSeedChronologicalMaxArithmetic
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual full 11026-row source ownership and the two ledger-slot increments.
The source owners are the original simplex ordinals, not ledger slots21/22.
Closed finite field/total source proof terms are NOT EXECUTED. This is not
an all-row analytic enclosure or a proof of geometric disjointness/cover.
-/

namespace ImbalancedChen.P2Winner9CompleteSeedChronology

open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData

abbrev SourceOwner := RowIndex

def q96 : Nat := 79228162514264337593543950336

def owner (i : RowIndex) : Nat := (entry i).parentId

def adoptedLogTotal : ℚ := ((∑ i : RowIndex, (entry i).logSelected : Nat) : ℚ) / q96

def curvatureSelectedTotal : ℚ :=
  ((∑ i : RowIndex, (entry i).curvatureSelected : Nat) : ℚ) / q96

def mixedSelectedTotal : ℚ :=
  ((∑ i : RowIndex, (entry i).mixedSelected : Nat) : ℚ) / q96

def curvatureGain : ℚ := curvatureSelectedTotal - adoptedLogTotal

def mixedGain : ℚ := mixedSelectedTotal - curvatureSelectedTotal

/-- These finite checks bind every original retained row, including zero
or nonwinning alternates, to the original max chronology. NOT EXECUTED. -/
theorem all_actual_row_maxima : ∀ i : RowIndex,
    (entry i).logSelected ≤ (entry i).curvatureSelected ∧
      (entry i).curvatureSelected ≤ (entry i).mixedSelected ∧
      (entry i).curvatureSelected = max (entry i).logSelected (entry i).curvatureRaw ∧
      (entry i).mixedSelected = max (entry i).curvatureSelected (entry i).mixedRaw := by
  decide +kernel

theorem owner_is_original_ordinal (i : RowIndex) : owner i = i.val :=
  (full_source_shapes_and_chronology.2.2 i).1

/-- Each source stream ordinal is represented once. This is ordinal
ownership, not a claim that different physical simplex supports are disjoint. -/
theorem source_owner_injective : Function.Injective owner := by
  intro i j h
  rw [owner_is_original_ordinal, owner_is_original_ordinal] at h
  exact Fin.ext h

/-- The three exact totals are computed from ALL actual literal rows.
This closed proof is an unevaluated source proposal, not a numeric replay. -/
theorem full_literal_totals :
    adoptedLogTotal = P2OriginalSeedChronologicalMaxArithmetic.adoptedLogTotal ∧
      curvatureSelectedTotal = P2OriginalSeedChronologicalMaxArithmetic.curvatureSelectedTotal ∧
      mixedSelectedTotal = P2OriginalSeedChronologicalMaxArithmetic.mixedSelectedTotal := by
  decide +kernel

/-- Ledger slot21 is one complete-seed curvature replacement. It is not
simplex_id21 and it is not the unmaximized curvature sum. -/
theorem full_seed_slot21 :
    curvatureGain = P2OriginalCertificateBudget.savingLower
      P2OriginalSeedChronologicalMaxArithmetic.slot21 := by
  unfold curvatureGain
  rw [full_literal_totals.2.1, full_literal_totals.1]
  exact P2OriginalSeedChronologicalMaxArithmetic.curvature_increment_exact

/-- Ledger slot22 is one complete-seed mixed replacement of the already
adopted curvature maximum. It is not simplex_id22 or an extra Q0 sum. -/
theorem full_seed_slot22 :
    mixedGain = P2OriginalCertificateBudget.savingLower
      P2OriginalSeedChronologicalMaxArithmetic.slot22 := by
  unfold mixedGain
  rw [full_literal_totals.2.2, full_literal_totals.2.1]
  exact P2OriginalSeedChronologicalMaxArithmetic.mixed_increment_exact

/-- The true original owner row subtracts the adopted old value once. -/
theorem actual_row_telescope (i : RowIndex) :
    ((entry i).mixedSelected : ℤ) - (entry i).logSelected =
      (((entry i).curvatureSelected : ℤ) - (entry i).logSelected) +
        (((entry i).mixedSelected : ℤ) - (entry i).curvatureSelected) := by ring

/-- A complete actual-array telescope, followed by exact original slot
identification. No raw curvature or plain P10 diagnostic is added. -/
theorem full_seed_slot_telescope :
    mixedSelectedTotal - adoptedLogTotal =
      P2OriginalCertificateBudget.savingLower P2OriginalSeedChronologicalMaxArithmetic.slot21 +
      P2OriginalCertificateBudget.savingLower P2OriginalSeedChronologicalMaxArithmetic.slot22 := by
  rw [← full_seed_slot21, ← full_seed_slot22]
  unfold curvatureGain mixedGain
  ring

theorem actual_owner_stage_gains_nonneg (i : RowIndex) :
    (0 : ℤ) ≤ ((entry i).curvatureSelected : ℤ) - (entry i).logSelected ∧
      (0 : ℤ) ≤ ((entry i).mixedSelected : ℤ) - (entry i).curvatureSelected := by
  have h := all_actual_row_maxima i
  have h₁ : ((entry i).logSelected : ℤ) ≤ (entry i).curvatureSelected := by exact_mod_cast h.1
  have h₂ : ((entry i).curvatureSelected : ℤ) ≤ (entry i).mixedSelected := by exact_mod_cast h.2.1
  constructor <;> omega

end ImbalancedChen.P2Winner9CompleteSeedChronology
