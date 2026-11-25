import ImbalancedChen.P4AOriginalFull87ArchivedValueDefinitions
import ImbalancedChen.P4AOriginalFull87CellIndexedArchiveWeight
import ImbalancedChen.P2Winner9CompleteSeedTerminal

/-! SOURCE ONLY / NOT COMPILED / NO FORMAL CREDIT.
Selected replacement for the original module of this same name. The seven
seed/ledger declarations below retain their original names and statements;
only original_seed_refined_floor consumes the current complete Winner9
terminal. The older geometry helpers remain in the frozen source archive.
Do not load that archived module as a second owner of these declarations.
The original Full87 definition-owner refactors must also be installed.
-/
namespace ImbalancedChen.P4AOriginalFull87SeedRefinements
noncomputable section
open scoped BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87ArchivedIntegralRows (archived)
open P2OriginalCertificateBudget (savingLower)
open P2OriginalSeedChronologicalMaxArithmetic (slot21 slot22)

def seed : Cell := .remaining (.nine 11)

theorem original_seed_log_selected :
    archived seed = P2Winner9CompleteSeedChronology.adoptedLogTotal := by
  rw [P2Winner9CompleteSeedChronology.full_literal_totals.1]
  rfl

/-- The same original seed bound, supplied by the complete current family. -/
theorem original_seed_refined_floor :
    (archived seed : ℝ) + (savingLower slot21 : ℝ) + (savingLower slot22 : ℝ) ≤ cellIntegral seed := by
  rw [original_seed_log_selected]
  exact P2Winner9CompleteSeedTerminal.complete_seed_ledger_le_original_full87_nine11

def refinedRecord (c : Cell) : ℚ :=
  archived c + if c = seed then savingLower slot21 + savingLower slot22 else 0

theorem refined_seed_le_integral : (refinedRecord seed : ℝ) ≤ cellIntegral seed := by
  simpa [refinedRecord,add_assoc] using original_seed_refined_floor

theorem original_increment_values :
    savingLower slot21 = (77410436074156865471 : ℚ)/2^96 ∧
    savingLower slot22 = (481322793305152847935 : ℚ)/2^96 := by
  rw [← P2OriginalSeedChronologicalMaxArithmetic.curvature_increment_exact,
    ← P2OriginalSeedChronologicalMaxArithmetic.mixed_increment_exact]
  norm_num [P2OriginalSeedChronologicalMaxArithmetic.curvatureIncrement,
    P2OriginalSeedChronologicalMaxArithmetic.curvatureSelectedTotal,
    P2OriginalSeedChronologicalMaxArithmetic.adoptedLogTotal,
    P2OriginalSeedChronologicalMaxArithmetic.mixedIncrement,
    P2OriginalSeedChronologicalMaxArithmetic.mixedSelectedTotal]

theorem refined_record_sum :
    (∑ c : Cell, refinedRecord c) =
      (3111307568597708509491143 : ℚ)/2^96 + savingLower slot21 + savingLower slot22 := by
  classical
  have h : (∑ c : Cell, archived c) = (3111307568597708509491143 : ℚ)/2^96 :=
    P4AOriginalFull87CellIndexedArchiveWeight.original_cell_archive_selected_sum_exact
  simp [refinedRecord,Finset.sum_add_distrib,h,add_assoc]

end
end ImbalancedChen.P4AOriginalFull87SeedRefinements
