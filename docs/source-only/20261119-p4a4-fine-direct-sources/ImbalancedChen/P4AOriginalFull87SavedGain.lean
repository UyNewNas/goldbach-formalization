import ImbalancedChen.P4AOriginalFull87Saved86
import ImbalancedChen.P2OriginalSaving15RadialIntegral

/-! All 87 original selected values on the respective physical source
integrals. The complete winner9 refinements enter only at index 41. -/
namespace ImbalancedChen.P4AOriginalFull87SavedGain
noncomputable section
open scoped BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87ArchivedIntegralRows (archived)
open P4AOriginalFull87SeedRefinements (seed refinedRecord)
open P4AOriginalFull87Saved86 (radial radialQ base87 savedGain)
open P2OriginalCertificateBudget (savingLower)

theorem original87_archived_cell_le_integral (c : Cell) :
    (archived c : ℝ) ≤ cellIntegral c := by
  by_cases h : c = radial
  · subst c
    exact P2OriginalSaving15RadialIntegral.original_radial_archived_cell_le_source_integral
  · exact P4AOriginalFull87Saved86.original86_archived_cell_le_integral c h

theorem original87_refined_cell_le_integral (c : Cell) :
    (refinedRecord c : ℝ) ≤ cellIntegral c := by
  by_cases h : c = radial
  · subst c
    simpa [refinedRecord,show radial ≠ seed by decide] using original87_archived_cell_le_integral radial
  · exact P4AOriginalFull87Saved86.original86_refined_cell_le_integral c h

/-- The original six selected stage totals on their 87 actual sources. -/
theorem original_base87_le_integral :
    (base87 : ℝ) ≤ ∑ c : Cell, cellIntegral c := by
  have hsum : (∑ c : Cell, (archived c : ℝ)) = (base87 : ℝ) := by
    exact_mod_cast P4AOriginalFull87CellIndexedArchiveWeight.original_cell_archive_selected_sum_exact
  rw [← hsum]
  exact Finset.sum_le_sum (fun c _ => original87_archived_cell_le_integral c)

/-- Six selected totals and the two successive winner9 replacements.
Every source is counted with multiplicity one. -/
theorem original_saved_gain_le_integral :
    (savedGain : ℝ) ≤ ∑ c : Cell, cellIntegral c := by
  have hsum : (∑ c : Cell, (refinedRecord c : ℝ)) = (savedGain : ℝ) := by
    exact_mod_cast P4AOriginalFull87Saved86.original_refined_record_sum
  rw [← hsum]
  exact Finset.sum_le_sum (fun c _ => original87_refined_cell_le_integral c)

theorem original_saved_gain_q96 :
    savedGain =
      (3111307568597708509491143 + 77410436074156865471 + 481322793305152847935 : ℚ)/2^96 := by
  rw [P4AOriginalFull87Saved86.savedGain,P4AOriginalFull87Saved86.base87,
    P4AOriginalFull87SeedRefinements.original_increment_values.1,
    P4AOriginalFull87SeedRefinements.original_increment_values.2]
  ring

theorem original_eight_slot_sum_le_integral :
    ((∑ j : Fin 8, savingLower ⟨14 + j.val,by omega⟩ : ℚ) : ℝ) ≤ ∑ c : Cell, cellIntegral c := by
  rw [← P4AOriginalFull87Saved86.savedGain_eq_original_eight_slots]
  exact original_saved_gain_le_integral

end
end ImbalancedChen.P4AOriginalFull87SavedGain
