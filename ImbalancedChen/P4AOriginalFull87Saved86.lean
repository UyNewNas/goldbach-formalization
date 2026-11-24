import ImbalancedChen.P4AOriginalFull87SeedRefinements
import ImbalancedChen.P2OriginalSaving20FirstFailureIntegral

/-! All original eighth numerical records other than the single radial
whole-cell replacement. Its genuine integral stays in the comparison.
The final two increments change the already counted index 41. -/
namespace ImbalancedChen.P4AOriginalFull87Saved86
noncomputable section
open scoped BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87ArchivedIntegralRows (archived)
open P4AOriginalFull87SeedRefinements (seed refinedRecord refined_seed_le_integral)
open P2OriginalSaving18UnequalIntegral (Paid57 originatingCell original57_archived_cell_le_integral)
open P2OriginalSaving20FirstFailureIntegral (sourceCell original_archived_cell_le_source_integral)
open P2OriginalCertificateBudget (savingLower)
open P2OriginalSeedChronologicalMaxArithmetic (slot21 slot22)

def radial : Cell := .remaining .seed
def radialQ : ℚ := 74558208451675327462975/2^96
def base87 : ℚ := 3111307568597708509491143/2^96
def savedGain : ℚ := base87 + savingLower slot21 + savingLower slot22

theorem original_radial_record : archived radial = radialQ := by decide

/-- The first six original slots include three refined stage totals.
The last two are the complete seed's successive replacement increments. -/
theorem savedGain_eq_original_eight_slots :
    savedGain = ∑ j : Fin 8, savingLower ⟨14 + j.val,by omega⟩ := by decide

theorem original_refined_record_sum : (∑ c : Cell, refinedRecord c) = savedGain :=
  P4AOriginalFull87SeedRefinements.refined_record_sum

/-- These are the actual constructors of the 57 Jensen/log cells and
the 29 first-failure cells. Source index 7 is the only other constructor. -/
theorem original_86_owners : ∀ c : Cell,
    c = radial ∨ (∃ j : Paid57, originatingCell j = c) ∨ ∃ j : Fin 29, sourceCell j = c := by
  decide

theorem original86_archived_cell_le_integral (c : Cell) (hc : c ≠ radial) :
    (archived c : ℝ) ≤ cellIntegral c := by
  rcases original_86_owners c with h | ⟨j,rfl⟩ | ⟨j,rfl⟩
  · exact False.elim (hc h)
  · exact original57_archived_cell_le_integral j
  · exact original_archived_cell_le_source_integral j

theorem original86_refined_cell_le_integral (c : Cell) (hc : c ≠ radial) :
    (refinedRecord c : ℝ) ≤ cellIntegral c := by
  by_cases hs : c = seed
  · subst c
    exact refined_seed_le_integral
  · simpa [refinedRecord,hs] using original86_archived_cell_le_integral c hc

private theorem original_refined_without_radial :
    (∑ c : Cell, if c = radial then (0 : ℚ) else refinedRecord c) = savedGain - radialQ := by
  have hsep (c : Cell) : refinedRecord c =
      (if c = radial then (0 : ℚ) else refinedRecord c) + (if c = radial then radialQ else 0) := by
    by_cases h : c = radial
    · subst c
      simp [refinedRecord,show radial ≠ seed by decide,original_radial_record]
    · simp [h]
  have h := calc
    savedGain = ∑ c : Cell, refinedRecord c := original_refined_record_sum.symm
    _ = (∑ c : Cell, if c = radial then (0 : ℚ) else refinedRecord c) + radialQ := by
      calc
        _ = ∑ c : Cell, ((if c = radial then (0 : ℚ) else refinedRecord c) +
            (if c = radial then radialQ else 0)) := Finset.sum_congr rfl (fun c _ => hsep c)
        _ = _ := by simp [Finset.sum_add_distrib]
  linarith

/-- This keeps the radial integral with unit multiplicity while the
other 86 records, including the refined winner9 seed, are cashed. -/
theorem original86_refined_with_radial_integral :
    ((savedGain - radialQ : ℚ) : ℝ) + cellIntegral radial ≤ ∑ c : Cell, cellIntegral c := by
  have hp (c : Cell) :
      ((if c = radial then (0 : ℚ) else refinedRecord c : ℚ) : ℝ) +
        (if c = radial then cellIntegral radial else 0) ≤ cellIntegral c := by
    by_cases h : c = radial
    · subst c
      simp
    · simpa [h] using original86_refined_cell_le_integral c h
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hp c)
  have he : (∑ c : Cell, ((if c = radial then (0 : ℚ) else refinedRecord c : ℚ) : ℝ)) =
      ((savedGain - radialQ : ℚ) : ℝ) := by exact_mod_cast original_refined_without_radial
  simpa [Finset.sum_add_distrib,he] using hb

end
end ImbalancedChen.P4AOriginalFull87Saved86
