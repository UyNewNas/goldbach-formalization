import ImbalancedChen.P4AOriginalCompleteSixthAffinePrograms
import ImbalancedChen.P4AOriginalFull87CompleteSixthBound

/-! Four original nonsingleton witnesses. Their old parent comparison
is D(x+p), where p is coordinate five. Rows 4 and 49 in each literal
archive give the strict ordering of the three distinct caps. -/
namespace ImbalancedChen.P4AOriginalNonsingletonComparison
noncomputable section
open scoped Classical BigOperators
open P4AOriginalSixthLaterLiteral (Cell Point Affine rows stage comparisonChart)
open P4AOriginalSixthLaterSemantics (Source eval coordinates comparison endpoint R17)
open Certificates.P2OriginalSixthElevenLogSemantics (R0 S6 H5)
open P4AOriginalCompleteSixthChronology (laterEligible)

def action (j : Fin 4) : Cell := ⟨15+j.val,by omega⟩

@[simp] theorem stage_action (j : Fin 4) : stage (action j)=7 := by
  fin_cases j <;> rfl

@[simp] theorem comparison_action (j : Fin 4) (t : Point) : comparison (action j) t=R17 t := by
  fin_cases j <;> rfl

def row (j : Fin 4) (i : ℕ) : Affine := ((rows (action j))[i]?).getD 0

private theorem row_mem (j : Fin 4) (i : ℕ) (hi : i<(rows (action j)).length) :
    row j i∈rows (action j) := by
  simpa [row,hi] using (show (rows (action j))[i] ∈ rows (action j) from List.getElem_mem hi)

private theorem source_less (j : Fin 4) (t : Point) (h : Source (action j) t) :
    R0 t < R17 t ∧ R17 t < endpoint (action j) t := by
  have h49 : 49<(rows (action j)).length := by fin_cases j <;> decide
  have lo := P4AOriginalSixthLaterSemantics.source_r17_above_r0 (action j) t h
    (by fin_cases j <;> rfl)
  have hi := h (row j 49) (row_mem j 49 h49)
  have eq49 : eval (row j 49) (coordinates (action j) t)=endpoint (action j) t-R17 t := by
    fin_cases j <;> norm_num [action,row,rows,coordinates,P4AOriginalSixthLaterLiteral.mapped,eval,
      endpoint,P4AOriginalSixthLaterLiteral.descending,P4AOriginalSixthLaterSemantics.selectedSum,
      P4AOriginalSixthLaterLiteral.mask,Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit,Certificates.P2OriginalSixthElevenLogSemantics.eta,
      Fin.sum_univ_succ,R17] <;> ring
  rw [eq49] at hi
  exact ⟨lo,sub_pos.mp hi⟩

theorem original_gate (j : Fin 4) (A N : ℝ) (pre : List ℕ) :
    let t := primeHistoryLogCoordinates N 6 pre
    laterEligible 7 A N (action j) pre ↔
      pre.length=6 ∧ Source (action j) t ∧ H5 t<A ∧ A≤R17 t := by
  dsimp only
  simp only [laterEligible,stage_action,comparison_action,true_and]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩,
    fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,(source_less _ _ h.2.1).2⟩⟩

theorem earlier_gate_implies (j : Fin 4) (A N : ℝ) (pre : List ℕ)
    (hl : pre.length=6) (hs : Source (action j) (primeHistoryLogCoordinates N 6 pre))
    (h5 : H5 (primeHistoryLogCoordinates N 6 pre)<A)
    (hA : A≤R0 (primeHistoryLogCoordinates N 6 pre)) :
    laterEligible 7 A N (action j) pre :=
  (original_gate j A N pre).mpr ⟨hl,hs,h5,hA.trans (source_less _ _ hs).1.le⟩

theorem affine_gate (j : Fin 4) (t : Point) :
    (P4AOriginalCompleteSixthAffinePrograms.laterComparisonA (action j)).eval t=R17 t := by
  rw [P4AOriginalCompleteSixthAffinePrograms.laterComparisonA_exact,comparison_action]

/-- On an original eighth source, the complete all-subset bound controls
the new candidate before any cutoff comparison with R0 or R17. -/
theorem actual_candidate_below_eighth (j : Fin 4) (c : P4AOriginalFull87SourceDictionary.Cell)
    (t : Fin 8 → ℝ) (h8 : P4AOriginalFull87SourceDictionary.Source c t)
    (hs : Source (action j) (P4AOriginalFull87CompleteSixthBound.firstSix t)) :
    endpoint (action j) (P4AOriginalFull87CompleteSixthBound.firstSix t) <
      P4AOriginalFull87SourceDictionary.comparison c t := by
  apply (P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent _ _ hs).trans_le
  exact P4AOriginalFull87CompleteSixthBound.source_sixth_tents c t h8
    (P4AOriginalSixthLaterLiteral.mask (action j)) (P4AOriginalSixthLaterSemantics.original_mask_range _)

def kernel (j : Fin 4) (t : Point) : ℝ :=
  4*(endpoint (action j) t-R17 t)/((R17 t-S6 t)*(endpoint (action j) t-S6 t)*∏ i,t i)

/-- The numerator and first residual denominator use the same original
R17. The actual prefix parent can lie strictly below that plane. -/
theorem kernel_le_actual (j : Fin 4) (t : Point) (A : ℝ) (hs : Source (action j) t)
    (hA : S6 t<A) (hAR : A≤R17 t) (hp : 0<∏ i,t i) :
    kernel j t ≤ 4*(1/(A-S6 t)-1/(endpoint (action j) t-S6 t))/(∏ i,t i) := by
  have hr : 0<R17 t-S6 t := sub_pos.mpr (hA.trans_le hAR)
  have hm : 0<endpoint (action j) t-S6 t := sub_pos.mpr ((hA.trans_le hAR).trans (source_less j t hs).2)
  have hrec : 1/(R17 t-S6 t)≤1/(A-S6 t) :=
    one_div_le_one_div_of_le (sub_pos.mpr hA) (sub_le_sub_right hAR _)
  calc
    kernel j t = 4*(1/(R17 t-S6 t)-1/(endpoint (action j) t-S6 t))/(∏ i,t i) := by
      unfold kernel
      field_simp [ne_of_gt hr,ne_of_gt hm,ne_of_gt hp]
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hrec _) (by norm_num)) hp.le

end
end ImbalancedChen.P4AOriginalNonsingletonComparison
