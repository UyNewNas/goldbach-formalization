import ImbalancedChen.P2OriginalSaving18UnequalArchive
import ImbalancedChen.P2OriginalPhysicalSimplexMomentRow
import ImbalancedChen.P4AOriginalFull87ArchivedIntegralRows

/-! All 60,820 original unequal-parent simplices. The three affine
profiles are the literal nine-ascending, fifty-ascending and fifty-
descending cases. Their original log-moment floors replace each
simplex's previous Jensen bound on the same strict source. -/
namespace ImbalancedChen.P2OriginalSaving18UnequalIntegral
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory VariableEnvelope
open P2OriginalSaving18UnequalArchive
open P2OriginalFull87PullingCell (rowVertices row_det sum_support_integrals_le)
open P2OriginalSaving16OriginalArchive (QPoint evalQ castPoint)
open P2OriginalSaving19OwnedSource (eval eval_cast eval_sub eval_interpolate)
open P4AOriginalFull87SourceDictionary (Cell Point comparison newCap)
open P4AOriginalFull87EighthKernelControl (kernel residual total product)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P2OriginalLogMomentQ96CheckerSourceOnly (factorLowerQ80 oldFloorQ96 newFloorQ96)
open P2OriginalPhysicalSimplexMomentRow
  (rowCoordinates rowMassQ rowMeansQ rowMomentsQ rowTopsQ rowDensity rowGap rowFactors
   row_pointInterpolate_coordinates checkStoredRowFloor stored_row_floor_sound)

def physical (c : Kind) (s : Row c) : P2OriginalPhysicalSimplexMomentRow.Row :=
  ⟨rowVertices (data c) s,gapsQ c s,factorsQ c s,row_det (original_geometry c) s,
    (original_positive_inputs c s).1,(original_positive_inputs c s).2.1,
    (original_positive_inputs c s).2.2⟩

theorem eval_R (c : Kind) (t : Point) : eval (R c) t = comparison (originalCell c) t := by
  cases c <;> norm_num [R,eval,OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
    originalCell,comparison,P4AOriginalRemainingEighthSources.comparison,A,C,Fin.sum_univ_succ] <;> ring

theorem eval_M (c : Kind) (t : Point) : eval (M c) t = newCap (originalCell c) t := by
  cases c <;> norm_num [M,eval,OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
    originalCell,newCap,P4AOriginalRemainingEighthSources.newCap,
    P4AOriginalRemainingEighthSources.descendingNew,P4AOriginalRemainingEighthSources.selectedSum,
    P4AOriginalRemainingEighthSources.selected,P4AOriginalRemainingEighthSources.eta,A,C,Fin.sum_univ_succ] <;> ring

theorem eval_coord (j : Fin 8) (t : Point) : eval (coord j) t = t j := by
  fin_cases j <;> norm_num [eval,OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
    coord,Pi.single_apply,Fin.sum_univ_succ]

theorem eval_total (t : Point) : eval totalRow t = total t := by
  norm_num [eval,OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
    totalRow,total,coord,Pi.single_apply,Fin.sum_univ_succ] <;> ring

theorem original_factors (c : Kind) (t : Point) :
    (∏ j : Fin 10, eval (factors c j) t) =
      (comparison (originalCell c) t - total t) * (newCap (originalCell c) t - total t) * product t := by
  simp [factors,Fin.prod_univ_succ,eval_sub,eval_R,eval_M,eval_total,eval_coord,product] <;> ring

theorem interpolate_affine (a : Affine) (r : P2OriginalPhysicalSimplexMomentRow.Row) (t : Point) :
    P2OriginalSaving19SimplexMoments.interpolate (fun i => (evalQ a (r.verticesQ i) : ℝ))
      (rowCoordinates r t) = eval a t := by
  have h := eval_interpolate a (fun i => castPoint (r.verticesQ i)) (rowCoordinates r t)
  rw [row_pointInterpolate_coordinates r t] at h
  simpa only [eval_cast] using h.symm

theorem original_density (c : Kind) (s : Row c) (t : Point) :
    rowDensity (physical c s) t = kernel (originalCell c) t := by
  have hg : rowGap (physical c s) t = eval (gapRow c) t := interpolate_affine _ _ _
  have hf (j : Fin 10) : rowFactors (physical c s) t j = eval (factors c j) t :=
    interpolate_affine _ _ _
  rw [rowDensity,hg]
  simp_rw [hf]
  rw [original_factors,gapRow,eval_sub,eval_M,eval_R]
  rfl

/-- The closed field equalities also bind the previous and refined
Q96 floors and every saved per-factor Q80 floor to this same simplex. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_moment_operations : ∀ (c : Kind) (s : Row c),
    let r := physical c s
    let w := momentRow c s
    (∀ j : Fin 10, (w.factorFloorsQ80.getD j.val 0 : ℚ) / 2^80 =
      factorLowerQ80 (rowMomentsQ r j)) ∧
    w.oldFloorQ96 = oldFloorQ96 (rowMassQ r) (rowMeansQ r) ∧
    w.newFloorQ96 = newFloorQ96 (rowMassQ r) (rowMeansQ r) (rowMomentsQ r) := by decide

theorem original_s18_row (c : Kind) (s : Row c) :
    ((momentRow c s).newFloorQ96 : ℝ)/(2 : ℝ)^96 ≤
      ∫ t in P2OriginalFull87PullingCell.rowSupport (data c) s (row_det (original_geometry c) s),
        kernel (originalCell c) t := by
  have he := (original_moment_operations c s).2.2
  have hh : checkStoredRowFloor (physical c s) (momentRow c s).newFloorQ96 = true := by
    simp only [checkStoredRowFloor,P2OriginalLogMomentQ96CheckerSourceOnly.checkStoredQ96,he,
      le_refl,decide_true]
  have h := stored_row_floor_sound (physical c s) (momentRow c s).newFloorQ96 hh
  simpa only [original_density] using h

theorem original18_archived_cell_le_integral (c : Kind) :
    (selectedQ c : ℝ) ≤ cellIntegral (originalCell c) := by
  rw [original_selected_records,Rat.cast_sum]
  refine (Finset.sum_le_sum ?_).trans (sum_support_integrals_le (originalCell c) (data c) (original_geometry c))
  intro s _
  exact_mod_cast original_s18_row c s

theorem original_stage18_floor_le_sum_full87_integrals :
    (1033407531585213315823239 : ℝ)/(2 : ℝ)^96 ≤ ∑ c : Kind, cellIntegral (originalCell c) := by
  have he : (∑ c : Kind, (selectedQ c : ℝ)) = (1033407531585213315823239 : ℝ)/(2 : ℝ)^96 := by
    exact_mod_cast original_stage18_total
  rw [← he]
  exact Finset.sum_le_sum (fun c _ => original18_archived_cell_le_integral c)

/-- The actual original saved rational of every one of the first 57
paid cells is directed below its own physical source integral. -/
abbrev Paid57 := P4AOriginalFull87ArchivedIntegralRows.Paid ⊕ Kind
def originatingCell : Paid57 → Cell
  | .inl p => P4AOriginalFull87ArchivedIntegralRows.paidCell p
  | .inr c => originalCell c

theorem original57_archived_cell_le_integral (i : Paid57) :
    (P4AOriginalFull87ArchivedIntegralRows.archived (originatingCell i) : ℝ) ≤
      cellIntegral (originatingCell i) := by
  cases i with
  | inl p => exact P4AOriginalFull87ArchivedIntegralRows.paid_cell_le_integral p
  | inr c => exact original18_archived_cell_le_integral c

theorem originatingCell_injective : Function.Injective originatingCell := by
  intro i j h
  cases i with
  | inl p =>
    cases j with
    | inl q => exact congrArg Sum.inl (P4AOriginalFull87ArchivedIntegralRows.paidCell_injective h)
    | inr c =>
      rcases p with (p|p)|p <;> cases c <;>
        simp [originatingCell,P4AOriginalFull87ArchivedIntegralRows.paidCell,originalCell] at h
  | inr c =>
    cases j with
    | inl p =>
      rcases p with (p|p)|p <;> cases c <;>
        simp [originatingCell,P4AOriginalFull87ArchivedIntegralRows.paidCell,originalCell] at h
    | inr d => cases c <;> cases d <;> simp_all [originatingCell,originalCell]

def paid57Numerical : ℚ := P4AOriginalFull87ArchivedIntegralRows.paidNumerical +
  (1033407531585213315823239 : ℚ)/2^96

theorem paid57_archive_sum : (∑ i : Paid57, P4AOriginalFull87ArchivedIntegralRows.archived (originatingCell i)) =
    paid57Numerical := by
  rw [Fintype.sum_sum_type]
  exact congrArg₂ (· + ·) P4AOriginalFull87ArchivedIntegralRows.paid_archive_sum original_stage18_total

theorem paid57_numerical_le_full_source : (paid57Numerical : ℝ) ≤ ∑ c : Cell, cellIntegral c := by
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ => original57_archived_cell_le_integral i)
  have he : (∑ i : Paid57, (P4AOriginalFull87ArchivedIntegralRows.archived (originatingCell i) : ℝ)) =
      (paid57Numerical : ℝ) := by exact_mod_cast paid57_archive_sum
  rw [he] at hp
  let A : Finset Cell := Finset.univ.image originatingCell
  have ha : ∑ c ∈ A, cellIntegral c = ∑ i : Paid57, cellIntegral (originatingCell i) :=
    Finset.sum_image (fun i _ j _ hij => originatingCell_injective hij)
  rw [← ha] at hp
  apply hp.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) ?_)
  intro c _ _
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (P4AOriginalFull87StrictActionTrim.sourceSet_measurable c)] with t ht
  exact (P4AOriginalFull87EighthKernelControl.kernel_bounds ht).1

end
end ImbalancedChen.P2OriginalSaving18UnequalIntegral
