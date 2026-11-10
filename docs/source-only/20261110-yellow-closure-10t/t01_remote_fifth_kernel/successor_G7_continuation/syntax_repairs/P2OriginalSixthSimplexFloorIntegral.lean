import ImbalancedChen.P2OriginalSixthLogArchive

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
This endpoint concerns the sum of the original 2631 actual physical
simplex integrals. Source-region ownership and same-policy admission
are separate necessary theorems; neither is presumed here.
-/
namespace ImbalancedChen.P2OriginalSixthSimplexFloorIntegral
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSixthLogArchive
open P2OriginalSixthMomentRow
def support (i : Fin 11) (s : Fin (archive i).simplices.size) : Set Point :=
  rowSupport (physicalRow i s).toRow
def cellSimplexIntegral (i : Fin 11) : ℝ :=
  ∑ s : Fin (archive i).simplices.size, ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral (sourceCell i) (support i s)
def originalSimplexIntegral : ℝ := ∑ i : Fin 11, cellSimplexIntegral i

theorem original_stored_row_floor (i : Fin 11) (s : Fin (archive i).simplices.size) :
    ((logAt i s).newFloor : ℝ)/(2:ℝ)^96 ≤ ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.sourceIntegral (sourceCell i) (support i s) := by
  apply P2OriginalSixthPhysicalRow.original_physical_row_floor
  have h := (original_moment_rows i s).2.2.2.2.2.2
  simp only [checkStoredRowFloor,P2OriginalLogMomentQ96CheckerSourceOnly.checkStoredQ96,
    h,le_refl,decide_true]

theorem original_cell_stored_floor (i : Fin 11) :
    (cellFloorNumerator i : ℝ)/(2:ℝ)^96 ≤ cellSimplexIntegral i := by
  have h := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin (archive i).simplices.size))) =>
    original_stored_row_floor i s)
  simpa only [cellSimplexIntegral,cellFloorNumerator,Int.cast_sum,Finset.sum_div] using h

/-- The full original G7 replacement floor is proved from its individual
original rows, never by flooring their total or adding the old total. -/
theorem original_all2631_stored_floor :
    (1208544915921356327515701 : ℝ)/(2:ℝ)^96 ≤ originalSimplexIntegral := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 11))) =>
    original_cell_stored_floor i)
  have he : (∑ i : Fin 11, (cellFloorNumerator i : ℝ)/(2:ℝ)^96) =
      (1208544915921356327515701 : ℝ)/(2:ℝ)^96 := by
    rw [← Finset.sum_div,← Int.cast_sum]
    change (aggregateNumerator : ℝ)/(2:ℝ)^96 = _
    rw [original_q96_aggregate]
    rfl
  rw [he] at h
  exact h

end
end ImbalancedChen.P2OriginalSixthSimplexFloorIntegral
