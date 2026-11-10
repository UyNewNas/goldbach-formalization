import ImbalancedChen.P2OriginalLaterSixthCorrections

/-! Five actual affine entries in every one of the original nineteen
row lists. They retain their genuine chart and include the R17 comparison
on the last four rows. -/
namespace ImbalancedChen.P4AOriginalLaterSixthHistoryRows
noncomputable section
open scoped BigOperators
open P4AOriginalSixthLaterLiteral (Cell Point Affine rows mapped)
open P4AOriginalSixthLaterSemantics (Source endpoint comparison R17 eval coordinates)
open Certificates.P2OriginalSixthElevenLogSemantics (H3 H5 R0 S5 S6 W)

def id (c : Cell) : Fin 5→ℕ := ![
  ![9,9,9,9,9,9,8,8,8,8,8,8,8,8,8,5,5,5,5] c,
  ![10,10,10,10,10,10,9,9,9,9,9,9,9,9,9,6,6,6,6] c,
  ![11,11,11,11,11,11,10,10,10,10,10,10,10,10,10,7,7,7,7] c,
  ![44,44,45,45,45,45,41,41,41,41,41,41,41,41,62,49,49,49,49] c,
  ![57,57,58,58,58,58,54,54,54,54,53,53,53,53,54,62,62,62,62] c]

def row (c : Cell) (g : Fin 5) : Affine := (rows c).getD (id c g) 0
def margin (c : Cell) (t : Point) : Fin 5→ℝ :=
  ![R0 t-H3 t,R0 t-H5 t,R0 t-W t,endpoint c t-comparison c t,S6 t+3*t 5-endpoint c t]

theorem row_mem (c : Cell) (g : Fin 5) : row c g∈rows c := by
  have hi : id c g<(rows c).length := by fin_cases c <;> fin_cases g <;> decide
  rw [row,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row_evaluation (c : Cell) (g : Fin 5) (t : Point) :
    eval (row c g) (coordinates c t)=margin c t g := by
  fin_cases c <;> fin_cases g <;>
    norm_num [row,id,margin,rows,coordinates,mapped,eval,endpoint,comparison,R17,
      P4AOriginalSixthLaterLiteral.comparisonChart,P4AOriginalSixthLaterLiteral.descending,
      P4AOriginalSixthLaterLiteral.mask,P4AOriginalSixthLaterSemantics.selectedSum,
      Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,Certificates.P2OriginalSixthElevenLogSemantics.bit,
      Certificates.P2OriginalSixthElevenLogSemantics.chart,Certificates.P2OriginalSixthElevenLogSemantics.eta,
      R0,H3,H5,S5,S6,W,Certificates.P2OriginalSixthElevenLogSemantics.descending33,
      Certificates.P2OriginalSixthElevenLogSemantics.ascending34,Fin.sum_univ_succ] <;> ring

theorem source_margins (c : Cell) (t : Point) (hs : Source c t) :
    H3 t<R0 t ∧ H5 t<R0 t ∧ W t<R0 t ∧ comparison c t<endpoint c t ∧ endpoint c t-S6 t<3*t 5 := by
  have h (g : Fin 5) : 0<margin c t g := by rw [←row_evaluation]; exact hs _ (row_mem c g)
  exact ⟨sub_pos.mp (h 0),sub_pos.mp (h 1),sub_pos.mp (h 2),sub_pos.mp (h 3),by
    have hh : 0<S6 t+3*t 5-endpoint c t := h 4
    linarith⟩

end
end ImbalancedChen.P4AOriginalLaterSixthHistoryRows
