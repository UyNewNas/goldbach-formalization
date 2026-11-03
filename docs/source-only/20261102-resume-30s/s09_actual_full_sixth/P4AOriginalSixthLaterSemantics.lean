import ImbalancedChen.P4AOriginalSixthLaterLiteral
import ImbalancedChen.P2OriginalSixthElevenLogSemantics
import ImbalancedChen.VariableEnvelope

/-! SOURCE ONLY / UNCOMPILED. The nineteen exact later source domains,
with their original physical chart, endpoints and source licensing rows.
No licence field, cap comparison hypothesis, point evaluation, polytope
exhaustion or saved integral is used in the source licence theorem. -/
namespace ImbalancedChen.P4AOriginalSixthLaterSemantics
noncomputable section
open scoped Classical BigOperators
open P4AOriginalSixthLaterLiteral

def eval (r : Affine) (t : Point) : ℝ := r 0 + ∑ i : Fin 6, r i.succ * t i

def coordinates (c : Cell) (t : Point) : Point :=
  if mapped c then Certificates.P2OriginalSixthElevenLogSemantics.chart t else t

/-- Every original named row is retained, including old activation/branch
exclusions. The chart is invertible by Certificates.P2OriginalSixthElevenLogSemantics.physical_chart. -/
def Source (c : Cell) (t : Point) : Prop :=
  ∀ r ∈ rows c, 0 < eval r (coordinates c t)

def selectedSum (c : Cell) (t : Point) : ℝ := Certificates.P2OriginalSixthElevenLogSemantics.selectedSum (mask c) t

def endpoint (c : Cell) (t : Point) : ℝ :=
  (if descending c then 57 / 64 - 3 * selectedSum c t / 2
   else (1 + selectedSum c t) / 2) - Certificates.P2OriginalSixthElevenLogSemantics.eta

/-- R0, D33 and A34 are the three ORIGINAL comparison charts. The two
comparison-only G13 corrections are deliberately not additional actions. -/
def comparison (c : Cell) (t : Point) : ℝ :=
  if comparisonChart c = 0 then Certificates.P2OriginalSixthElevenLogSemantics.R0 t
  else if comparisonChart c = 1 then Certificates.P2OriginalSixthElevenLogSemantics.descending33 t
  else Certificates.P2OriginalSixthElevenLogSemantics.ascending34 t

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem opposite_license_identity (c : Cell) (t : Point) :
    eval (oppositeLicenseRow c) (coordinates c t) =
      (if descending c then (1 + selectedSum c t) / 2
       else 57 / 64 - 3 * selectedSum c t / 2) - endpoint c t := by
  fin_cases c <;>
    norm_num [eval, oppositeLicenseRow, coordinates, mapped, descending,
      selectedSum, mask, endpoint, Certificates.P2OriginalSixthElevenLogSemantics.chart, Certificates.P2OriginalSixthElevenLogSemantics.R0, Certificates.P2OriginalSixthElevenLogSemantics.S5, Certificates.P2OriginalSixthElevenLogSemantics.H5,
      Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, Certificates.P2OriginalSixthElevenLogSemantics.bit, Certificates.P2OriginalSixthElevenLogSemantics.eta, Fin.sum_univ_succ] <;> ring

/-- Actual literal source membership supplies both tent licences. -/
theorem source_endpoint_lt_selected_tent (c : Cell) (t : Point) (h : Source c t) :
    endpoint c t < VariableEnvelope.v (selectedSum c t) := by
  have ho := h (oppositeLicenseRow c) (oppositeLicenseRow_mem c)
  rw [opposite_license_identity] at ho
  rw [VariableEnvelope.v_eq_min]
  dsimp only [VariableEnvelope.A, VariableEnvelope.C]
  have he : (0 : ℝ) < Certificates.P2OriginalSixthElevenLogSemantics.eta := by norm_num [Certificates.P2OriginalSixthElevenLogSemantics.eta]
  by_cases hd : descending c = true
  · simp only [hd, Bool.true_eq_true, if_true] at ho
    have hh : endpoint c t = 57 / 64 - 3 * selectedSum c t / 2 - Certificates.P2OriginalSixthElevenLogSemantics.eta := by
      simp only [endpoint, hd, Bool.true_eq_true, if_true]
    exact lt_min (by linarith) (by linarith)
  · have hf : descending c = false := Bool.eq_false_iff.mpr hd
    simp only [hf, Bool.false_eq_true, if_false] at ho
    have hh : endpoint c t = (1 + selectedSum c t) / 2 - Certificates.P2OriginalSixthElevenLogSemantics.eta := by
      simp only [endpoint, hf, Bool.false_eq_true, if_false]
    exact lt_min (by linarith) (by linarith)

theorem original_mask_range (c : Cell) : mask c ∈ Finset.Icc 1 63 := by
  fin_cases c <;> norm_num [mask]

theorem original_stage_range (c : Cell) : stage c < 8 := by
  fin_cases c <;> norm_num [stage]

/-- The numerical library's two G13 comparison corrections alter no cap.
The complete genuine later-action list has nineteen entries, not twenty-one. -/
theorem later_action_count : Fintype.card Cell = 19 := by decide

end
end ImbalancedChen.P4AOriginalSixthLaterSemantics
