import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P1OriginalHistoricalFifthOwnCubeAffineGates

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Real historical accepted fifth NPZ row zero:
[n,l1,l2,l3,l4,l5,mask,vertex_gap_sum,A,B]
= [400,31,30,27,26,25,28,5984,3200,800].
NPZ SHA256 2473b7457e09eb67b4f0b99a7c58c4a52ccd5262d8bf28138f638dd562428d6e.
The selected cap in that producer is VARIABLE M_{3,4,5}(t), not a saved
constant cap5. This file constructs ONE tiny genuine mesh subcell of the
saved box and new admissible buffer/chi/omega parameters. Those parameters
are not claimed to have been saved by the historical producer. The full
historical box, numeric weight, global policy identity and cost stay OPEN.
-/

namespace ImbalancedChen.P1HistoricalFifthSavedRowZero
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope HistoricalThirdCoarse
open P1OriginalVariableFifthContinuation

def savedGrid : ℕ := 400
def savedLo : Fin 5 → ℕ := ![31, 30, 27, 26, 25]
def savedMask : ℕ := 28
def selected : Finset (Fin 5) := {2, 3, 4}

/-- Each saved 1/400 interval contains 960 intervals of this common
original 0..19/96 mesh. Only its first interval is selected here. -/
def mesh : ℕ := 75999
def cell : Fin 5 → Fin (mesh + 1) :=
  ![⟨29760, by norm_num [mesh]⟩, ⟨28800, by norm_num [mesh]⟩,
    ⟨25920, by norm_num [mesh]⟩, ⟨24960, by norm_num [mesh]⟩,
    ⟨24000, by norm_num [mesh]⟩]
def row : FifthRow mesh := ⟨cell, selected⟩

/-- Newly chosen admissible parameters, not historical saved parameters. -/
def buffer : ℚ := 1 / 10000
def chi : ℝ := 1 / 384000
def omega0 : ℝ := 1 / 100

theorem selected_is_saved_mask : selected = Finset.univ.filter
    (fun i : Fin 5 => Nat.testBit savedMask i.val) := by
  ext i
  fin_cases i <;> norm_num [selected, savedMask, Nat.testBit]

theorem cell_is_saved_lower_refinement (i : Fin 5) : (cell i).val = 960 * savedLo i := by
  fin_cases i <;> norm_num [cell, savedLo]

theorem new_parameters_admissible :
    0 < (buffer : ℝ) ∧ (buffer : ℝ) < (3 / 256 : ℝ) / 100 ∧
      0 < chi ∧ chi < (buffer : ℝ) / 10 ∧ 0 < omega0 := by
  norm_num [buffer, chi, omega0]

/-- This is a real subcell of the authenticated saved rectangle, not an
assertion that the single subcell exhausts that rectangle. -/
theorem subcell_subset_saved_box {t : Fin 5 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) mesh cell) :
    ∀ i, (savedLo i : ℝ) / savedGrid ≤ t i ∧
      t i < ((savedLo i : ℝ) + 1) / savedGrid := by
  intro i
  have hi := mem_logPrimeMeshCell.mp ht i
  fin_cases i <;>
    norm_num [cell, mesh, savedLo, savedGrid, logPrimeMeshLo, logPrimeMeshHi,
      logPrimeMeshPoint, logPrimeMeshStep] at hi ⊢ <;> linarith

theorem subcell_nonempty : (logPrimeMeshCell 0 (19 / 96) mesh cell).Nonempty := by
  refine ⟨fun i => (qLogPrimeMeshLo 0 (19 / 96) mesh cell i : ℝ), ?_⟩
  apply mem_logPrimeMeshCell.mpr
  intro i
  fin_cases i <;> norm_num [cell, mesh, qLogPrimeMeshLo, qLogPrimeMeshPoint,
    logPrimeMeshLo, logPrimeMeshHi, logPrimeMeshPoint, logPrimeMeshStep]

/-- The complete full/selected-square upper bound is checked exactly,
including the compulsory half-level test. No gain is used as a premise. -/
theorem selected_gate_upper : selectedCapLower selected 0
    (qLogPrimeMeshHi 0 (19 / 96) mesh cell) ≤ (11 / 20 : ℚ) := by
  unfold selectedCapLower
  apply Finset.max'_le
  intro q hq
  unfold selectedCapLowerSet at hq
  rcases Finset.mem_insert.mp hq with hq | hq
  · rw [hq]
    norm_num
  rcases Finset.mem_insert.mp hq with hq | hq
  · rw [hq]
    norm_num
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hq
    fin_cases k <;> norm_num [prefixSquareExpr, Finset.sum_filter, Fin.sum_univ_succ,
      qLogPrimeMeshHi, qLogPrimeMeshPoint, mesh, cell]
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    fin_cases k <;> norm_num [selected, selectedSquareExpr, Finset.sum_filter,
      Fin.sum_univ_succ, qLogPrimeMeshHi, qLogPrimeMeshPoint, mesh, cell] at *

/-- A passing buffered whole-cell gateCheck for the authentic mask on
this constructed subcell. The literal variable candidate is retained. -/
theorem row_gateCheck : gateCheck buffer mesh row = true := by
  rw [gateCheck, decide_eq_true_eq]
  change selectedCapLower selected 0 (qLogPrimeMeshHi 0 (19 / 96) mesh cell) +
    2 * buffer < qVLo
      (∑ i ∈ selected, qLogPrimeMeshLo 0 (19 / 96) mesh cell i)
      (∑ i ∈ selected, qLogPrimeMeshHi 0 (19 / 96) mesh cell i)
  have hgap : (11 / 20 : ℚ) + 2 * buffer < qVLo
      (∑ i ∈ selected, qLogPrimeMeshLo 0 (19 / 96) mesh cell i)
      (∑ i ∈ selected, qLogPrimeMeshHi 0 (19 / 96) mesh cell i) := by
    norm_num [selected, buffer, qVLo, qA, qC, qLogPrimeMeshLo, qLogPrimeMeshHi,
      qLogPrimeMeshPoint, mesh, cell]
  exact (add_le_add_right selected_gate_upper (2 * buffer)).trans_lt hgap

/-- The ORIGINAL third owner really belongs to cells, including the
whole firstStop endpoint and actual width, rather than an ordinary parent. -/
theorem original_third_owner_selected :
    historicalPrefixProject (by omega : 3 ≤ 5) cell ∈ cells (buffer : ℝ) chi mesh := by
  apply (mem_cells (buffer : ℝ) chi mesh _).mpr
  norm_num [HistoricalThirdCoarse.box, RationalBox.WellFormed, RationalBox.width,
    historicalPrefixProject, qLogPrimeMeshLo, qLogPrimeMeshHi, qLogPrimeMeshPoint,
    cell, mesh, buffer, chi, extendedFirstStop]

theorem original_fifth_owner_selected : cell ∈
    P1OriginalCoarseFifthContinuation.selectedFifthCells buffer chi mesh omega0 {cell} := by
  apply (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells buffer chi mesh omega0 {cell} cell).mpr
  refine ⟨by simp, original_third_owner_selected, ?_⟩
  norm_num [omega0, historicalPrefixProject, qLogPrimeMeshLo, qLogPrimeMeshPoint, cell, mesh]

theorem row_eligible {t : Fin 5 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) mesh cell) :
    eligible buffer chi mesh omega0 {cell} row t :=
  ⟨original_fifth_owner_selected, row_gateCheck, ht⟩

/-- A crude baseline lower bound is sufficient for every original parent
cube here; the actual Gamma remains unchanged and may be larger. -/
theorem original_third_level_gt_half : (1 / 2 : ℝ) <
    levelExponent (buffer : ℝ)
      (HistoricalThirdCoarse.box mesh (historicalPrefixProject (by omega : 3 ≤ 5) cell)) := by
  let b := HistoricalThirdCoarse.box mesh (historicalPrefixProject (by omega : 3 ≤ 5) cell)
  have hbase : (qVLo b.lx b.ux : ℝ) ≤ (gamma (buffer : ℝ) b : ℝ) := by
    exact_mod_cast baseline_le_gamma (buffer : ℝ) b
  have hval : (qVLo b.lx b.ux : ℝ) = (431 / 800 : ℝ) := by
    norm_num [b, HistoricalThirdCoarse.box, historicalPrefixProject, qLogPrimeMeshLo,
      qLogPrimeMeshHi, qLogPrimeMeshPoint, cell, mesh, qVLo, qA, qC]
  rw [hval] at hbase
  change (1 / 2 : ℝ) < (gamma (buffer : ℝ) b : ℝ) - 2 * (buffer : ℝ)
  norm_num [buffer] at *
  linarith

/-- Every real point of this genuine subcell meets the literal original
firstStop and rawQ3 parent geometry; no fifth own cube is pre-imposed. -/
theorem subcell_in_original_jointRegion {t : Fin 5 → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) mesh cell) :
    t ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion
      (buffer : ℝ) chi mesh omega0 cell := by
  have h0 := mem_logPrimeMeshCell.mp ht 0
  have h1 := mem_logPrimeMeshCell.mp ht 1
  have h2 := mem_logPrimeMeshCell.mp ht 2
  have h3 := mem_logPrimeMeshCell.mp ht 3
  have h4 := mem_logPrimeMeshCell.mp ht 4
  norm_num [cell, mesh, logPrimeMeshLo, logPrimeMeshHi, logPrimeMeshPoint,
    logPrimeMeshStep] at h0 h1 h2 h3 h4
  have hcurrent := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    buffer chi mesh omega0 {cell} cell original_fifth_owner_selected ht
  apply (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_jointRegion _ _ _ _ _ _).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (P1OriginalHistoricalFifthOwnCubeAffineGates.firstLabelRegion_on_cell
      (buffer : ℝ) mesh cell t ht).mpr
    norm_num [cell, mesh, buffer, extendedFirstStop, logPrimeMeshHi,
      logPrimeMeshPoint, logPrimeMeshStep]
  · apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i <;> linarith
  · norm_num [initial, extendedDistributionCap, buffer]
    linarith
  · rw [hcurrent]
    linarith [original_third_level_gt_half]
  · rw [hcurrent]
    linarith [original_third_level_gt_half]

/-- The historical mask keeps its actual variable endpoint. There is no
saved constant cap5 hidden in the row's Jensen statistics. -/
theorem row_candidate_is_literal (t : Fin 5 → ℝ) :
    candidate (buffer : ℝ) row.selected t =
      v (t 2 + t 3 + t 4) - 2 * (buffer : ℝ) := by
  rw [candidate, envelope_eq_v]
  simp [row, selected, add_assoc]

theorem row_candidate_buffered_upper (t : Fin 5 → ℝ) :
    candidate (buffer : ℝ) row.selected t ≤ (153 / 256 : ℝ) - 2 * (buffer : ℝ) := by
  rw [row_candidate_is_literal]
  exact sub_le_sub_right (v_le_cap _) _

/-- Exact actual rawQ3 identification on this selected original owner,
including the rough-activation decision at the same first-three history. -/
theorem actual_original_rawQ3 (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ)
    (hpos : ∀ i, 0 < p i)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) mesh cell) :
    rawLevel (buffer : ℝ) chi mesh omega0 (N : ℝ)
      (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdHistory p) =
      (N : ℝ) ^ levelExponent (buffer : ℝ)
        (HistoricalThirdCoarse.box mesh
          (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdOwner cell)) := by
  rw [HistoricalThirdCoarse.P1OriginalCoarseFifth.rawLevel_on_fifth_cell
    (buffer : ℝ) chi mesh omega0 N hN p hpos cell ht,
    P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
      buffer chi mesh omega0 {cell} cell original_fifth_owner_selected ht]

/-- The original first-label stop is proved for actual tuples in this
subcell. It is not replaced by the ordinary initial first cube alone. -/
theorem actual_original_firstStop (N : ℕ) (p : Fin 5 → ℕ)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) mesh cell) :
    firstStop (buffer : ℝ) mesh (N : ℝ) [p 0] := by
  apply (HistoricalThirdCoarse.P1OriginalCoarseFifth.firstStop_iff_log
    (buffer : ℝ) mesh N p).mpr
  exact ((HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_jointRegion
    (buffer : ℝ) chi mesh omega0 cell _).mp (subcell_in_original_jointRegion ht)).1
/-- Real target-deleted prime tuples in this subcell are actual next
candidates of the ORIGINAL T3 tree, with no assumed history-validity field. -/
theorem actual_original_candidate (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (p : Fin 5 → ℕ)
    (hp : p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.primeBox N)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) mesh cell) :
    p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (buffer : ℝ) chi mesh omega0 N cap := by
  apply (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_candidates_iff_log_on_cell
    (buffer : ℝ) chi mesh omega0 N cap hN hcap p cell ht).mpr
  have hi := mem_actualPrimeBoxTuples_iff.mp hp
  exact ⟨fun i => ⟨(hi i).1, (hi i).2.1, Nat.cast_nonneg _, (hi i).2.2.2⟩,
    subcell_in_original_jointRegion ht⟩

end
end ImbalancedChen.P1HistoricalFifthSavedRowZero