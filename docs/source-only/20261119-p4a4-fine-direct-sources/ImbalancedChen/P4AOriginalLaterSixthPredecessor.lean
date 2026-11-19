import ImbalancedChen.P4AOriginalLaterSixthMesh
import ImbalancedChen.P4AOriginalOrderedLaterChanged
import ImbalancedChen.P4AOriginalOrderedFifthOwner
import ImbalancedChen.P4AOriginalElevenOwnCaps

/-! The actual chronological predecessor on the same d+ history.
Saved sixth is absent by the sixth-coordinate cutoff. The eleven and
all earlier later candidates are compared individually on their true
physical domains. Both the raw acceptance test and the finite cap used
in the signed density get their own upper bound. -/
namespace ImbalancedChen.P4AOriginalLaterSixthPredecessor
noncomputable section
open Set VariableEnvelope
open scoped Classical BigOperators
open P2OriginalLaterSixthKernel (Piece action correction eval lower upper eval_lower eval_upper)
open P2OriginalLaterSixthSourceIntegral (owned)
open P2OriginalLaterSixthInnerTests (trim trim_region inner_factors)
open P4AOriginalLaterSixthPriorGeometry (regular previous_eleven previous_later)
open P4AOriginalLaterSixthMesh (Owner)
open P4AOriginalSavedSixthHistoricalOwner (bank root pre_len pre_log)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalSixthLaterLiteral (Cell stage)
open P4AOriginalSixthLaterSemantics (Source comparison endpoint)
open P4AOriginalFull87DataPolicy (active level5Exponent savedExponent elevenExponent afterLater cap5 Accepted)
open P5OriginalCommonRefinedConstructor (OriginalData actualParent5 originalSeed)
open P1OriginalVariableFourthContinuation (finiteMax_le finiteMax_seed_le)
open P1GuardFrozenFiniteCapAlgebra (rounded rounded_error protect_error protect)
open Certificates.P2OriginalSixthElevenLogSemantics (PhysicalCell newCap H5)
open P4AOriginalFull87HistoryCore (width)

theorem low_le_comparison (i : Piece) {t : Fin 6→ℝ} (ht : t∈owned i) :
    eval (lower i) t≤comparison (action i) t := by
  by_cases hc : correction i=true
  · have he : eval (upper i) t=comparison (action i) t := by
      rw [eval_upper,if_pos hc]
      fin_cases i <;> norm_num [correction] at hc <;> rfl
    exact (inner_factors i ht.1).2.2.trans_eq he
  · rw [eval_lower,if_neg hc]
theorem endpoint_range (c : Cell) {t : Fin 6→ℝ} (hs : Source c t) :
    0≤endpoint c t ∧ endpoint c t≤cap := by
  have hl := (P4AOriginalSixthSquareRows.later_comparison_half c t hs).trans
    (P4AOriginalLaterSixthHistoryRows.source_margins c t hs).2.2.2.1
  exact ⟨by linarith,(P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent c t hs).le.trans (v_le_cap _)⟩

theorem fifth_bounds (n : ℕ) {d : OriginalData} {N : ℕ} {p : Fin 6→ℕ} {i : Piece}
    (ht : actualPrimeTupleLog N p∈owned i) (ho : Owner d N p i) :
    root d N p≤level5Exponent n d (N:ℝ) (rosserAncestor 5 (pre p)) ∧
    level5Exponent n d (N:ℝ) (rosserAncestor 5 (pre p))≤eval (lower i) (actualPrimeTupleLog N p) := by
  let t := actualPrimeTupleLog N p
  have hs := ht.2.1
  have hcap := (endpoint_range (action i) hs).2
  have hf := (low_le_comparison i ht).trans
    ((P4AOriginalLaterSixthHistoryRows.source_margins (action i) t hs).2.2.2.1.le.trans hcap)
  have hpos := (P4AOriginalSixthSquareRows.later_source_basic (action i) t hs)
  have hx : 0<t 0 := (show (0:ℝ)<53/4608 by norm_num).trans
    (hpos.2.2.1.trans_le (hpos.2.2.2.antitone (Fin.zero_le 5)))
  have hroot : 0≤root d N p := by linarith only [hx,ho.first]
  have hr := protect_error n (root d N p) (actualParent5 d (N:ℝ) (pre p)) hroot ho.cap (ho.upper.trans hf)
  rw [level5Exponent,if_pos ((P4AOriginalFull87DataPolicy.active_ancestor _ _ 5 (by decide) _).mpr ho.active),
    P4AOriginalFull87DataPolicy.cap5_eq_protect,P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 5 (by decide),←ho.seed]
  exact ⟨hr.1,hr.2.2.trans ho.upper⟩

theorem earlier_eleven (i : Piece) {t : Fin 6→ℝ} (ht : t∈owned i) (hr : t∈regular)
    (c : Certificates.P2OriginalSixthElevenLogSemantics.Cell) (hc : PhysicalCell c t) :
    newCap c t≤eval (lower i) t := by
  obtain ⟨j,rfl⟩ := P4AOriginalElevenOwnCaps.sourceCell_surjective c
  exact previous_eleven i j ht hr hc

theorem raw_bounds {d : OriginalData} {N : ℕ} {p : Fin 6→ℕ} {i : Piece}
    (ht : actualPrimeTupleLog N p∈owned i) (hr : actualPrimeTupleLog N p∈regular)
    (ho : Owner d N p i) :
    ∀ k≤stage (action i),root d N p≤afterLater d (N:ℝ) (pre p) k ∧
      afterLater d (N:ℝ) (pre p) k≤eval (lower i) (actualPrimeTupleLog N p) := by
  let t := actualPrimeTupleLog N p
  let h := pre p
  have hh : primeHistoryLogCoordinates (N:ℝ) 6 h=t := pre_log N p
  have hcut := (P4AOriginalSixthSquareRows.later_source_basic (action i) t ht.2.1).2.1
  have hsav : savedExponent d (N:ℝ) h=actualParent5 d (N:ℝ) h := by
    apply P1OriginalVariableFourthContinuation.finiteMax_eq_seed_of_outside
    intro j _ hj
    exact (not_le_of_gt hcut) (hh ▸ hj.2.1.2.2.2.2.1)
  have hbase : elevenExponent d (N:ℝ) h≤eval (lower i) t := by
    apply finiteMax_le _ _ _ _ _ (hsav.le.trans ho.upper)
    intro c _ hc
    rw [hh]
    exact earlier_eleven i ht hr c (hh ▸ hc.2.1)
  have hfirst : root d N p≤afterLater d (N:ℝ) h 0 :=
    ho.cap.trans (hsav.symm.le.trans (finiteMax_seed_le _ _ _ _))
  intro k hk
  refine ⟨hfirst.trans (P4AOriginalFull87DataPolicy.afterLater_mono _ _ _ (Nat.zero_le k)),?_⟩
  induction k with
  | zero => exact hbase
  | succ k ih =>
    apply finiteMax_le _ _ _ _ _ (ih (by omega))
    intro c _ hc
    rw [hh]
    exact previous_later i c ht (by rw [hc.2.1];omega) (hh ▸ hc.2.2.1)

theorem active_bounds (n : ℕ) {d : OriginalData} {N : ℕ} {p : Fin 6→ℕ} {i : Piece}
    (ht : actualPrimeTupleLog N p∈owned i) (hr : actualPrimeTupleLog N p∈regular)
    (ho : Owner d N p i) :
    ∀ k≤stage (action i),P4AOriginalLaterSixthStages.level n d (N:ℝ) (pre p) k≤eval (lower i) (actualPrimeTupleLog N p) := by
  let t := actualPrimeTupleLog N p
  let h := pre p
  have hh : primeHistoryLogCoordinates (N:ℝ) 6 h=t := pre_log N p
  have hcut := (P4AOriginalSixthSquareRows.later_source_basic (action i) t ht.2.1).2.1
  have hsave : P4AOriginalSavedSixthStage.level n d (N:ℝ) h=level5Exponent n d (N:ℝ) (rosserAncestor 5 h) :=
    P4AOriginalSavedSixthStage.inherit_if_no_source n d _ _ (fun j hj => (not_le_of_gt hcut) (hh ▸ hj.2.2.2.2.1))
  have hbase : P4AOriginalElevenSixthStage.level n d (N:ℝ) h≤eval (lower i) t := by
    rw [P4AOriginalElevenSixthStage.level,if_pos ho.active]
    apply finiteMax_le _ _ _ _ _ (hsave.le.trans (fifth_bounds n ht ho).2)
    intro c _ hc
    have hsrc : PhysicalCell c t := hh ▸ hc.1.2.1
    have hL := P4AOriginalSixthActionBank.geometric_lower_license (.eleven c) t hsrc none
    change 1/2<newCap c t at hL
    have hU := (P4AOriginalSixthActionBank.geometric_upper_license (.eleven c) t hsrc).trans (v_le_cap _)
    rw [hh]
    exact (rounded_error n _ (by linarith) hU).2.2.trans (earlier_eleven i ht hr c hsrc)
  intro k hk
  rw [P4AOriginalLaterSixthStages.level,if_pos ho.active]
  induction k with
  | zero => exact hbase
  | succ k ih =>
    apply finiteMax_le _ _ _ _ _ (ih (by omega))
    intro c _ hc
    have hsrc : Source c t := hh ▸ hc.2.1.2.2.1
    rw [hh]
    obtain ⟨hL,hU⟩ := endpoint_range c hsrc
    exact (rounded_error n _ hL hU).2.2.trans (previous_later i c ht (by rw [hc.1];omega) hsrc)

theorem eligible {d : OriginalData} {N : ℕ} {p : Fin 6→ℕ} {i : Piece} (ht : actualPrimeTupleLog N p∈owned i)
    (hr : actualPrimeTupleLog N p∈regular) (ho : Owner d N p i) :
    P4AOriginalFull87DataPolicy.ActualEligible d (N:ℝ) (pre p) (.later (action i)) := by
  let t := actualPrimeTupleLog N p
  obtain ⟨hL,hU⟩ := raw_bounds ht hr ho (stage (action i)) le_rfl
  exact ⟨pre_len p,rfl,by simpa only [pre_log] using ht.2.1,
    by rw [pre_log];exact ho.fifth.trans_le hL,
    by rw [pre_log];exact hU.trans (low_le_comparison i ht),
    by rw [pre_log];exact (P4AOriginalLaterSixthHistoryRows.source_margins (action i) t ht.2.1).2.2.2.1⟩

end
end ImbalancedChen.P4AOriginalLaterSixthPredecessor
