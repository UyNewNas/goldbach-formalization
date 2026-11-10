import ImbalancedChen.P4AOriginalLaterSixthOccurrence

/-! At a fixed chronological update there is at most one bought cap
action. Its ordinary and comparison-correction tests may coexist.
Their two reciprocal differences add exactly to the original full
comparison window, even if their triangulations differ. -/
namespace ImbalancedChen.P2OriginalLaterSixthJointTests
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalLaterSixthKernel (Piece action correction eval lower upper eval_lower eval_upper)
open P2OriginalLaterSixthArchive (bank Individual sx vertex original_primitive)
open P2OriginalLaterSixthOwnedIntegral (nonpos_on)
open P2OriginalLaterSixthStageMass (epoch)
open P2OriginalLaterSixthSourceIntegral (owned separates gate_domain)
open P2OriginalLaterSixthInnerTests (trim trim_region test test_bounds test_off_trim profile inner_factors)
open P2OriginalLaterSixthCorrections (basePiece extraPiece)
open P4AOriginalSixthLaterSemantics (comparison endpoint)
open P4AOriginalFull87HistoryCore (width width_pos)
open P2OriginalSixthSimplexMoments (Point)
open Certificates.P2OriginalSixthElevenLogSemantics (S6 descending33 R0)
open P2OriginalSixthMomentRow (cutoff)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cross_separation (i j : Piece) :
    epoch i=epoch j → action i≠action j → separates i j ∨ separates j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem sep (i j : Piece) (hs : separates i j) {t : Point} (hi : t∈owned i) (hj : t∈owned j) : False := by
  obtain ⟨a,ha,hv⟩ := hs
  obtain ⟨s,hs⟩ := mem_iUnion.mp hj.1
  exact ((gate_domain i t).mp hi.2 a ha).not_ge
    (nonpos_on j s a (fun k=>hv ⟨(sx j s).ids.getD k.val 0,(original_primitive j s).idsWithin k⟩) hs)

theorem unique_action {i j : Piece} (hij : epoch i=epoch j) {t : Point} (hi : t∈owned i) (hj : t∈owned j) :
    action i=action j := by
  by_contra hn
  rcases cross_separation i j hij hn with h|h
  · exact sep i j h hi hj
  · exact sep j i h hj hi

def value (R M : ℝ) (t : Point) : ℝ := 4/(R-S6 t)-4/(M-S6 t)
theorem profile_of_bounds (i : Piece) {t : Point} (hL : cutoff≤eval (lower i) t-S6 t)
    (hLU : eval (lower i) t≤eval (upper i) t) : profile i t=value (eval (lower i) t) (eval (upper i) t) t := by
  have hU := hL.trans (sub_le_sub_right hLU _)
  have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4)
    ((by norm_num [cutoff] : (0:ℝ)<cutoff).trans_le hL) (sub_le_sub_right hLU _)
  simp only [profile,value,max_eq_right hL,max_eq_right hU,max_eq_right (sub_nonneg.mpr hh)]

theorem ordinary {i : Piece} (hi : correction i=false) {t : Point} (ht : t∈owned i) (r : ℕ) :
    test r i t≤value (eval (lower i) t) (endpoint (action i) t) t := by
  have h := inner_factors i ht.1
  have he := profile_of_bounds i h.1 h.2.2
  rw [eval_upper,hi] at he
  simpa only [Bool.false_eq_true,if_false] using (test_bounds r i t).2.trans_eq he

theorem pair (r : ℕ) (j : Fin 2) {t : Point} (ht : t∈owned (extraPiece j)) :
    test r (basePiece j) t+test r (extraPiece j) t≤
    value (eval (lower (extraPiece j)) t) (endpoint (action (extraPiece j)) t) t := by
  let b := basePiece j
  let x := extraPiece j
  have hb : eval (lower b) t=descending33 t ∧ eval (upper b) t=endpoint (action x) t ∧
      eval (lower x) t=R0 t ∧ eval (upper x) t=descending33 t ∧ comparison (action x) t=descending33 t := by
    simp only [eval_lower,eval_upper]
    fin_cases j <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨bL,bU,xL,xU,cD⟩ := hb
  have hx := inner_factors x ht.1
  have hD := hx.2.1
  rw [xU] at hD
  have hE := (P4AOriginalLaterSixthHistoryRows.source_margins (action x) t ht.2.1).2.2.2.1
  rw [cD] at hE
  have hb' := profile_of_bounds b (bL.symm ▸ hD) (by rw [bL,bU];exact hE.le)
  have hx' := profile_of_bounds x hx.1 hx.2.2
  have hsum := add_le_add (test_bounds r b t).2 (test_bounds r x t).2
  rw [hb',hx',bL,bU,xU] at hsum
  dsimp only [value] at hsum ⊢
  linarith only [hsum]

def sum (r : ℕ) (k : Fin 8) (t : Point) := ∑ i∈Finset.univ.filter (fun i=>epoch i=k),test r i t

theorem charge {r : ℕ} {k : Fin 8} {t : Point} (live : ∃ i : Piece,epoch i=k ∧ t∈trim i (width r)) :
    ∃ i : Piece,epoch i=k ∧ t∈trim i (width r) ∧
      sum r k t≤value (eval (lower i) t) (endpoint (action i) t) t := by
  let F := Finset.univ.filter (fun i : Piece=>epoch i=k ∧ t∈trim i (width r))
  have mem (i : Piece) : i∈F ↔ epoch i=k ∧ t∈trim i (width r) := by simp [F]
  have hrestrict : sum r k t=∑ i∈F,test r i t := by
    apply (Finset.sum_subset (fun i hi=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,((mem i).mp hi).1⟩) ?_).symm
    intro i hi hn
    exact test_off_trim r i (fun ht=>hn ((mem i).mpr ⟨(Finset.mem_filter.mp hi).2,ht⟩))
  by_cases he : ∃ j : Fin 2,extraPiece j∈F
  · obtain ⟨j,hj⟩ := he
    have hx := (mem _).mp hj
    refine ⟨extraPiece j,hx.1,hx.2,?_⟩
    rw [hrestrict]
    have hsub : F⊆{basePiece j,extraPiece j} := by
      intro i hi
      have hv := (mem i).mp hi
      have ha := unique_action (hv.1.trans hx.1.symm) (trim_region (width_pos r) hv.2).1 (trim_region (width_pos r) hx.2).1
      have hf : ∀ (j : Fin 2) (i : Piece),action i=action (extraPiece j) → i=basePiece j ∨ i=extraPiece j := by decide
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hf j i ha
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _=>(test_bounds r i t).1)
    have hne : basePiece j≠extraPiece j := by fin_cases j <;> decide
    have htwo : (∑ i∈({basePiece j,extraPiece j} : Finset Piece),test r i t)=
        test r (basePiece j) t+test r (extraPiece j) t := by rw [Finset.sum_pair hne]
    exact (hsum.trans_eq htwo).trans (pair r j (trim_region (width_pos r) hx.2).1)
  · obtain ⟨i,hi,ht⟩ := live
    refine ⟨i,hi,ht,?_⟩
    have hif : i∈F := (mem i).mpr ⟨hi,ht⟩
    have hreg (l : Piece) (hl : l∈F) : correction l=false := by
      by_contra hn
      have h : ∃ j : Fin 2,l=extraPiece j := by
        have h' : ∀ l : Piece,correction l≠false → ∃ j : Fin 2,l=extraPiece j := by decide
        exact h' l hn
      obtain ⟨j,rfl⟩ := h
      exact he ⟨j,hl⟩
    have hF : F={i} := by
      ext l
      refine ⟨fun hl=>?_,fun hh=>by simpa only [Finset.mem_singleton.mp hh] using hif⟩
      have hh := (mem l).mp hl
      have ha := unique_action (hh.1.trans hi.symm) (trim_region (width_pos r) hh.2).1 (trim_region (width_pos r) ht).1
      have hf : ∀ l i : Piece,action l=action i → correction l=false → correction i=false → l=i := by decide
      exact Finset.mem_singleton.mpr (hf l i ha (hreg l hl) (hreg i hif))
    rw [hrestrict,hF,Finset.sum_singleton]
    exact ordinary (hreg i hif) (trim_region (width_pos r) ht).1 r

theorem zero_of_no_live {r : ℕ} {k : Fin 8} {t : Point} (hn : ¬∃ i : Piece,epoch i=k ∧ t∈trim i (width r)) :
    sum r k t=0 := Finset.sum_eq_zero (fun i hi=>test_off_trim r i (fun ht=>hn ⟨i,(Finset.mem_filter.mp hi).2,ht⟩))

end
end ImbalancedChen.P2OriginalLaterSixthJointTests
