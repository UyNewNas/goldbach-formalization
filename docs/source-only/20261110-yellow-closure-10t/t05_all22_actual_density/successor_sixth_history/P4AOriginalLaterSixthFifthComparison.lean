import ImbalancedChen.P4AOriginalLaterSixthPriorGeometry
import ImbalancedChen.P4AOriginalElevenFifthComparison
import ImbalancedChen.P4AOriginalSavedSixthHistoricalOwner

/-! Every selected subset of the actual first five coordinates, including
those of the new fifth archive, has a literal tent side below the stated
comparison on each bought simplex. The third lookup also includes W. -/
namespace ImbalancedChen.P4AOriginalLaterSixthFifthComparison
noncomputable section
open Set VariableEnvelope
open scoped Classical BigOperators
open P2OriginalLaterSixthKernel
open P2OriginalLaterSixthArchive (Individual rowVertices)
open P2OriginalLaterSixthOwnedIntegral (inner)
open P2OriginalLaterSixthSourceIntegral (owned)
open P2OriginalSixthSimplexMoments (Point)
open P2OriginalSixthSimplexBinding (QPoint)
open P4AOriginalLaterSixthPriorGeometry (allVertices sourceIndex affine_order)
open P4AOriginalElevenFifthComparison (slots slots_complete)
open Certificates.P2OriginalSixthElevenLogSemantics (bit subsetSum R0 W)
open P4AOriginalSavedSixthHistoricalOwner (pre_log third_eq_seed root)
open P4AOriginalSavedSixthSigned (pre)
open P5OriginalCommonRefinedConstructor (OriginalData actualParent5 originalSeed exponent4 exponent5)
open P1OriginalVariableFourthContinuation (finiteMax_le)

def asc (m : ℕ) : Plane := fun j =>
  if j=0 then 1/2 else if j.val≤5 ∧ bit m (j.val-1) then 1/2 else 0
def desc (m : ℕ) : Plane := fun j =>
  if j=0 then 57/64 else if j.val≤5 ∧ bit m (j.val-1) then -3/2 else 0

theorem eval_sides (m : ℕ) (t : Point) :
    eval (asc m) t=A (subsetSum m t) ∧ eval (desc m) t=C (subsetSum m t) := by
  simp only [asc,desc,eval,A,C,subsetSum,Fin.sum_univ_succ]
  simp <;> split_ifs <;> ring

def Bound {k : ℕ} (v : Fin k→QPoint) (i : Piece) (m : Fin 32) : Prop :=
  (∀ j,evalQ (asc m.val) (v j)≤evalQ (lower i) (v j)) ∨
  (∀ j,evalQ (desc m.val) (v j)≤evalQ (lower i) (v j))
instance {k : ℕ} (v : Fin k→QPoint) (i : Piece) (m : Fin 32) : Decidable (Bound v i m) := by
  unfold Bound; infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fifth_side_check (i : Piece) (m : Fin 32) :
    Bound (allVertices i) i m ∨ ∀ s : Individual i,Bound (rowVertices i s) i m := by
  fin_cases i <;> fin_cases m <;> decide

theorem subset_tent (i : Piece) {t : Point} (ht : t∈inner i) (I : Finset (Fin 5)) :
    v (∑ j∈I,t j.castSucc)≤eval (lower i) t := by
  obtain ⟨m,hm,rfl⟩ := slots_complete I
  let u : Fin 32 := ⟨m,by have h := (Finset.mem_Icc.mp hm).2;omega⟩
  have he : (∑ j∈slots m,t j.castSucc)=subsetSum m t := by simp only [slots,Finset.sum_filter,subsetSum]
  rw [he,v_eq_min]
  obtain ⟨s,hs⟩ := mem_iUnion.mp ht
  have hb : Bound (rowVertices i s) i u := by
    rcases fifth_side_check i u with h|h
    · rcases h with h|h
      · exact Or.inl (fun j => h (sourceIndex i s j))
      · exact Or.inr (fun j => h (sourceIndex i s j))
    · exact h s
  rcases hb with h|h
  · exact (min_le_left _ _).trans (by rw [←(eval_sides m t).1];exact affine_order i s _ _ t h hs)
  · exact (min_le_right _ _).trans (by rw [←(eval_sides m t).2];exact affine_order i s _ _ t h hs)

theorem six_upper (i : Piece) {t : Point} (ht : t∈owned i) :
    six (t 0) (t 1) (t 2)≤eval (lower i) t := by
  have one := subset_tent i ht.1 ({0}:Finset (Fin 5))
  have two := subset_tent i ht.1 ({0,1}:Finset (Fin 5))
  have three := subset_tent i ht.1 ({0,1,2}:Finset (Fin 5))
  have ac := subset_tent i ht.1 ({0,2}:Finset (Fin 5))
  have bc := subset_tent i ht.1 ({1,2}:Finset (Fin 5))
  norm_num at one two three ac bc
  have hx := (P4AOriginalSixthSquareRows.later_source_basic (action i) t ht.2.1).1.le
  have hb : B (t 2)≤eval (lower i) t := by
    have hbW : B (t 2)=W t := by dsimp [B,cap,W];ring
    rw [hbW]
    have hW := (P4AOriginalLaterSixthHistoryRows.source_margins (action i) t ht.2.1).2.2.1
    have hr : R0 t=v (t 0) := by rw [v_eq_A hx];rfl
    exact (hW.le.trans_eq hr).trans one
  apply max_le one
  apply max_le two
  apply max_le (by simpa only [add_assoc] using three)
  exact max_le hb (max_le ac bc)

theorem last_tent (i : Piece) (N : ℝ) (h : List ℕ) (hl : h.length=6)
    (ht : primeHistoryLogCoordinates N 6 h∈inner i) (k : ℕ) (hk : k≤5) (I : Finset (Fin k)) :
    v (∑ j∈I,primeHistoryLogCoordinates N k (rosserAncestor k h) j)≤eval (lower i) (primeHistoryLogCoordinates N 6 h) := by
  let emb : Fin k ↪ Fin 5 := ⟨fun j => j.castLE hk,by intro j l hh;exact Fin.ext (congrArg Fin.val hh)⟩
  have he : (∑ j∈I,primeHistoryLogCoordinates N k (rosserAncestor k h) j)=
      ∑ j∈I.map emb,primeHistoryLogCoordinates N 6 h j.castSucc := by
    rw [Finset.sum_map];apply Finset.sum_congr rfl;intro j _
    exact primeHistoryLogCoordinates_ancestor N hl (by omega : k≤6) j
  rw [he]
  exact subset_tent i ht _

theorem actual_fifth (i : Piece) (d : OriginalData) (N : ℕ) (p : Fin 6→ℕ)
    (he : 0≤(d.e:ℝ)) (ht : actualPrimeTupleLog N p∈inner i)
    (hroot : root d N p≤eval (lower i) (actualPrimeTupleLog N p)) :
    actualParent5 d N (pre p)≤eval (lower i) (actualPrimeTupleLog N p) := by
  let h := pre p
  let t := actualPrimeTupleLog N p
  have hl : h.length=6 := by simp [h,pre]
  have ht' : primeHistoryLogCoordinates (N:ℝ) 6 h∈inner i := by simpa only [h,pre_log] using ht
  have bounds (k : ℕ) (hk : k≤5) (I : Finset (Fin k)) :
      v (∑ j∈I,primeHistoryLogCoordinates (N:ℝ) k (rosserAncestor k h) j)≤eval (lower i) t := by
    simpa only [h,pre_log] using last_tent i (N:ℝ) h hl ht' k hk I
  have h4len : (rosserAncestor 4 h).length=4 := by simp [hl]
  have h5len : (rosserAncestor 5 h).length=5 := by simp [hl]
  have h4 : exponent4 d N (rosserAncestor 4 h)≤eval (lower i) t := by
    rw [exponent4,if_pos h4len]
    apply finiteMax_le _ _ _ _ _ hroot
    intro r _ _
    rw [r.bufferedCandidate_eq]
    linarith only [bounds 4 (by decide) r.selected,he]
  change exponent5 d (N:ℝ) (rosserAncestor 5 h)≤_
  rw [exponent5,if_pos h5len,rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le _ _ _ _ _ h4
  intro r _ _
  rw [P1OriginalVariableFifthContinuation.candidate,P1OriginalVariableFifthContinuation.envelope_eq_v]
  linarith only [bounds 5 (by decide) r.selected,he]

end
end ImbalancedChen.P4AOriginalLaterSixthFifthComparison
