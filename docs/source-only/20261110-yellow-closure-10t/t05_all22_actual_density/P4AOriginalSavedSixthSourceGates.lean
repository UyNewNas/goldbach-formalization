import ImbalancedChen.P4AOriginalSavedSixthPrimeMean
import ImbalancedChen.P4AOriginalSavedSixthStage
import ImbalancedChen.P4AOriginalSixthQuantizedActionLicense

/-! The six original old-third components and the saved row's quantized
full/selected square bounds on the entire physical Ico rectangle. -/
namespace ImbalancedChen.P4AOriginalSavedSixthSourceGates
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P4AOriginalSavedSixthPlanes P4AOriginalSavedSixthBank
open P4AOriginalSavedSixthIntegral
open P4AOriginalSavedSixthPrimeMean (ordered6 bounds)
open P4AOriginalSavedSixthArchive (Row endpoint oldUpper selectedMask)
open P4AOriginalFull87HistoryCore (width)

@[simp] theorem mask_eq (i : Row) : chosenMask i = selectedMask i := by
  simp only [chosenMask,selectedMask,P4AOriginalSavedSixthWordAccess.word_eq]
@[simp] theorem slots_eq (m : ℕ) : slots 6 m = P4AOriginalSixthSquareRows.slots m := by
  ext j; simp [slots,P4AOriginalSixthSquareRows.slots, j.isLt]
@[simp] theorem eval_h3 (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : h3.eval t=Certificates.P2OriginalSixthElevenLogSemantics.H3 t := by simp [h3,Certificates.P2OriginalSixthElevenLogSemantics.H3]
@[simp] theorem eval_h5 (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : h5.eval t=Certificates.P2OriginalSixthElevenLogSemantics.H5 t := by simp [h5,Certificates.P2OriginalSixthElevenLogSemantics.H5]
@[simp] theorem eval_full (j : Fin 6) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) : (full j).eval t = Certificates.P2OriginalSixthElevenLogSemantics.fullSquare j t := by
  simp [full,prefix,Plane.eval,Certificates.P2OriginalSixthElevenLogSemantics.fullSquare,ite_mul]
@[simp] theorem eval_remaining (m : ℕ) (j : Fin 6) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) :
    (remaining m j).eval t=Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare m j t := by
  simp [remaining,prefixUnmarked,Plane.eval,Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare,eval_selected,
    P4AOriginalSixthSquareRows.sum_slots,slots_eq,P4AOriginalSixthSquareRows.not_mem_slots,ite_mul]

theorem one_component (j : Fin 6) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) :
    min ((thirdFace j false).eval t) ((thirdFace j true).eval t) ≤ six (t 0) (t 1) (t 2) := by
  have hW : Certificates.P2OriginalSixthElevenLogSemantics.W t = B (t 2) := by unfold Certificates.P2OriginalSixthElevenLogSemantics.W B cap; ring
  have htern (m : ℕ) : min ((tentPlane 5 m false).eval t) ((tentPlane 5 m true).eval t) =
      v (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum m t) := by simp [sum_five,v_eq_min]
  by_cases hj : j.val=0
  · simp [thirdFace,hj,hW,six,le_max_iff]
  · simp only [thirdFace,if_neg hj,htern]
    fin_cases j <;> norm_num [thirdMask,Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,Certificates.P2OriginalSixthElevenLogSemantics.bit,
      Fin.sum_univ_succ,six,le_max_iff,add_assoc] at hj ⊢

private theorem old_margin (i : Row) (p : Plane) {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical} (ht : t∈box i)
    (h : ∃ j : Fin 6,∀ b : Bool,above i (thirdFace j b) p (1/1600)) :
    p.eval t+1/1600 ≤ six (t 0) (t 1) (t 2) := by
  obtain ⟨j,hj⟩ := h
  exact (le_min (by simpa using above_at i _ _ _ (hj false) ht)
    (by simpa using above_at i _ _ _ (hj true) ht)).trans (one_component j t)
theorem old_margins (i : Row) {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical} (ht : t∈box i) :
    Certificates.P2OriginalSixthElevenLogSemantics.H3 t+1/1600 ≤ six (t 0) (t 1) (t 2) ∧ Certificates.P2OriginalSixthElevenLogSemantics.H5 t+1/1600 ≤ six (t 0) (t 1) (t 2) := by
  exact ⟨by simpa using old_margin i h3 ht (facts i).third,
    by simpa using old_margin i h5 ht (facts i).fifth⟩

private theorem le_both (i : Row) (p : Plane) {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical} (ht : t∈box i)
    (h : ∀ b : Bool,above i (newFace i b) p (1/1600)) :
    p.eval t + 1/1600 ≤ endpoint i t := by
  rw [← new_min]
  exact le_min (by simpa using above_at i _ _ _ (h false) ht)
    (by simpa using above_at i _ _ _ (h true) ht)

theorem square_margins (i : Row) {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical} (ht : t∈box i) :
    (1/2:ℝ)+1/1600 ≤ endpoint i t ∧
    (∀ j,Certificates.P2OriginalSixthElevenLogSemantics.fullSquare j t+1/1600 ≤ endpoint i t) ∧
    ∀ j,Certificates.P2OriginalSixthElevenLogSemantics.bit (selectedMask i) j.val=false → Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare (selectedMask i) j t+1/1600 ≤ endpoint i t := by
  refine ⟨by simpa using le_both i _ ht (facts i).half,?_,?_⟩
  · intro j; simpa using le_both i _ ht (fun b => (facts i).fullGate b j)
  · intro j hj
    have hm : j ∉ slots 6 (chosenMask i) := by simp [P4AOriginalSixthSquareRows.not_mem_slots,hj]
    simpa using le_both i _ ht (fun b => (facts i).remainingGate b j hm)

theorem source_iff (i : Row) (t : Certificates.P2OriginalSixthElevenLogSemantics.Physical) :
    P4AOriginalSavedSixthArchive.Source i t ↔ t∈box i ∧ oldUpper i t < endpoint i t := by
  have hc := corners_match i (grid i)
  have hbox : P4AOriginalSavedSixthArchive.InBox i t ↔ t∈box i := by
    rw [P4AOriginalSavedSixthArchive.InBox,box,mem_logPrimeBox,hc.1,hc.2]
  constructor
  · exact fun h => ⟨hbox.mp h.2.1,h.2.2.2.2.2.2.2.2⟩
  · rintro ⟨ht,hg⟩
    have hh := square_margins i ht
    have hm := (facts i).mask
    rw [mask_eq] at hm
    exact ⟨by simp [P4AOriginalSavedSixthArchive.denominator,grid],hbox.mpr ht,hm.1,hm.2,
      (bounds i ht 5).1,fun j => by linarith only [hh.2.1 j],
      fun j hj => by linarith only [hh.2.2 j hj],(residual_ceiling i ht).2.2,hg⟩

theorem quantized_all_gates (i : Row) {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical} (ht : t∈box i)
    (n : ℕ) (hn : 4*width n < 1/1600) :
    P1QuantizedActionLicense.LowerLicense (P4AOriginalSixthSquareRows.slots (selectedMask i)) t (P1GuardFrozenFiniteCapAlgebra.rounded n (endpoint i t):ℝ) ∧
    (P1GuardFrozenFiniteCapAlgebra.rounded n (endpoint i t):ℝ)+width n ≤
      v (∑ j ∈ P4AOriginalSixthSquareRows.slots (selectedMask i),t j) := by
  have hh := square_margins i ht
  have hgate (g : P1QuantizedActionLicense.Gate 6) : P1QuantizedActionLicense.gate (P4AOriginalSixthSquareRows.slots (selectedMask i)) t g+1/1600 ≤ endpoint i t := by
    rcases g with _ | ⟨b,j⟩
    · exact hh.1
    · cases b with
      | false => simpa only [P1QuantizedActionLicense.gate,P4AOriginalSixthSquareRows.full_dictionary] using hh.2.1 j
      | true =>
        by_cases h : j ∈ P4AOriginalSixthSquareRows.slots (selectedMask i)
        · simpa [P1QuantizedActionLicense.gate,h] using hh.1
        · simpa [P1QuantizedActionLicense.gate,h,P4AOriginalSixthSquareRows.remaining_dictionary] using hh.2.2 j ((P4AOriginalSixthSquareRows.not_mem_slots _ _).mp h)
  have h := P1QuantizedActionLicense.rounded_licensed n (P4AOriginalSixthSquareRows.slots (selectedMask i)) t (endpoint i t) (1/1600)
    (by norm_num) (v_le_cap _) hgate hn
  exact ⟨fun g => by linarith only [h.1 g],by simpa only [P4AOriginalSixthSquareRows.sum_slots] using h.2⟩

end
end ImbalancedChen.P4AOriginalSavedSixthSourceGates
