import ImbalancedChen.P2OriginalLaterSixthSourceIntegral
import ImbalancedChen.P4AOriginalSixthSquareRows

/-! The two comparison refinements enter the initial-range density
of their existing mask34 update. The earlier descending33 cap is
excluded on those subcells by its actual nonselected square at slot 4. -/
namespace ImbalancedChen.P2OriginalLaterSixthCorrections
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalLaterSixthKernel
open P2OriginalLaterSixthArchive (Individual physicalRow original_primitive)
open P2OriginalLaterSixthOwnedIntegral (inner support)
open P2OriginalLaterSixthSourceIntegral (domain owned)
open P2OriginalSixthSimplexMoments (Point)
open Certificates.P2OriginalSixthElevenLogSemantics (R0 descending33 S6 S5 eta)
open P4AOriginalSixthLaterSemantics (Source endpoint)

theorem eval_diff (a b : Plane) (t : Point) : eval (a-b) t=eval a t-eval b t := by
  simp [eval,sub_mul,Finset.sum_sub_distrib]
  <;> ring
theorem eval_x (j : Fin 6) (t : Point) : eval (xP j) t=t j := by
  fin_cases j <;> norm_num [eval,xP,Fin.sum_univ_succ]
theorem eval_total (t : Point) : eval totalP t=S6 t := by
  norm_num [eval,totalP,S6,S5,Fin.sum_univ_succ] <;> ring

theorem factor_product (i : Piece) (t : Point) :
    (∏ j,eval (factorPlane i j) t) =
    (eval (lower i) t-S6 t)*(eval (upper i) t-S6 t)*(∏ j,t j) := by
  simp [factorPlane,Fin.prod_univ_succ,eval_diff,eval_x,eval_total]
  <;> ring

theorem kernel_profile (i : Piece) (t : Point) :
    kernel i t=primeBoxInitialSavingProfile (eval (lower i) t) (eval (upper i) t) t/(∏ j,t j) := by
  rw [kernel,factor_product,gapPlane,eval_diff]
  simp only [primeBoxInitialSavingProfile,←Certificates.P2OriginalSixthElevenLogSemantics.S6_eq_sum,div_div]

theorem reciprocal (i : Piece) (t : Point) (hl : eval (lower i) t≠S6 t)
    (hu : eval (upper i) t≠S6 t) (hp : (∏ j,t j)≠0) :
    kernel i t=4*(1/(eval (lower i) t-S6 t)-1/(eval (upper i) t-S6 t))/(∏ j,t j) := by
  rw [kernel,factor_product,gapPlane,eval_diff]
  field_simp [sub_ne_zero.mpr hl,sub_ne_zero.mpr hu,hp] <;> ring

def basePiece : Fin 2→Piece := ![3,5]
def extraPiece : Fin 2→Piece := ![19,20]

private theorem endpoints (j : Fin 2) (t : Point) :
    eval (lower (basePiece j)) t=descending33 t ∧
    eval (upper (basePiece j)) t=endpoint (action (basePiece j)) t ∧
    eval (lower (extraPiece j)) t=R0 t ∧ eval (upper (extraPiece j)) t=descending33 t := by
  simp only [eval_lower,eval_upper]
  fin_cases j <;> exact ⟨rfl,rfl,rfl,rfl⟩

/-- This pointwise identity allows distinct physical triangulations
of the parent and its correction. No disjointness between them is required. -/
theorem correction_at_own_stage (j : Fin 2) (t : Point)
    (h0 : R0 t≠S6 t) (hD : descending33 t≠S6 t)
    (hM : endpoint (action (basePiece j)) t≠S6 t) (hp : (∏ k,t k)≠0) :
    kernel (basePiece j) t+kernel (extraPiece j) t =
      4*(1/(R0 t-S6 t)-1/(endpoint (action (basePiece j)) t-S6 t))/(∏ k,t k) := by
  obtain ⟨hbL,hbU,heL,heU⟩ := endpoints j t
  rw [reciprocal _ _ (hbL.symm ▸ hD) (hbU.symm ▸ hM) hp,
    reciprocal _ _ (heL.symm ▸ h0) (heU.symm ▸ hD) hp,hbL,hbU,heL,heU]
  ring

theorem correction_original_source (j : Fin 2) {t : Point} (ht : t∈domain (extraPiece j)) :
    Source (action (basePiece j)) t ∧ descending33 t<t 0+t 1+t 2+t 5+2*t 3 := by
  fin_cases j <;> exact ⟨ht.1,ht.2 rfl⟩

/-- Both of the original mask33 predecessors violate the same actual
remaining-square test. Their raw and licensed action filters must reject. -/
theorem descending33_excluded (j k : Fin 2) {t : Point} (ht : t∈domain (extraPiece j)) :
    ¬Source (action (if k=0 then (0:Piece) else 1)) t := by
  intro hs
  let c := action (if k=0 then (0:Piece) else 1)
  have hm : (3:Fin 6)∉P4AOriginalSixthSquareRows.slots (P4AOriginalSixthLaterLiteral.mask c) := by
    fin_cases k <;> decide
  have hr := (P4AOriginalSixthSquareRows.later_source_squares c t hs).2 3 hm
  rw [P4AOriginalSixthSquareRows.remaining_dictionary] at hr
  have hsq : Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare (P4AOriginalSixthLaterLiteral.mask c) 3 t =
      t 0+t 1+t 2+t 5+2*t 3 := by
    fin_cases k <;> norm_num [c,action,P4AOriginalSixthLaterLiteral.mask,
      Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare,
      Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit,Fin.sum_univ_succ] <;> ring
  have hep : endpoint c t=descending33 t-eta := by
    fin_cases k <;> norm_num [c,action,endpoint,P4AOriginalSixthLaterLiteral.descending,
      P4AOriginalSixthLaterSemantics.selectedSum,P4AOriginalSixthLaterLiteral.mask,
      Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit,descending33,Fin.sum_univ_succ] <;> ring
  rw [hsq,hep] at hr
  have hf := (correction_original_source j ht).2
  linarith only [hr,hf,show 0<eta by norm_num [eta]]

end
end ImbalancedChen.P2OriginalLaterSixthCorrections
