import ImbalancedChen.P4BOriginalTwoLongMotherPayment

/-! SOURCE ONLY / UNCOMPILED. Source identity for the filtered row used
in the paid bank. It is the original typeIValue on the two actual HB Row
records, with the original psi, group logs, rough weights and upperTest.
No new source-equality or whole-bank predicate is supplied as a premise. -/
namespace ImbalancedChen.P4BOriginalTwoLongSourceRow
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalNoMediumPairRows (noMedium typeI_pair_selector)
open P4BOriginalTwoLongRetainedRows (originalBranchRow)
open P4BOriginalHighRankPostModulusRow (original)
open P4BUpperPairOrderedRowGeometry (rowRoles)
open P4BUpperPairOrderedRowModes (rowAtom upperTest pair_row_reindex)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ActualRoughHeathBrownWords (roughTupleWeight roles)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.PerGroupIntegerHBAtlasPushforward (Row hbCutoff typeIValue)
open P5Z.ExactOriginalSmoothDyadicPartition (R psi)
open P5Z.ActualHBMediumBranchPartition (originalLower originalUpper)
open P4BOuterRampRoughness (baseline)

theorem originalBranchRow_eq_typeI (zeta : ℝ) {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N : ℕ) (kap0 : ℝ) (cj ck j l : ℕ)
    (bs : Fin (2*(j+1))→Block) (cs : Fin (2*(l+1))→Block)
    (Z : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) :
    originalBranchRow (u:=2*(j+1)) (v:=2*(l+1)) zeta b kap s N kap0 cj ck (Fin.append bs cs) Z
      (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) S c=
    ∑ u∈rectangle bs,∑ v∈rectangle cs,
      roughTupleWeight Z (hbCutoff cj) (roles j) (List.ofFn u)*
      roughTupleWeight Z (hbCutoff ck) (roles l) (List.ofFn v)*
      (psi P5Z.ActualEtaPsiOccurrenceBudget.chi ((completeProduct u:ℝ)/R cj)*
       psi P5Z.ActualEtaPsiOccurrenceBudget.chi ((completeProduct v:ℝ)/R ck)*
       typeIValue (originalLower (R cj*R ck) zeta) (originalUpper (R cj*R ck) zeta)
         (upperTest hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs
           (by simpa only [one_mul] using hg) N kap0 S (fun d => (c d:ℂ)))
         [{order:=j,blocks:=List.ofFn bs,factors:=List.ofFn u},
          {order:=l,blocks:=List.ofFn cs,factors:=List.ofFn v}]) := by
  simp_rw [typeI_pair_selector]
  by_cases hn : noMedium zeta cj ck (Fin.append bs cs)
  · have hn' : P5Z.ActualHBMediumBranchPartition.firstMedium
        (originalLower (R cj*R ck) zeta) (originalUpper (R cj*R ck) zeta)
        (List.ofFn (Fin.append bs cs))=none := hn
    simp only [originalBranchRow,if_pos hn,if_pos hn']
    exact (pair_row_reindex hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs
      (by simpa only [one_mul] using hg) N kap0 cj ck j l bs cs Z S (fun d => (c d:ℂ))).symm
  · have hn' : ¬P5Z.ActualHBMediumBranchPartition.firstMedium
        (originalLower (R cj*R ck) zeta) (originalUpper (R cj*R ck) zeta)
        (List.ofFn (Fin.append bs cs))=none := hn
    simp only [originalBranchRow,if_neg hn,if_neg hn',mul_zero,Finset.sum_const_zero]

end
end ImbalancedChen.P4BOriginalTwoLongSourceRow
