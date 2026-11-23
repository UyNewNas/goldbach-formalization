import ImbalancedChen.P2WuJointWindowTheta

/-! The original W1 switched count at (3,16/5), with the complete-product
trim and both endpoints of every prefix window on the very same tuple.
One threshold serves both the prime test and the unsifted comparison. -/

namespace ImbalancedChen.P2WuJointWindowOriginalCount
noncomputable section
open Finset Filter Wu2008DoubleSieve
open P2NativeOmega3RankTupleReceiver
open P2WuProductInnerProfile P2WuProductInnerThetaPayment
open P2WuJointWindowCarrier P2WuJointWindowTheta
open P5Z.ActualSingletonLogCollarFamily
open scoped Classical BigOperators

theorem original_count_with_all_prefix_windows (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ R T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
      let B := collarExponent k
      let w := logWidth B N
      let θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2)
      (wuOmega3Sum N δ 3 (16/5) (convolutionWuWindows N b.2.1 b.2.2) ≤
        (∑ r ∈ range (R+1), p5z_labelledPrimeMass (carrier δ r N b.1) Part3.labelledProduct
          (fun u => innerWeight B N u * jointWeight δ w r N b u) N)+ε*θ) ∧
      (∑ r ∈ range (R+1), ∑ u ∈ Part3.labelledPrimeTuples r N,
        |innerWeight B N u*jointWeight δ w r N b u-indexedWeight k δ r N b u|) ≤ ε*θ := by
  obtain ⟨R,Tp,h4,hp⟩ := uniform_original_with_product_inner_cut k hδ hδhi hε
  obtain ⟨Tb,_,hbounds⟩ := uniform_joint_prefix_error k R hδ hδhi hε
  obtain ⟨Tw,hw⟩ := eventually_atTop.mp (eventually_both_widths k (collarExponent k) hδ)
  refine ⟨R, max Tp (max Tb Tw), h4.trans (le_max_left _ _), ?_⟩
  intro N hN he b hb
  have hNp := (le_max_left Tp (max Tb Tw)).trans hN
  have hNbw := (le_max_right Tp (max Tb Tw)).trans hN
  have hNb := (le_max_left Tb Tw).trans hNbw
  have hNw := (le_max_right Tb Tw).trans hNbw
  have hN4 := h4.trans hNp
  let B := collarExponent k
  let w := logWidth B N
  have hwpos : 0 < w := (logWidth_bounds B (by omega : 2 ≤ N)).1
  have hends := hw N hNw b hb
  have row (r : ℕ) :
      p5z_labelledPrimeMass (indexedFamily k δ r N b) Part3.labelledProduct (innerWeight B N) N ≤
        p5z_labelledPrimeMass (carrier δ r N b.1) Part3.labelledProduct
          (fun u => innerWeight B N u * jointWeight δ w r N b u) N := by
    let S := indexedFamily k δ r N b
    calc
      _ = p5z_labelledPrimeMass S Part3.labelledProduct
            (fun u => innerWeight B N u * jointWeight δ w r N b u) N := by
        apply sum_congr rfl
        intro u hu
        rw [jointWeight_one hb hwpos (fun j => (hends j).1) (fun j => (hends j).2.1) hu,
          mul_one]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (indexed_subset_carrier hb)
        intro u _ _
        split_ifs
        · exact mul_nonneg (innerWeight_bounds B N u).1 (jointWeight_bounds δ w r N b u).1
        · exact le_rfl
  have hm := sum_le_sum (s := range (R+1)) (fun r _ => row r)
  exact ⟨(hp N hNp he b hb).trans (add_le_add hm le_rfl), (hbounds N hNb b hb).2.2⟩

end
end ImbalancedChen.P2WuJointWindowOriginalCount
