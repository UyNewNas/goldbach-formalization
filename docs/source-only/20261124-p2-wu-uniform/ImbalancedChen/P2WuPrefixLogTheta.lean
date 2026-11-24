import ImbalancedChen.P2WuPrefixLogProfile
import ImbalancedChen.P2WuJointWindowTheta

/-!
The new quantitatively controlled logarithmic prefix profile is attached to
the actual W1 (3,16/5) carrier. Its leakage is dominated by the already
priced physical prefix profile, so the same native moving-box Theta scale
and all original convolution multiplicities are retained.

This does not smooth the carrier's other walls or remove its coprimality
filter, and it asserts no signed PP supplier. It is not the complete
bad-Gamma5 plus Gamma9--21 seed family.
SOURCE ONLY: not compiled and no kernel credit until separately replayed.
-/
namespace ImbalancedChen.P2WuPrefixLogTheta

noncomputable section
open Finset Filter Wu2008DoubleSieve
open P2NativeOmega3RankTupleReceiver
open P2WuJointWindowCarrier P2WuJointWindowTheta
open P2WuProductInnerProfile P2WuProductInnerThetaPayment
open P2WuPrefixLogProfile
open P5Z.ActualSingletonLogCollarFamily
open scoped Classical BigOperators

def jointLogWeight (δ w : ℝ) (r N : ℕ) (b : BoxIndex)
    (u : Fin r → Fin (N+1)) : ℝ :=
  p5z_markedPhysicalWeight (carrier δ r N b.1) (fun v =>
    if hr : b.1≤r then physicalProfile (lower b) b.2.2 w (Fin.castLE hr) (physical v)
    else 0) u

theorem jointLogWeight_bounds (δ w : ℝ) (r N : ℕ) (b : BoxIndex)
    (u : Fin r → Fin (N+1)) :
    0≤jointLogWeight δ w r N b u ∧ jointLogWeight δ w r N b u≤1 := by
  unfold jointLogWeight p5z_markedPhysicalWeight
  split_ifs
  · exact physicalProfile_bounds _ _ _ _ _
  all_goals norm_num

theorem jointLogWeight_one {k r N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (hw : 0<w)
    (hL : ∀ j,0<lower b j) {u : Fin r → Fin (N+1)}
    (hu : u∈indexedFamily k δ r N b) : jointLogWeight δ w r N b u=1 := by
  have hcar := indexed_subset_carrier hb hu
  have hfit := prefix_fits hcar
  have hin := (indexed_iff_prefix hb hfit hcar).mp hu
  simp only [jointLogWeight,p5z_markedPhysicalWeight,if_pos hcar,dif_pos hfit]
  exact physicalProfile_one hL hw (fun j => ⟨(hin j).1,(hin j).2.le⟩)

theorem jointLogWeight_le {r N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hw : 0<w) (hL : ∀ j,0<lower b j) (hV : ∀ j,0<b.2.2 j)
    {u : Fin r → Fin (N+1)} (hu : u∈Part3.labelledPrimeTuples r N) :
    jointLogWeight δ w r N b u≤jointWeight δ w r N b u := by
  have hp : ∀ l,0<physical u l := by
    intro l
    exact_mod_cast ((mem_filter.mp hu).2 l).pos
  by_cases hcar : u∈carrier δ r N b.1
  · by_cases hfit : b.1≤r
    · simp only [jointLogWeight,jointWeight,p5z_markedPhysicalWeight,if_pos hcar,dif_pos hfit]
      exact physicalProfile_le_original hL hV hw (fun j => hp (Fin.castLE hfit j))
    · simp only [jointLogWeight,jointWeight,p5z_markedPhysicalWeight,if_pos hcar,dif_neg hfit]
  · simp only [jointLogWeight,jointWeight,p5z_markedPhysicalWeight,if_neg hcar]

theorem log_prefix_error_le_original {k r B N : ℕ} {δ w : ℝ} {b : BoxIndex}
    (hb : wuSourceBox k δ N b.1 b.2.1 b.2.2) (hw : 0<w)
    (hL : ∀ j,0<lower b j) (hV : ∀ j,0<b.2.2 j)
    {u : Fin r → Fin (N+1)} (hu : u∈Part3.labelledPrimeTuples r N) :
    |innerWeight B N u*jointLogWeight δ w r N b u-indexedWeight k δ r N b u|≤
      |innerWeight B N u*jointWeight δ w r N b u-indexedWeight k δ r N b u| := by
  by_cases hin : u∈indexedFamily k δ r N b
  · rw [jointLogWeight_one hb hw hL hin,jointWeight_one hb hw hL hV hin]
  · have hz : indexedWeight k δ r N b u=0 := by
      simp only [indexedWeight,p5z_markedPhysicalWeight,if_neg hin]
    rw [hz,sub_zero,sub_zero,
      abs_of_nonneg (mul_nonneg (innerWeight_bounds B N u).1 (jointLogWeight_bounds _ _ _ _ _ _).1),
      abs_of_nonneg (mul_nonneg (innerWeight_bounds B N u).1 (jointWeight_bounds _ _ _ _ _ _).1)]
    exact mul_le_mul_of_nonneg_left (jointLogWeight_le hw hL hV hu) (innerWeight_bounds B N u).1

/-- Reuse the existing native-box lower bound and entire prefix-collar
payment by pointwise domination. No extra analytic estimate is requested. -/
theorem uniform_log_prefix_error (k R : ℕ) {δ ε : ℝ}
    (hδ : 0<δ) (hδhi : δ≤1/10) (hε : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N →
      ∀ b : BoxIndex,wuSourceBox k δ N b.1 b.2.1 b.2.2 →
      let B := collarExponent k
      let w := logWidth B N
      let X := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2)
      (∀ r : ℕ,(∑ u∈indexedFamily k δ r N b,
        innerWeight B N u*(1-jointLogWeight δ w r N b u))=0) ∧
      (∑ r∈range (R+1),∑ u∈Part3.labelledPrimeTuples r N\indexedFamily k δ r N b,
        innerWeight B N u*jointLogWeight δ w r N b u)≤(ε/2)*X ∧
      (∑ r∈range (R+1),∑ u∈Part3.labelledPrimeTuples r N,
        |innerWeight B N u*jointLogWeight δ w r N b u-indexedWeight k δ r N b u|)≤ε*X := by
  obtain ⟨Ta,h4,ha⟩ := uniform_joint_prefix_error k R hδ hδhi hε
  obtain ⟨Tb,hb⟩ := eventually_atTop.mp (eventually_both_widths k (collarExponent k) hδ)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN b hbox
  have hNa := (le_max_left Ta Tb).trans hN
  have hNb := (le_max_right Ta Tb).trans hN
  have hN4 := h4.trans hNa
  let B := collarExponent k
  let w := logWidth B N
  have hw : 0<w := (logWidth_bounds B (by omega : 2≤N)).1
  have hends := hb N hNb b hbox
  have hL := fun j => (hends j).1
  have hV := fun j => (hends j).2.1
  have H := ha N hNa b hbox
  refine ⟨?_,?_,?_⟩
  · intro r
    apply sum_eq_zero
    intro u hu
    rw [jointLogWeight_one hbox hw hL hu,sub_self,mul_zero]
  · apply le_trans ?_ H.2.1
    apply sum_le_sum
    intro r _
    apply sum_le_sum
    intro u hu
    exact mul_le_mul_of_nonneg_left
      (jointLogWeight_le hw hL hV (mem_sdiff.mp hu).1) (innerWeight_bounds B N u).1
  · apply le_trans ?_ H.2.2
    apply sum_le_sum
    intro r _
    exact sum_le_sum (fun u hu => log_prefix_error_le_original hbox hw hL hV hu)

/-- The original additive-prime test is retained on the same full labelled
word and the same carrier. Both conclusions use the actual new prefix
profile whose mixed log-chart bound is proved in the companion module. -/
theorem original_count_with_log_prefix_windows (k : ℕ) {δ ε : ℝ}
    (hδ : 0<δ) (hδhi : δ≤1/10) (hε : 0<ε) :
    ∃ R T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N →
      ∀ b : BoxIndex,wuSourceBox k δ N b.1 b.2.1 b.2.2 →
      let B := collarExponent k
      let w := logWidth B N
      let θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2)
      (wuOmega3Sum N δ 3 (16/5) (convolutionWuWindows N b.2.1 b.2.2)≤
        (∑ r∈range (R+1),p5z_labelledPrimeMass (carrier δ r N b.1) Part3.labelledProduct
          (fun u => innerWeight B N u*jointLogWeight δ w r N b u) N)+ε*θ) ∧
      (∑ r∈range (R+1),∑ u∈Part3.labelledPrimeTuples r N,
        |innerWeight B N u*jointLogWeight δ w r N b u-indexedWeight k δ r N b u|)≤ε*θ := by
  obtain ⟨R,Tp,h4,hp⟩ := uniform_original_with_product_inner_cut k hδ hδhi hε
  obtain ⟨Te,_,he⟩ := uniform_log_prefix_error k R hδ hδhi hε
  obtain ⟨Tw,hw⟩ := eventually_atTop.mp (eventually_both_widths k (collarExponent k) hδ)
  refine ⟨R,max Tp (max Te Tw),h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven b hb
  have hNp := (le_max_left Tp (max Te Tw)).trans hN
  have hNew := (le_max_right Tp (max Te Tw)).trans hN
  have hNe := (le_max_left Te Tw).trans hNew
  have hNw := (le_max_right Te Tw).trans hNew
  have hN4 := h4.trans hNp
  let B := collarExponent k
  let w := logWidth B N
  have hwpos : 0<w := (logWidth_bounds B (by omega : 2≤N)).1
  have hends := hw N hNw b hb
  have row (r : ℕ) :
      p5z_labelledPrimeMass (indexedFamily k δ r N b) Part3.labelledProduct (innerWeight B N) N≤
        p5z_labelledPrimeMass (carrier δ r N b.1) Part3.labelledProduct
          (fun u => innerWeight B N u*jointLogWeight δ w r N b u) N := by
    let S := indexedFamily k δ r N b
    calc
      _ = p5z_labelledPrimeMass S Part3.labelledProduct
          (fun u => innerWeight B N u*jointLogWeight δ w r N b u) N := by
        apply sum_congr rfl
        intro u hu
        rw [jointLogWeight_one hb hwpos (fun j => (hends j).1) hu,mul_one]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (indexed_subset_carrier hb)
        intro u _ _
        split_ifs
        · exact mul_nonneg (innerWeight_bounds B N u).1 (jointLogWeight_bounds _ _ _ _ _ _).1
        · exact le_rfl
  have hm := sum_le_sum (s:=range (R+1)) (fun r _ => row r)
  exact ⟨(hp N hNp hEven b hb).trans (add_le_add hm le_rfl),(he N hNe b hb).2.2⟩

end
end ImbalancedChen.P2WuPrefixLogTheta
