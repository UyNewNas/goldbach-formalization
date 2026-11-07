import ImbalancedChen.P5ZU1011OriginalFifteenJointSelectedSupport

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual natural three-factor completion for original15 near-cap JOINT rows.
The middle is the true bit-selected product when its remaining capacity
is at least one. Otherwise the actual deterministic two-capacity allocator
is rerun on ALL original specified primes and the actual residual vector;
the final middle may change and the third factor is one. Support is proved
from the nonzero native coefficient, never supplied as an allocation premise.
The existing generic allocator and full-vector repair are reused unchanged.
This is finite completion; kappa/beta monomial and analytic licenses remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenJointSelectedCompletion
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalSixteenInteriorArithmetic P5U1011JointOverlap
open U1011OriginalSixteenNearCapBoxProfiles (nu delta Tplus)
open U1011OriginalSixteenJointNearCapCompiler (rowD rowCoefficient)
open U1011OriginalFifteenJointSelectedSupport
open U1011OriginalW16AttachedWellSupport (specified specified_product)

def fullVector (t : Four) (d : ℕ) : List ℕ := specified t++residualPrimes d
def selectedVector (p : Policy) (t : Four) (d : ℕ) : List ℕ := remainderPrimes p t++residualPrimes d

theorem fullVector_product {N d : ℕ} (p : Policy) (B : Box) (eta : ℚ) {t : Four}
    (hd : rowCoefficient p B eta N d≠0) : (fullVector t d).prod=fullPrefix t*d := by
  rw [fullVector,List.prod_append,specified_product,residualPrimes_product hd]

theorem specified_support {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) : actualDwellSupport (runLevel p B eta N) (specified t) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hm:=U1011OriginalSixteenNearCapBoxProfiles.whole_box_nearcap_margins p B eta hv hw hc heta (coordinates N t) hb
  have hdQ:=(U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p B eta hv hw hc heta).2.2.1
  have hd : (0:ℝ)<(delta p B eta:ℝ) := by exact_mod_cast hdQ
  have hs : ∀j:Fin 4,(prefixProduct j t:ℝ)*(slots t j:ℝ)^2≤runLevel p B eta N := by
    intro j
    rw [←fullSquare_rpow hN ht j]
    exact Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [runLevel];linarith [hm.2.2.2.1 j])
  intro i hi
  have hi4 : i<4 := by simpa only [specified,List.length_cons,List.length_nil] using hi
  interval_cases i
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 0
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 1
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 2
  · simpa [specified,prefixProduct,prefixIndices,Finset.prod_filter,Fin.prod_univ_succ] using hs 3

theorem native_full_support {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B eta N d≠0) :
    actualDwellSupport (runLevel p B eta N) (fullVector t d) := by
  apply append_square_support _ _ (specified_support hN ht p B eta heta hv hw hc hb) (actual_plus_residual_well hd)
  have hbpos : (0:ℝ)<selectedProduct p t := by exact_mod_cast selectedProduct_pos ht p
  have h := (le_div_iff₀ hbpos).mp (prefix_residual_budget hN ht p B eta heta hv hw hc hb)
  rw [specified_product]
  have hid : (selectedProduct p t:ℝ)*((remainderPrimes p t).prod:ℝ)=(fullPrefix t:ℝ) := by
    exact_mod_cast selected_remainderPrimes_product p t
  calc
    (fullPrefix t:ℝ)*rowD p B eta N=((remainderPrimes p t).prod:ℝ)*rowD p B eta N*(selectedProduct p t:ℝ) := by
      rw [←hid];ring
    _ ≤ runLevel p B eta N := h

/-- Both branches are actual deterministic natural products. The small
capacity branch does not retain a fictitious selected middle. -/
def factors (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) (A : ℝ) (t : Four) (d : ℕ) : ℕ×ℕ×ℕ :=
  if 1≤runLevel p B eta N/(A*(selectedProduct p t:ℝ)) then
    let ac:=actualTwoCapacityFactors A (selectedVector p t d)
    (ac.1,selectedProduct p t,ac.2)
  else
    let ab:=actualTwoCapacityFactors A (fullVector t d)
    (ab.1,ab.2,1)

theorem native_completion {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ)
    (heta : 0<eta) (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B eta N d≠0)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) :
    let abc:=factors p B eta N A t d
    abc.1*abc.2.1*abc.2.2=fullPrefix t*d ∧ (abc.1:ℝ)≤A ∧
      A*(abc.2.1:ℝ)*(abc.2.2:ℝ)≤runLevel p B eta N ∧
      (if 1≤runLevel p B eta N/(A*(selectedProduct p t:ℝ)) then abc.2.1=selectedProduct p t
       else abc.2.2=1 ∧ (abc.2.1:ℝ)≤runLevel p B eta N/A ∧ runLevel p B eta N/A<(selectedProduct p t:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hApos : 0<A := zero_lt_one.trans_le hA
  have hb0 : 0<selectedProduct p t := selectedProduct_pos ht p
  have hb0r : (0:ℝ)<selectedProduct p t := by exact_mod_cast hb0
  have hm:=U1011OriginalSixteenNearCapBoxProfiles.whole_box_nearcap_margins p B eta hv hw hc heta (coordinates N t) hb
  have hAle : A≤runLevel p B eta N := hAupper.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [runLevel];linarith [hm.1,hm.2.1]))
  have hRdiv : 1≤runLevel p B eta N/A := (le_div_iff₀ hApos).mpr (by simpa only [one_mul] using hAle)
  by_cases hC : 1≤runLevel p B eta N/(A*(selectedProduct p t:ℝ))
  · have hs:=(native_active_selected_support hN ht p hp B eta heta hv hw hc hb hd).1
    have hsplit : A*(runLevel p B eta N/(A*(selectedProduct p t:ℝ)))=
        runLevel p B eta N/(selectedProduct p t:ℝ) := by field_simp [hApos.ne',hb0r.ne']
    have hs' : actualDwellSupport (A*(runLevel p B eta N/(A*(selectedProduct p t:ℝ)))) (selectedVector p t d) := by
      simpa only [hsplit,selectedVector] using hs
    obtain ⟨hprod,ha,hc'⟩:=actualTwoCapacityFactors_correct hA hC (selectedVector p t d) hs'
    have hexact:=(native_active_selected_support hN ht p hp B eta heta hv hw hc hb hd).2
    have hproduct : (actualTwoCapacityFactors A (selectedVector p t d)).1*selectedProduct p t*
        (actualTwoCapacityFactors A (selectedVector p t d)).2=fullPrefix t*d := by
      calc
        _ = selectedProduct p t*((actualTwoCapacityFactors A (selectedVector p t d)).1*
            (actualTwoCapacityFactors A (selectedVector p t d)).2) := by ring
        _ = _ := by rw [hprod];exact hexact
    have hcap : A*(selectedProduct p t:ℝ)*((actualTwoCapacityFactors A (selectedVector p t d)).2:ℝ)≤runLevel p B eta N := by
      have h:=(le_div_iff₀ (mul_pos hApos hb0r)).mp hc'
      simpa only [mul_assoc,mul_comm,mul_left_comm] using h
    simpa only [factors,if_pos hC] using And.intro hproduct (And.intro ha (And.intro hcap (rfl : selectedProduct p t=selectedProduct p t)))
  · have hs:=native_full_support hN ht p B eta heta hv hw hc hb hd
    obtain ⟨hsmall,hprod,ha,hb'⟩:=actualDwell_full_vector_repair hA hRdiv (fullVector t d) hs
      (selectedProduct p t) hb0 (lt_of_not_ge hC)
    have hproduct : (actualTwoCapacityFactors A (fullVector t d)).1*(actualTwoCapacityFactors A (fullVector t d)).2*1=
        fullPrefix t*d := by rw [mul_one,hprod,fullVector_product p B eta hd]
    have hcap : A*((actualTwoCapacityFactors A (fullVector t d)).2:ℝ)*(1:ℝ)≤runLevel p B eta N := by
      simpa only [mul_one,mul_comm] using (le_div_iff₀ hApos).mp hb'
    simpa only [factors,if_neg hC,Nat.cast_one] using
      And.intro hproduct (And.intro ha (And.intro hcap (And.intro (rfl : (1:ℕ)=1) (And.intro hb' hsmall))))

theorem completed_factors_positive {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ)
    (heta : 0<eta) (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B eta N d≠0)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) :
    let abc:=factors p B eta N A t d
    0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 := by
  have hprod:=(native_completion hN ht p hp B eta heta hv hw hc hb hd A hA hAupper).1
  have hdpos : 0<d := Nat.pos_of_ne_zero
    (actualSmallRosserSupport_squarefree _ _ _ (actualSmallRosserPlus_active hd).1).ne_zero
  have hfullpos : 0<fullPrefix t := by rw [fullPrefix_eq_multiplier];exact joint_multiplier_pos ht
  have hpos : 0<(factors p B eta N A t d).1*(factors p B eta N A t d).2.1*(factors p B eta N A t d).2.2 := by
    rw [hprod];exact mul_pos hfullpos hdpos
  exact ⟨Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hpos),
    Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hpos),Nat.pos_of_mul_pos_left hpos⟩

end
end ImbalancedChen.P5Z.U1011OriginalFifteenJointSelectedCompletion
