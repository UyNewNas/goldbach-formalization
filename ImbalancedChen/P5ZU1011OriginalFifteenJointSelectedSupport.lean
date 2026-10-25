import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler
import ImbalancedChen.Part3ActualCompactAllRankSupport
import ImbalancedChen.ActualDwellSelectedRemainder

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual original15 bit-selected remainder vectors for a fixed near-cap box.
Nonzero native upper-Rosser coefficients produce their genuine decreasing
prime-factor residual vector and its full square support from the actual
odd-cubic tests. The literal unselected four-prime slots are attached using
the original selected-square gates and the SAME full-prefix residual budget.
No primitive hFullSupport, factorability or unit-to-factorability implication.
W is excluded from the selected-middle construction. Native density, H248,
physical AP/PP and completion monomials remain separate OPEN obligations.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenJointSelectedSupport
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalSixteenInteriorArithmetic P5U1011JointOverlap
open U1011OriginalSixteenNearCapBoxProfiles (nu delta Tplus)
open U1011OriginalSixteenJointNearCapCompiler (rowD rowZ rowCoefficient)
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def residualPrimes (d : ℕ) : List ℕ := d.primeFactorsList.reverse

/-- This follows from the literal coefficient's parity-cubic predicate,
not from its amplitude or its total-product cutoff. -/
theorem actual_plus_residual_well {N cap d : ℕ} {Z D : ℝ}
    (hd : actualSmallRosserPlus N cap Z D d≠0) :
    actualDwellSupport D (residualPrimes d) := by
  have ha := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_active hd
  have hs := actualSmallRosserSupport_squarefree N cap Z ha.1
  have hge : (residualPrimes d).Pairwise (·≥·) := (Nat.primeFactorsList_sorted d).reverse.pairwise
  have hnd : (residualPrimes d).Nodup := hs.nodup_primeFactorsList.reverse
  have hgt : (residualPrimes d).Pairwise (·>·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hle := (List.pairwise_iff_getElem.mp hge) i j hi hj hij
    have hne := (List.pairwise_iff_getElem.mp hnd) i j hi hj hij
    omega
  apply Part3.ActualCompactAllRankSupport.upper_set_dwell_support (residualPrimes d)
    (fun p hp=>Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)) hgt
  simpa only [residualPrimes,List.toFinset_reverse,Nat.toFinset_factors] using ha.2.2

theorem residualPrimes_product {N cap d : ℕ} {Z D : ℝ}
    (hd : actualSmallRosserPlus N cap Z D d≠0) : (residualPrimes d).prod=d := by
  rw [residualPrimes,List.prod_reverse,Nat.prod_primeFactorsList]
  exact (actualSmallRosserSupport_squarefree N cap Z (actualSmallRosserPlus_active hd).1).ne_zero

def remainderSlots (p : Policy) : List (Fin 4) :=
  [0,1,2,3].filter (fun j=>decide (¬Selected p j))
def remainderPrimes (p : Policy) (t : Four) : List ℕ := (remainderSlots p).map (slots t)

theorem remainderPrimes_product (p : Policy) (t : Four) :
    (remainderPrimes p t).prod=remainderProduct p t := by
  by_cases h0 : Selected p 0 <;> by_cases h1 : Selected p 1 <;>
    by_cases h2 : Selected p 2 <;> by_cases h3 : Selected p 3
  all_goals simp [remainderPrimes,remainderSlots,remainderProduct,remainderIndices,
    Finset.prod_filter,Fin.prod_univ_succ,h0,h1,h2,h3]

theorem selected_remainderPrimes_product (p : Policy) (t : Four) :
    selectedProduct p t*(remainderPrimes p t).prod=fullPrefix t := by
  rw [remainderPrimes_product,selected_mul_remainder]

theorem selectedProduct_pos {N : ℕ} {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) : 0<selectedProduct p t :=
  Finset.prod_pos (fun i _=>slots_pos ht i)

/-- Exact finite bitmask-to-list prefix bridge: each list prefix contains
precisely the earlier unselected slots of the ORIGINAL decreasing tuple. -/
theorem remainder_square_support (p : Policy) (t : Four) {D : ℝ}
    (hb : (0:ℝ)<selectedProduct p t)
    (hg : ∀j:Fin 4,¬Selected p j→
      (selectedProduct p t:ℝ)*(earlierRemainderProduct p j t:ℝ)*(slots t j:ℝ)^2≤D) :
    actualDwellSupport (D/(selectedProduct p t:ℝ)) (remainderPrimes p t) := by
  have g (j : Fin 4) (hj : ¬Selected p j) :
      (earlierRemainderProduct p j t:ℝ)*(slots t j:ℝ)^2≤D/(selectedProduct p t:ℝ) := by
    apply (le_div_iff₀ hb).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hg j hj
  have g0:=g 0
  have g1:=g 1
  have g2:=g 2
  have g3:=g 3
  intro k hk
  by_cases h0 : Selected p 0 <;> by_cases h1 : Selected p 1 <;>
    by_cases h2 : Selected p 2 <;> by_cases h3 : Selected p 3
  all_goals simp [remainderPrimes,remainderSlots,h0,h1,h2,h3] at hk ⊢
  all_goals interval_cases k <;>
    simp_all [earlierRemainderProduct,earlierRemainderIndices,Finset.prod_filter,
      Fin.prod_univ_succ,mul_assoc]

/-- Public indexed append law, preserving original occurrences. -/
theorem append_square_support (front tail : List ℕ) {D R : ℝ}
    (hf : actualDwellSupport D front) (ht : actualDwellSupport R tail)
    (hbudget : (front.prod:ℝ)*R≤D) : actualDwellSupport D (front++tail) := by
  intro i hi
  by_cases hfront : i<front.length
  · have hs:=hf i hfront
    have htake : (front++tail).take i=front.take i := List.take_append_of_le_length (by omega)
    have hget : (front++tail)[i]=front[i] := List.getElem_append_left hfront
    simpa only [htake,hget] using hs
  · let k:=i-front.length
    have hk : k<tail.length := by dsimp [k];simp only [List.length_append] at hi;omega
    have heq : i=front.length+k := by dsimp [k];omega
    rw [heq]
    have htake : (front++tail).take (front.length+k)=front++tail.take k := by
      rw [List.take_append,List.take_of_length_le (by omega),Nat.add_sub_cancel_left]
    have hget : (front++tail)[front.length+k]=tail[k] := by
      simpa only [Nat.add_comm] using (List.getElem_append_right' front hk).symm
    rw [htake,hget,List.map_append,List.prod_append,actualNatList_cast_prod]
    have hs:=mul_le_mul_of_nonneg_left (ht k hk) (Nat.cast_nonneg front.prod : (0:ℝ)≤front.prod)
    exact (by simpa only [mul_assoc] using hs).trans hbudget

def runLevel (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : ℝ :=
  (N:ℝ)^((nu p B eta:ℝ)-2*(delta p B eta:ℝ))

theorem native_remainder_support {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ)
    (heta : 0<eta) (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) :
    actualDwellSupport (runLevel p B eta N/(selectedProduct p t:ℝ)) (remainderPrimes p t) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hm:=U1011OriginalSixteenNearCapBoxProfiles.whole_box_nearcap_margins p B eta hv hw hc heta (coordinates N t) hb
  have hdQ:=(U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p B eta hv hw hc heta).2.2.1
  have hd : (0:ℝ)<(delta p B eta:ℝ) := by exact_mod_cast hdQ
  apply remainder_square_support p t (by exact_mod_cast selectedProduct_pos ht p)
  intro j hj
  have hsel : ∀j:Fin 4,¬Selected p j→
      selectedSquare p j (coordinates N t)+64*(delta p B eta:ℝ)≤(nu p B eta:ℝ) := by
    simpa only [if_pos hp] using hm.2.2.2.2
  have hselected:=hsel j hj
  rw [←selectedSquare_rpow hN ht p j]
  exact Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [runLevel];linarith)

theorem prefix_residual_budget {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) :
    ((remainderPrimes p t).prod:ℝ)*rowD p B eta N≤runLevel p B eta N/(selectedProduct p t:ℝ) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hdQ:=(U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p B eta hv hw hc heta).2.2.1
  have hd : (0:ℝ)<(delta p B eta:ℝ) := by exact_mod_cast hdQ
  have hs : U11SelectedLargest.prefixSum (coordinates N t)≤(Tplus B:ℝ) := by
    simp only [U11SelectedLargest.prefixSum,U1011OriginalSixteenNearCapBoxProfiles.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus,Rat.cast_add]
    linarith [hb.2 0,hb.2 1,hb.2 2,hb.2 3]
  have hprod : (fullPrefix t:ℝ)≤(N:ℝ)^(Tplus B:ℝ) := by
    rw [←fullPrefix_rpow hN ht]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hs
  have hfull : (fullPrefix t:ℝ)*rowD p B eta N≤runLevel p B eta N := by
    calc
      _ ≤ (N:ℝ)^(Tplus B:ℝ)*rowD p B eta N := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hn0.le _)
      _ = (N:ℝ)^((nu p B eta:ℝ)-20*(delta p B eta:ℝ)) := by
        rw [rowD,←Real.rpow_add hn0]
        congr 1
        simp only [U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [runLevel];linarith)
  apply (le_div_iff₀ (by exact_mod_cast selectedProduct_pos ht p)).mpr
  have hid : (selectedProduct p t:ℝ)*((remainderPrimes p t).prod:ℝ)=(fullPrefix t:ℝ) := by
    exact_mod_cast selected_remainderPrimes_product p t
  calc
    ((remainderPrimes p t).prod:ℝ)*rowD p B eta N*(selectedProduct p t:ℝ)=
        (fullPrefix t:ℝ)*rowD p B eta N := by rw [←hid];ring
    _ ≤ runLevel p B eta N := hfull

/-- The actual nonzero native divisor produces the completed selected
remainder support. There is no supplied residual well-support predicate. -/
theorem native_active_selected_support {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ)
    (heta : 0<eta) (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B eta N d≠0) :
    actualDwellSupport (runLevel p B eta N/(selectedProduct p t:ℝ))
      (remainderPrimes p t++residualPrimes d) ∧
      selectedProduct p t*(remainderPrimes p t++residualPrimes d).prod=fullPrefix t*d := by
  refine ⟨append_square_support _ _ (native_remainder_support hN ht p hp B eta heta hv hw hc hb)
    (actual_plus_residual_well hd) (prefix_residual_budget hN ht p B eta heta hv hw hc hb),?_⟩
  rw [List.prod_append,residualPrimes_product hd,←mul_assoc,selected_remainderPrimes_product]

end
end ImbalancedChen.P5Z.U1011OriginalFifteenJointSelectedSupport
