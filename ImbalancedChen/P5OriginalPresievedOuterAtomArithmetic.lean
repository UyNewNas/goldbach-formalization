import ImbalancedChen.P5OriginalPresievedOuterAtomSupport
import ImbalancedChen.P5OriginalCommonBetaActualParameters
import ImbalancedChen.ActualPrimeSlotSquarefreeSymmetry

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Independent outer prefix tuples retain the physical arithmetic carrier
when their literal prime labels are distinct and their lower endpoints
stay above the frozen row's prime cutoff. The actual xi buffer pays the
outer padding. This does not infer original source ownership or physical
fibre uniqueness from a smooth box.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedOuterAtomArithmetic

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells)
open OriginalOrdinaryCommonBetaModel OriginalPresievedOuterAtomSupport
open OriginalCommonBetaActualParameters

theorem common_parameters_on_selected_cell {n N:ℕ} {eta:ℚ} {nu epsilon:ℝ}
    (hN:1<N) (hnu:0<nu) (he:0<epsilon) (heBudget:epsilon<epsilonBudget n eta nu)
    (j:Grid n) (hj:j∈selectedCells n) :
    (N:ℝ)^(nu*epsilon^2)≤U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N ∧
      nu*epsilon≤(U1011OriginalSixteenNearCapBoxProfiles.delta
        (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)/8 := by
  have he8:epsilon≤1/8:=heBudget.le.trans (min_le_left _ _)
  have heCut:epsilon≤(cutoffMin n eta:ℝ)/nu:=
    heBudget.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heEll:epsilon≤(U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ)/(4*nu):=
    heBudget.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcutLinear:=(le_div_iff₀ hnu).mp heCut
  have hellLinear:=(le_div_iff₀ (by positivity:0<4*nu)).mp heEll
  have hcut:(cutoffMin n eta:ℝ)≤(cellCutoff n eta j:ℝ):=by
    exact_mod_cast cutoffMin_le_cell eta j hj
  have hell:(U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta:ℝ)≤
      (U1011OriginalSixteenNearCapCommonSmallParameters.cellDelta n eta j:ℝ)/2:=by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.ellMax_le_cell eta j hj
  have heSquare:epsilon^2≤epsilon:=by nlinarith
  have hn:(1:ℝ)<N:=by exact_mod_cast hN
  constructor
  · change (N:ℝ)^(nu*epsilon^2)≤(N:ℝ)^(cellCutoff n eta j:ℝ)
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    exact (mul_le_mul_of_nonneg_left heSquare hnu.le).trans (by nlinarith)
  · change nu*epsilon≤(U1011OriginalSixteenNearCapCommonSmallParameters.cellDelta n eta j:ℝ)/8
    nlinarith

/-- Literal endpoint separation pays the prefix/residual coprimality,
then actual label injectivity pays squarefreeness. These are proved even
for tuples outside the original selector. -/
theorem actual_outer_physical_arithmetic {n N r:ℕ} {eta:ℚ} {nu epsilon width:ℝ}
    (hN:1<N) (heta:0<eta) (hnu:0<nu) (he:0<epsilon)
    (heBudget:epsilon<epsilonBudget n eta nu) (j:Grid n) (hj:j∈selectedCells n)
    (hwidthDelta:width≤(U1011OriginalSixteenNearCapBoxProfiles.delta
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)/32)
    (hwidthXi:width≤(U1011OriginalSixteenNearCapBoxProfiles.xi
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)/2)
    (t:Fin 4→ℕ) (hprime:∀i,Nat.Prime (t i) ∧ ¬t i∣N) (hinj:Function.Injective t)
    (hlo:∀i,(N:ℝ)^(((gridBox n j).lo 3:ℝ)-width)≤(t i:ℝ))
    (hhi:∀i,(t i:ℝ)≤(N:ℝ)^(((gridBox n j).hi i:ℝ)+width))
    (hr:frozenCoefficient n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) r≠0) :
    0<(∏i,t i)*r ∧ Squarefree ((∏i,t i)*r) ∧ ((∏i,t i)*r).Coprime N ∧
      ((((∏i,t i)*r:ℕ):ℝ)<(N:ℝ)^(153/256:ℝ)) := by
  let box:=gridBox n j
  let p:=U1011OriginalSixteenStaticNativeCompiler.boxPolicy box
  let z:=U1011OriginalSixteenJointNearCapCompiler.rowZ p box eta N
  let L:=U1011OriginalSixteenJointNearCapCompiler.rowD p box eta N
  let w:=(N:ℝ)^(nu*epsilon^2)
  have hparameters:=common_parameters_on_selected_cell hN hnu he heBudget j hj
  have hw:w≤z:=hparameters.1
  have hcert:=(U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate box
    ((U1011OriginalSixteenCommonSmallParameters.mem_selectedCells j).mp hj)).2
  have hpars:=U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p box eta
    (gridBox_valid n j) (gridBox_lower_positive n j 3) hcert heta
  have hxi:(0:ℝ)<(U1011OriginalSixteenNearCapBoxProfiles.xi p box eta:ℝ):=by
    exact_mod_cast hpars.2.2.2.1
  have hn:(1:ℝ)<N:=by exact_mod_cast hN
  have hz:z≤(N:ℝ)^((box.lo 3:ℝ)-(U1011OriginalSixteenNearCapBoxProfiles.xi p box eta:ℝ)):=by
    change (N:ℝ)^(U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p box eta:ℝ)≤_
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    change ((min _ _:ℚ):ℝ)≤_
    exact_mod_cast min_le_left (box.lo 3-U1011OriginalSixteenNearCapBoxProfiles.xi p box eta)
      (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p box eta/
        (2+U1011OriginalSixteenNearCapBoxProfiles.rho p box eta))
  have hprefixLower (i:Fin 4):z<(t i:ℝ):=by
    have hstrict:(N:ℝ)^((box.lo 3:ℝ)-(U1011OriginalSixteenNearCapBoxProfiles.xi p box eta:ℝ))<
        (N:ℝ)^((box.lo 3:ℝ)-width):=by
      apply Real.rpow_lt_rpow_of_exponent_lt hn
      change width≤(U1011OriginalSixteenNearCapBoxProfiles.xi p box eta:ℝ)/2 at hwidthXi
      linarith
    exact hz.trans_lt (hstrict.trans_le (hlo i))
  obtain ⟨e,heS,d,hd,her,heB,hdc⟩:=actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd L) N (Nat.ceil z) w z ((N:ℝ)^(nu*epsilon)) hr
  have hrMem:r∈actualSmallRoughModuli (ordinaryRetainOdd L) N (Nat.ceil z) w z:=
    Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨heS,hd⟩,her.symm⟩
  have hsfR:=actualSmallRoughModuli_squarefree _ _ _ _ _ hrMem
  have hcopR:=actualSmallRoughModuli_coprime_target _ _ _ _ _ hrMem
  have heSmall:=actualSmallRosserSupport_smallPrimeSupportedAt N (Nat.ceil z) w heS
  have hdSF:=fixedRoughSupport_squarefree (ordinaryRetainOdd L) N (Nat.ceil z) w z hd
  have hsmall:∀q∈r.primeFactors,(q:ℝ)<z:=by
    rw [her,Nat.primeFactors_mul heSmall.1 hdSF.ne_zero]
    intro q hq
    rcases Finset.mem_union.mp hq with hq|hq
    · exact (heSmall.2 q hq).trans_le hw
    · exact mem_roughPrimeUniverse_upper
        (fixedRoughSupport_primeFactors_mem (ordinaryRetainOdd L) N (Nat.ceil z) w z hd hq)
  have hcop:(∏i,t i).Coprime r:=by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    apply (hprime i).1.coprime_iff_not_dvd.mpr
    intro hdvd
    have hp: t i∈r.primeFactors:=Nat.mem_primeFactors.mpr ⟨(hprime i).1,hdvd,hsfR.ne_zero⟩
    exact (not_lt_of_ge (hprefixLower i).le) (hsmall (t i) hp)
  have hsfP:Squarefree (∏i,t i):=by
    have hp:∀q∈List.ofFn t,Nat.Prime q:=by
      intro q hq
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
      exact (hprime i).1
    simpa only [List.prod_ofFn] using
      actualPrimeVector_squarefree (List.ofFn t) hp (List.nodup_ofFn.mpr hinj)
  have hcopP:(∏i,t i).Coprime N:=by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    exact (hprime i).1.coprime_iff_not_dvd.mpr (hprime i).2
  have hposP:0<∏i,t i:=Finset.prod_pos (fun i hi=>(hprime i).1.pos)
  refine ⟨Nat.mul_pos hposP (Nat.pos_of_ne_zero hsfR.ne_zero),
    (Nat.squarefree_mul hcop).mpr ⟨hsfP,hsfR⟩,
    Nat.coprime_mul_iff_left.mpr ⟨hcopP,hcopR⟩,?_⟩
  exact actual_padded_physical_support hN heta j hj w (nu*epsilon) width
    hparameters.2 hwidthDelta t hhi hr

end
end ImbalancedChen.P5Z.OriginalPresievedOuterAtomArithmetic
