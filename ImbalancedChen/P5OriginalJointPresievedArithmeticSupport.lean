import ImbalancedChen.P5OriginalJointCommonBetaModel

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual ALL16 common-beta coefficient has genuine squarefree deleted-
target support below the ORIGINAL153/256 physical exponent. Its small
factor is paid by the actual20delta rough reserve, not discarded and not
identified with an all-prime native coefficient. This is arithmetic support
data for the new physical coefficient, not a distribution or PP licence.
-/

namespace ImbalancedChen.P5Z.OriginalJointPresievedArithmeticSupport

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open OriginalOrdinaryBetaRegroup OriginalOrdinaryResidualArithmeticFactor
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalCommonBetaActualParameters OriginalJointPresievedCompiler OriginalJointCommonBetaModel

private theorem cap_ceiling (p:Policy) (v:LogFour) (hv:0≤v 2) : cap p v≤(153/256:ℝ) := by
  by_cases hp:p.val<15
  · unfold cap
    rw [if_pos hp]
    by_cases hs:selectedMass p v≤(25/128:ℝ)
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  · unfold cap
    rw [if_neg hp]
    linarith

/-- Every active actual joint coefficient has the original arithmetic
carrier and support exponent, including the distinct W branch. -/
theorem actual_joint_arithmetic_support {n N q:ℕ} {eta:ℚ} {nu0 epsilon:ℝ}
    (hN:1<N) (heta:0<eta) (hnu0:0<nu0) (he:0<epsilon)
    (heBudget:epsilon<epsilonBudget n eta nu0) (E:ℕ×ℕ→Prop)
    (hq:jointPresievedSigma n N eta ((N:ℝ)^(nu0*epsilon^2)) ((N:ℝ)^(nu0*epsilon)) E q≠0) :
    0<q ∧ Squarefree q ∧ q.Coprime N ∧
      |jointPresievedSigma n N eta ((N:ℝ)^(nu0*epsilon^2)) ((N:ℝ)^(nu0*epsilon)) E q|≤1 ∧
      (q:ℝ)<(N:ℝ)^(153/256:ℝ) := by
  have hw (t:Four) (ht:t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :=
    (parameters_on_joint_row hN heta hnu0 he heBudget ht).1
  have hmem : q∈jointSupport n N eta ((N:ℝ)^(nu0*epsilon^2)) E := by
    by_contra h
    exact hq (jointSigma_zero_off_support n N eta _ _ E h)
  obtain ⟨m,hm,hmod⟩ := Finset.mem_image.mp hmem
  subst q
  obtain ⟨ht,hr⟩ := Finset.mem_sigma.mp hm
  have hsource := (Finset.mem_filter.mp ht).1
  have htag := (Finset.mem_filter.mp ht).2
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  have hrow : rowCoefficient n N eta ((N:ℝ)^(nu0*epsilon^2)) ((N:ℝ)^(nu0*epsilon)) m.1 m.2≠0 := by
    rw [←jointSigma_eq_row hN heta hw hm]
    exact hq
  have hsfR := actualSmallRoughModuli_squarefree
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta m.1)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
    ((N:ℝ)^(nu0*epsilon^2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1) hr
  have hcopR := actualSmallRoughModuli_coprime_target
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta m.1)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
    ((N:ℝ)^(nu0*epsilon^2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1) hr
  have hcop := joint_row_coprime_prefix hN heta ht (hw m.1 ht) hr
  have hsfP := U1011OriginalFifteenTopFourUniqueness.fullPrefix_squarefree hsource
  have hcopP := subproduct_coprime_target hsource Finset.univ
  have hposP : 0<fullPrefix m.1 := by
    rw [fullPrefix_eq_multiplier]
    exact joint_multiplier_pos hsource
  have hposR : 0<m.2 := Nat.pos_of_ne_zero hsfR.ne_zero
  refine ⟨Nat.mul_pos hposP hposR,(Nat.squarefree_mul hcop).mpr ⟨hsfP,hsfR⟩,
    Nat.coprime_mul_iff_left.mpr ⟨hcopP,hcopR⟩,jointSigma_abs_le_one hN heta E hw _,?_⟩
  obtain ⟨e,heS,d,hd,her,heB,hdc⟩ := actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta m.1)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
    ((N:ℝ)^(nu0*epsilon^2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1)
    ((N:ℝ)^(nu0*epsilon)) hrow
  have hdW : roughWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
      ((N:ℝ)^(nu0*epsilon^2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1)
      (U1011OriginalSixteenJointNearCapCompiler.D n N eta m.1) d≠0 := by
    rw [←ordinary_rough_coefficient N _ _ _ _ hlegal.2.1 d]
    exact hdc
  have hda := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_active hdW
  have he1 : 1∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1)) ((N:ℝ)^(nu0*epsilon^2)) :=
    Nat.mem_divisors.mpr ⟨one_dvd _,actualSmallPrimeProduct_ne_zero _ _ _⟩
  have hdM : d∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1) := by
    rw [nativeSupport_eq_products N _ (hw m.1 ht)]
    exact Finset.mem_image.mpr ⟨(1,d),Finset.mem_product.mpr ⟨he1,hda.1⟩,one_mul d⟩
  have hdNative : U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta m.1 d≠0 := by
    change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight
      (actualSmallPrimeProduct N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
      (U1011OriginalSixteenJointNearCapCompiler.D n N eta m.1) d≠0
    rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_apply,
      if_pos ⟨hdM,hda.2.1,hda.2.2⟩]
    exact pow_ne_zero _ (by norm_num)
  let box := U1011OriginalSixteenStaticNativeCompiler.ownerBox n N m.1
  let p := U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N m.1
  have hcert := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate box htag).2
  have hvalid : box.Valid := gridBox_valid n _
  have hpositive : 0<box.lo 3 := gridBox_lower_positive n _ 3
  have hp2 : (0:ℝ)≤(box.lo 2:ℝ) := by
    exact_mod_cast (gridBox_lower_positive n (owner n (coordinates N m.1)) 2).le
  have hcorner := U1011OriginalSixteenStaticCellWinner.corner_mem_region box hvalid
  have hpars := U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p box eta
    hvalid hpositive hcert heta
  have hnuLower : (U1011OriginalSixteenNearCapBoxProfiles.nu p box eta:ℝ)<
      (capLower p box:ℝ) := by exact_mod_cast hpars.2.1
  have hnu : (U1011OriginalSixteenNearCapBoxProfiles.nu p box eta:ℝ)<(153/256:ℝ) :=
    hnuLower.trans_le ((cap_bounds p box hcorner).1.trans
      (cap_ceiling p _ hp2))
  have hdelta : (0:ℝ)<(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ) := by
    exact_mod_cast hpars.2.2.1
  have hgeom := owner_mem n (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hsource)
  have hfull := U1011OriginalSixteenJointNearCapCompiler.joint_row_active_full_modulus_cap
    hN hsource p box eta (cell_subset_closed_box n _ hgeom) hdNative
  have hell := (parameters_on_joint_row hN heta hnu0 he heBudget ht).2.2
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hdpos : 0<d := Nat.pos_of_ne_zero (fixedRoughSupport_squarefree _ _ _ _ _ hd).ne_zero
  have hprodpos : (0:ℝ)<((fullPrefix m.1*d:ℕ):ℝ) := by exact_mod_cast Nat.mul_pos hposP hdpos
  calc
    (modulus m:ℝ)=(e:ℝ)*((fullPrefix m.1*d:ℕ):ℝ) := by
      simp only [modulus,her,Nat.cast_mul]
      ring
    _ < (N:ℝ)^(nu0*epsilon)*((fullPrefix m.1*d:ℕ):ℝ) :=
      mul_lt_mul_of_pos_right heB hprodpos
    _ < (N:ℝ)^(nu0*epsilon)*
        (N:ℝ)^((U1011OriginalSixteenNearCapBoxProfiles.nu p box eta:ℝ)-
          20*(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ)) :=
      mul_lt_mul_of_pos_left hfull (Real.rpow_pos_of_pos hn0 _)
    _ = (N:ℝ)^(nu0*epsilon+(U1011OriginalSixteenNearCapBoxProfiles.nu p box eta:ℝ)-
        20*(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ)) := by
      rw [←Real.rpow_add hn0]
      congr 1
      ring
    _ ≤ (N:ℝ)^(153/256:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn.le (by
        change nu0*epsilon≤(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ)/8 at hell
        linarith)

end
end ImbalancedChen.P5Z.OriginalJointPresievedArithmeticSupport
