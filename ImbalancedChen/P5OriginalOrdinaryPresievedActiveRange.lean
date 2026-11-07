import ImbalancedChen.P5OriginalOrdinaryPresievedSigma

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The true common-beta coefficient has a different active product carrier
from the old all-prime native coefficient. This file derives its actual
inflation: the rough original row retains its original near-cap margin,
and its small factor costs the common physical level B. No support or PP
licence for the old sigma is reused for the new coefficient.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryPresievedActiveRange

noncomputable section
open scoped BigOperators
open Classical
open U1011OriginalSixteenArithmeticProducts
open P5U1011JointOverlap
open OriginalOrdinaryBetaRegroup OriginalOrdinaryResidualArithmeticFactor
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma

def rowExponent (n N : ℕ) (eta : ℚ) (t : Four) : ℝ :=
  (U1011OriginalSixteenNearCapBoxProfiles.nu
    (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
    (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ) -
  20*(U1011OriginalSixteenNearCapBoxProfiles.delta
    (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
    (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta:ℝ)

/-- Active common-beta rows expose their actual small/rough integers.
The rough factor is proved to be a nonzero ORIGINAL native row in its own
right, so the existing original near-cap product estimate applies to it. -/
theorem active_row_factors {n N r : ℕ} {eta : ℚ} {w B : ℝ} {E : ℕ×ℕ→Prop}
    (hN : 1<N) (heta : 0<eta) {t : Four} (ht : t∈tuples n N E)
    (hw : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hr : rowCoefficient n N eta w B t r≠0) :
    ∃e∈actualSmallRosserSupport N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w,
      ∃d∈fixedRoughSupport
        (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
        r=e*d ∧ (e:ℝ)<B ∧
        ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^rowExponent n N eta t ∧
        ((fullPrefix t*r:ℕ):ℝ)<B*(N:ℝ)^rowExponent n N eta t := by
  have htOrd := (Finset.mem_filter.mp ht).1
  have hs := (Finset.mem_filter.mp htOrd).1
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta htOrd
  have hD := hlegal.2.1
  obtain ⟨e,he,d,hd,her,heB,hdc⟩ := actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) B hr
  have hdW : roughWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
      (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d≠0 := by
    rw [←ordinary_rough_coefficient N _ w _ _ hD d]
    exact hdc
  have hda := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_active hdW
  have he1 : 1∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w :=
    Nat.mem_divisors.mpr ⟨one_dvd _,actualSmallPrimeProduct_ne_zero _ _ _⟩
  have hdM : d∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) := by
    rw [nativeSupport_eq_products N _ hw]
    exact Finset.mem_image.mpr ⟨(1,d),Finset.mem_product.mpr ⟨he1,hda.1⟩,one_mul d⟩
  have hdNative : U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t d≠0 := by
    change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight
      (actualSmallPrimeProduct N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d≠0
    rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_apply,
      if_pos ⟨hdM,hda.2.1,hda.2.2⟩]
    exact pow_ne_zero _ (by norm_num)
  have hcell := U1011OriginalFifteenNativeGridCells.owner_mem n
    (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs)
  have hbox := U1011OriginalFifteenNativeGridCells.cell_subset_closed_box n _ hcell
  have hfull := U1011OriginalSixteenJointNearCapCompiler.joint_row_active_full_modulus_cap hN hs
    (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
    (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta hbox hdNative
  change ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^rowExponent n N eta t at hfull
  have hepos : (0:ℝ)<e := by
    exact_mod_cast Nat.pos_of_ne_zero (actualSmallRosserSupport_squarefree _ _ _ he).ne_zero
  have hdpos : 0<d := Nat.pos_of_ne_zero
    (fixedRoughSupport_squarefree _ _ _ _ _ hd).ne_zero
  have hpref : 0<fullPrefix t := by
    rw [fullPrefix_eq_multiplier]
    exact joint_multiplier_pos hs
  have hprodpos : (0:ℝ)<((fullPrefix t*d:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hpref hdpos
  have hBpos : 0<B := hepos.trans heB
  refine ⟨e,he,d,hd,her,heB,hfull,?_⟩
  calc
    ((fullPrefix t*r:ℕ):ℝ)=(e:ℝ)*((fullPrefix t*d:ℕ):ℝ) := by
      rw [her]
      push_cast
      ring
    _ < B*((fullPrefix t*d:ℕ):ℝ) := mul_lt_mul_of_pos_right heB hprodpos
    _ < B*(N:ℝ)^rowExponent n N eta t := mul_lt_mul_of_pos_left hfull hBpos

/-- Actual support of the physical presieved coefficient: the common
beta level is paid explicitly, before any complete-scale PP query. -/
theorem active_physical_factors {n N q : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1<N) (heta : 0<eta) (E : ℕ×ℕ→Prop)
    (hw : ∀t∈tuples n N E,w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hq : presievedSigma n N eta w B E q≠0) :
    ∃t∈tuples n N E, ∃r∈rowSupport n N eta w t,
      q=fullPrefix t*r ∧
      ∃e∈actualSmallRosserSupport N
          (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w,
        ∃d∈fixedRoughSupport
          (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
          (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
          (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
          r=e*d ∧ (e:ℝ)<B ∧
          ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^rowExponent n N eta t ∧
          (q:ℝ)<B*(N:ℝ)^rowExponent n N eta t := by
  have hmem : q∈physicalSupport n N eta w E := by
    by_contra h
    exact hq (presievedSigma_eq_zero_off_support n N eta w B E h)
  obtain ⟨m,hm,hmod⟩ := Finset.mem_image.mp hmem
  obtain ⟨ht,hr⟩ := Finset.mem_sigma.mp hm
  have hnz : rowCoefficient n N eta w B m.1 m.2≠0 := by
    rw [←presievedSigma_eq_row hN heta hw hm,hmod]
    exact hq
  obtain ⟨e,he,d,hd,hed,heB,hfull,hphysical⟩ :=
    active_row_factors hN heta ht (hw m.1 ht) hnz
  refine ⟨m.1,ht,m.2,hr,hmod.symm,e,he,d,hd,hed,heB,hfull,?_⟩
  simpa only [modulus,←hmod] using hphysical

end
end ImbalancedChen.P5Z.OriginalOrdinaryPresievedActiveRange
