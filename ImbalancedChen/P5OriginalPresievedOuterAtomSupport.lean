import ImbalancedChen.P5OriginalJointPresievedArithmeticSupport
import ImbalancedChen.P5ZU1011OriginalSixteenCommonSmallParameters

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Separated outer smooth boxes need not be subsets of the original tuple
source. This file proves their physical SUPPORT bound directly from the
literal frozen row and padded prime-slot endpoints. Padding and the true
beta factor are paid by the original20delta reserve. Source membership,
tuple ordering, physical injectivity and PP are NOT inferred here.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedOuterAtomSupport

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells mem_selectedCells)
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryResidualArithmeticFactor

def frozenCoefficient (n:ℕ) (eta:ℚ) (j:Grid n) (N:ℕ) (w ell:ℝ) (r:ℕ) : ℝ :=
  presievedCoefficient N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)) w
    (U1011OriginalSixteenJointNearCapCompiler.rowZ
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)
    (U1011OriginalSixteenJointNearCapCompiler.rowD
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N)
    ((N:ℝ)^ell) r

theorem padded_prefix_product {N:ℕ} (hN:1<N) (box:Box) (width:ℝ) (t:Fin 4→ℕ)
    (ht:∀i,(t i:ℝ)≤(N:ℝ)^((box.hi i:ℝ)+width)) :
    ((∏i,t i:ℕ):ℝ)≤(N:ℝ)^((U1011OriginalSixteenNearCapBoxProfiles.Tplus box:ℝ)+4*width) := by
  have hn:(0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsum : (U1011OriginalSixteenNearCapBoxProfiles.Tplus box:ℝ)+4*width=
      ∑i:Fin 4,((box.hi i:ℝ)+width) := by
    simp [U1011OriginalSixteenNearCapBoxProfiles.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus,Fin.sum_univ_succ]
    ring
  rw [Nat.cast_prod,hsum,Real.rpow_sum_of_pos hn]
  exact Finset.prod_le_prod (fun _ _=>Nat.cast_nonneg _) (fun i _=>ht i)

/-- Actual frozen selected-row support for arbitrary padded prime-slot
tuples, including tuples outside the original source or on its boundaries.
No one-boundedness or coefficient-fibre uniqueness is claimed. -/
theorem actual_padded_physical_support {n N r:ℕ} {eta:ℚ} (hN:1<N) (heta:0<eta)
    (j:Grid n) (hj:j∈selectedCells n) (w ell width:ℝ)
    (hell:ell≤(U1011OriginalSixteenNearCapBoxProfiles.delta
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)/8)
    (hwidth:width≤(U1011OriginalSixteenNearCapBoxProfiles.delta
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ)/32)
    (t:Fin 4→ℕ) (ht:∀i,(t i:ℝ)≤(N:ℝ)^(((gridBox n j).hi i:ℝ)+width))
    (hr:frozenCoefficient n eta j N w ell r≠0) :
    (((∏i,t i)*r:ℕ):ℝ)<(N:ℝ)^(153/256:ℝ) := by
  let box:=gridBox n j
  let p:=U1011OriginalSixteenStaticNativeCompiler.boxPolicy box
  let z:=U1011OriginalSixteenJointNearCapCompiler.rowZ p box eta N
  let L:=U1011OriginalSixteenJointNearCapCompiler.rowD p box eta N
  have hcert := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate box
    ((mem_selectedCells j).mp hj)).2
  have hvalid:box.Valid:=gridBox_valid n j
  have hpositive:0<box.lo 3:=gridBox_lower_positive n j 3
  have hpars:=U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p box eta
    hvalid hpositive hcert heta
  have hn:(1:ℝ)<N := by exact_mod_cast hN
  have hn0:(0:ℝ)<N := zero_lt_one.trans hn
  have hL:1<L := Real.one_lt_rpow hn (by exact_mod_cast hpars.2.2.2.2.2.1)
  have hdelta:(0:ℝ)<(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ) := by
    exact_mod_cast hpars.2.2.1
  obtain ⟨e,he,d,hd,her,heB,hdc⟩ := actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd L) N (Nat.ceil z) w z ((N:ℝ)^ell) hr
  have hdW:roughWeight N (Nat.ceil z) w z L d≠0 := by
    rw [←ordinary_rough_coefficient N (Nat.ceil z) w z L hL d]
    exact hdc
  have hdL:(d:ℝ)<L :=
    (MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_active hdW).2.1
  have hdpos:(0:ℝ)<d := by
    exact_mod_cast Nat.pos_of_ne_zero (fixedRoughSupport_squarefree _ _ _ _ _ hd).ne_zero
  have hrbound:(r:ℝ)<(N:ℝ)^ell*L := by
    rw [her,Nat.cast_mul]
    exact mul_lt_mul heB hdL.le hdpos (Real.rpow_nonneg hn0.le _)
  have hpref:=padded_prefix_product hN box width t ht
  have hp2:(0:ℝ)≤(box.lo 2:ℝ) := by exact_mod_cast (gridBox_lower_positive n j 2).le
  have hcap:cap p (fun i=>(box.lo i:ℝ))≤(153/256:ℝ) := by
    by_cases hp:p.val<15
    · unfold cap
      rw [if_pos hp]
      by_cases hs:selectedMass p (fun i=>(box.lo i:ℝ))≤(25/128:ℝ)
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
    · unfold cap
      rw [if_neg hp]
      linarith
  have hcorner:=U1011OriginalSixteenStaticCellWinner.corner_mem_region box hvalid
  have hnuLower:(U1011OriginalSixteenNearCapBoxProfiles.nu p box eta:ℝ)<(capLower p box:ℝ) := by
    exact_mod_cast hpars.2.1
  have hnu:(U1011OriginalSixteenNearCapBoxProfiles.nu p box eta:ℝ)<(153/256:ℝ) :=
    hnuLower.trans_le ((cap_bounds p box hcorner).1.trans hcap)
  calc
    (((∏i,t i)*r:ℕ):ℝ)=((∏i,t i:ℕ):ℝ)*(r:ℝ) := by rw [Nat.cast_mul]
    _ ≤ (N:ℝ)^((U1011OriginalSixteenNearCapBoxProfiles.Tplus box:ℝ)+4*width)*(r:ℝ) :=
      mul_le_mul_of_nonneg_right hpref (Nat.cast_nonneg r)
    _ < (N:ℝ)^((U1011OriginalSixteenNearCapBoxProfiles.Tplus box:ℝ)+4*width)*((N:ℝ)^ell*L) :=
      mul_lt_mul_of_pos_left hrbound (Real.rpow_pos_of_pos hn0 _)
    _ = (N:ℝ)^((U1011OriginalSixteenNearCapBoxProfiles.nu p box eta:ℝ)+4*width+ell-
        20*(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ)) := by
      dsimp only [L,U1011OriginalSixteenJointNearCapCompiler.rowD]
      rw [←Real.rpow_add hn0,←Real.rpow_add hn0]
      congr 1
      simp only [U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,Rat.cast_sub,
        Rat.cast_mul,Rat.cast_ofNat]
      ring
    _ ≤ (N:ℝ)^(153/256:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      change ell≤(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ)/8 at hell
      change width≤(U1011OriginalSixteenNearCapBoxProfiles.delta p box eta:ℝ)/32 at hwidth
      linarith

end
end ImbalancedChen.P5Z.OriginalPresievedOuterAtomSupport
