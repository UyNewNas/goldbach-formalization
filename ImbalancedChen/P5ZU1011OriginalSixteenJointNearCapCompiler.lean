import ImbalancedChen.P5ZU1011OriginalSixteenJointNativeCompiler
import ImbalancedChen.P5ZU1011OriginalFifteenNearCapNative
import ImbalancedChen.P5ZU1011OriginalSixteenNearCapBoxProfiles

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The actual JOINT native compiler at a rational precision eta fixed BEFORE
N and all tuples. The static corner plan is unchanged, but the support and
coefficient genuinely use the new near-cap residual and cutoff, not the
midpoint family. The profile geometry is reused unchanged. Both literal
source bands have true lowered-cutoff legality and the SAME native rho in
count, reciprocal-totient main, signed AP error and centre correction.
Primitive inputs are the concrete whole-box certificates and eta>0.
No H248/density/AP/PP/fallback-payment licence is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenJointNearCapCompiler
noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalSixteenInteriorArithmetic
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy boxPolicy_certificate ownerBox selectedPolicy tupleTag)
open U1011OriginalSixteenNearCapBoxProfiles (nu delta xi rho physicalResidual cutoffExponent Tplus)
open P5U1011JointOverlap
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

abbrev ordinaryTuples := U1011OriginalSixteenJointNativeCompiler.ordinaryTuples
abbrev fallbackTuples := U1011OriginalSixteenJointNativeCompiler.fallbackTuples

def rowZ (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^(cutoffExponent p B eta:ℝ)
def rowD (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : ℝ := (N:ℝ)^(physicalResidual p B eta:ℝ)
def rowSupport (p : Policy) (B : Box) (eta : ℚ) (N : ℕ) : Finset ℕ :=
  actualSmallRosserSupport N (Nat.ceil (rowZ p B eta N)) (rowZ p B eta N)
def rowCoefficient (p : Policy) (B : Box) (eta : ℚ) (N d : ℕ) : ℝ :=
  actualSmallRosserPlus N (Nat.ceil (rowZ p B eta N)) (rowZ p B eta N) (rowD p B eta N) d

/-- The new all16 physical objects are bound to the actual ordinary-mask
near-cap caller, not merely to its admissible endpoint geometry. -/
theorem ordinary_native_binding (p : Policy) (hp : p.val<15) (B : Box) (eta : ℚ) (N : ℕ) :
    rowZ p B eta N=U1011OriginalFifteenNearCapNative.Z p B eta N ∧
      rowD p B eta N=U1011OriginalFifteenNearCapNative.D p B eta N ∧
      rowSupport p B eta N=U1011OriginalFifteenNearCapNative.support p B eta N ∧
      ∀d,rowCoefficient p B eta N d=U1011OriginalFifteenNearCapNative.coefficient p B eta N d := by
  have hZ : rowZ p B eta N=U1011OriginalFifteenNearCapNative.Z p B eta N := by
    simp only [rowZ,U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent,
      U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,U1011OriginalSixteenNearCapBoxProfiles.nu,
      U1011OriginalSixteenNearCapBoxProfiles.delta,U1011OriginalSixteenNearCapBoxProfiles.xi,
      U1011OriginalSixteenNearCapBoxProfiles.rho,U1011OriginalSixteenNearCapBoxProfiles.G,if_pos hp,
      U1011OriginalFifteenNearCapNative.Z,U1011OriginalFifteenNearCapNative.cutoffExponent,
      U1011OriginalFifteenNearCapNative.residualExponent,U1011OriginalFifteenNearCapNative.nu,
      U1011OriginalFifteenNearCapNative.delta,U1011OriginalFifteenNearCapNative.xi,
      U1011OriginalFifteenNearCapNative.rho,U1011OriginalFifteenNearCapNative.G,
      U1011OriginalFifteenNearCapNative.U,U1011OriginalFifteenNearCapNative.Tplus,
      U1011OriginalSixteenNearCapBoxProfiles.Tplus]
  have hD : rowD p B eta N=U1011OriginalFifteenNearCapNative.D p B eta N := by
    simp only [rowD,U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,
      U1011OriginalSixteenNearCapBoxProfiles.nu,U1011OriginalSixteenNearCapBoxProfiles.delta,
      U1011OriginalSixteenNearCapBoxProfiles.G,if_pos hp,
      U1011OriginalFifteenNearCapNative.D,U1011OriginalFifteenNearCapNative.residualExponent,
      U1011OriginalFifteenNearCapNative.nu,U1011OriginalFifteenNearCapNative.delta,
      U1011OriginalFifteenNearCapNative.G,U1011OriginalFifteenNearCapNative.U,
      U1011OriginalFifteenNearCapNative.Tplus,U1011OriginalSixteenNearCapBoxProfiles.Tplus]
  refine ⟨hZ,hD,?_,?_⟩
  · simp only [rowSupport,hZ,U1011OriginalFifteenNearCapNative.support]
  · intro d
    simp only [rowCoefficient,hZ,hD,U1011OriginalFifteenNearCapNative.coefficient]

/-- W remains its distinct original near-cap family. -/
theorem W_native_binding (B : Box) (eta : ℚ) (N : ℕ) :
    rowZ wPolicy B eta N=U1011OriginalW16NearCapNative.Z B eta N ∧
      rowD wPolicy B eta N=U1011OriginalW16NearCapNative.D B eta N ∧
      rowSupport wPolicy B eta N=U1011OriginalW16NearCapNative.support B eta N ∧
      ∀d,rowCoefficient wPolicy B eta N d=U1011OriginalW16NearCapNative.coefficient B eta N d := by
  have hZ : rowZ wPolicy B eta N=U1011OriginalW16NearCapNative.Z B eta N := by
    simp only [rowZ,U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent,
      U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,U1011OriginalSixteenNearCapBoxProfiles.nu,
      U1011OriginalSixteenNearCapBoxProfiles.delta,U1011OriginalSixteenNearCapBoxProfiles.xi,
      U1011OriginalSixteenNearCapBoxProfiles.rho,U1011OriginalSixteenNearCapBoxProfiles.G,
      U1011OriginalW16NearCapNative.Z,U1011OriginalW16NearCapNative.cutoffExponent,
      U1011OriginalW16NearCapNative.residualExponent,U1011OriginalW16NearCapNative.nu,
      U1011OriginalW16NearCapNative.delta,U1011OriginalW16NearCapNative.xi,
      U1011OriginalW16NearCapNative.rho,U1011OriginalSixteenNearCapBoxProfiles.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus,U1011OriginalW16FixedCellNative.Tplus,
      wPolicy,show ¬(15:ℕ)<15 by omega,if_false]
  have hD : rowD wPolicy B eta N=U1011OriginalW16NearCapNative.D B eta N := by
    simp only [rowD,U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,
      U1011OriginalSixteenNearCapBoxProfiles.nu,U1011OriginalSixteenNearCapBoxProfiles.delta,
      U1011OriginalSixteenNearCapBoxProfiles.G,U1011OriginalW16NearCapNative.D,
      U1011OriginalW16NearCapNative.residualExponent,U1011OriginalW16NearCapNative.nu,
      U1011OriginalW16NearCapNative.delta,U1011OriginalSixteenNearCapBoxProfiles.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus,U1011OriginalW16FixedCellNative.Tplus,
      wPolicy,show ¬(15:ℕ)<15 by omega,if_false]
  refine ⟨hZ,hD,?_,?_⟩
  · simp only [rowSupport,hZ,U1011OriginalW16NearCapNative.support]
  · intro d
    simp only [rowCoefficient,hZ,hD,U1011OriginalW16NearCapNative.coefficient]

/-- Only the elementary rational physical-legality helper is shared;
positivity comes from the actual selected-mask OR W certificate. -/
theorem joint_row_legality {N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {t : Four}
    (ht : t∈jointSelector N E) (p : Policy) (B : Box) (eta : ℚ) (heta : 0<eta)
    (hv : B.Valid) (hw : 0<B.lo 3) (hc : wholeBoxEligibleTest p B=true)
    (hb : coordinates N t∈B.region) :
    0<rowZ p B eta N ∧ 1<rowD p B eta N ∧ rowZ p B eta N≤(t.1.1:ℝ) ∧
      rowZ p B eta N≤rowD p B eta N := by
  have hp := U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p B eta hv hw hc heta
  exact U1011OriginalW16JointNative.joint_physical_legality hN ht B
    (nu p B eta) (delta p B eta) (xi p B eta) (rho p B eta)
    hp.2.2.2.1.le hp.2.2.2.2.1 hp.2.2.2.2.2.1 hb

def Z (n N : ℕ) (eta : ℚ) (t : Four) : ℝ := rowZ (selectedPolicy n N t) (ownerBox n N t) eta N
def D (n N : ℕ) (eta : ℚ) (t : Four) : ℝ := rowD (selectedPolicy n N t) (ownerBox n N t) eta N
def support (n N : ℕ) (eta : ℚ) (t : Four) : Finset ℕ :=
  rowSupport (selectedPolicy n N t) (ownerBox n N t) eta N
def coefficient (n N : ℕ) (eta : ℚ) (t : Four) (d : ℕ) : ℝ :=
  rowCoefficient (selectedPolicy n N t) (ownerBox n N t) eta N d

theorem compiled_static_on_cell (n N : ℕ) (eta : ℚ) {t : Four} {j : Grid n}
    (ht : coordinates N t∈cell n j) :
    support n N eta t=rowSupport (boxPolicy (gridBox n j)) (gridBox n j) eta N ∧
      ∀d,coefficient n N eta t d=rowCoefficient (boxPolicy (gridBox n j)) (gridBox n j) eta N d := by
  have ho := owner_eq_of_mem n ht
  simp only [support,coefficient,selectedPolicy,ownerBox,ho,true_and]

theorem compiled_legality {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {eta : ℚ}
    (heta : 0<eta) {t : Four} (ht : t∈ordinaryTuples n N E) :
    0<Z n N eta t ∧ 1<D n N eta t ∧ Z n N eta t≤(t.1.1:ℝ) ∧ Z n N eta t≤D n N eta t := by
  obtain ⟨hs,hne⟩ := Finset.mem_filter.mp ht
  have hc := (boxPolicy_certificate (ownerBox n N t) hne).2
  have hg := owner_mem n (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs)
  exact joint_row_legality hN hs _ _ eta heta (gridBox_valid n _) (gridBox_lower_positive n _ 3)
    hc (cell_subset_closed_box n _ hg)

theorem joint_row_active_full_modulus_cap {N d : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop}
    {t : Four} (ht : t∈jointSelector N E) (p : Policy) (B : Box) (eta : ℚ)
    (hb : coordinates N t∈B.region) (hd : rowCoefficient p B eta N d≠0) :
    ((fullPrefix t*d:ℕ):ℝ)<(N:ℝ)^((nu p B eta:ℝ)-20*(delta p B eta:ℝ)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := zero_lt_one.trans hn
  have hs : U11SelectedLargest.prefixSum (coordinates N t)≤(Tplus B:ℝ) := by
    simp only [U11SelectedLargest.prefixSum,U1011OriginalSixteenNearCapBoxProfiles.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus,Rat.cast_add]
    linarith [hb.2 0,hb.2 1,hb.2 2,hb.2 3]
  have hprod : (fullPrefix t:ℝ)≤(N:ℝ)^(Tplus B:ℝ) := by
    rw [←fullPrefix_rpow hN ht]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hs
  have hactive : (d:ℝ)<rowD p B eta N := (actualSmallRosserPlus_active hd).2.1
  rw [Nat.cast_mul]
  calc
    (fullPrefix t:ℝ)*d≤(N:ℝ)^(Tplus B:ℝ)*d := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _)
    _ < (N:ℝ)^(Tplus B:ℝ)*rowD p B eta N := mul_lt_mul_of_pos_left hactive (Real.rpow_pos_of_pos hn0 _)
    _ = _ := by
      rw [rowD,←Real.rpow_add hn0]
      congr 1
      simp only [U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
      ring

def main (n N : ℕ) (eta : ℚ) (t : Four) : ℝ := trueLogarithmicIntegral N/(Nat.totient (fullPrefix t):ℝ)*
  actualSmallRosserPlusDensity N (Nat.ceil (Z n N eta t)) (Z n N eta t) (D n N eta t)
def signedAP (n N : ℕ) (eta : ℚ) (t : Four) : ℝ := ∑d∈support n N eta t,coefficient n N eta t d*
  chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (fullPrefix t*d)
def signedCentre (n N : ℕ) (eta : ℚ) (t : Four) : ℝ := ∑d∈support n N eta t,coefficient n N eta t d*
  chenCentrePrimeAPCount N N (fullPrefix t*d)
def estimator (n N : ℕ) (eta : ℚ) (t : Four) : ℝ := ∑d∈support n N eta t,coefficient n N eta t d*
  (chenPrimeAPCount N N (fullPrefix t*d)-chenCentrePrimeAPCount N N (fullPrefix t*d))

theorem compiled_estimator_identity {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {eta : ℚ}
    (heta : 0<eta) {t : Four} (ht : t∈ordinaryTuples n N E) :
    estimator n N eta t=main n N eta t+signedAP n N eta t-signedCentre n N eta t := by
  have hs := (Finset.mem_filter.mp ht).1
  have hl := compiled_legality hN heta ht
  have hz : Z n N eta t≤(slots t 3:ℝ) := by simpa only [slots,Matrix.cons_val_three] using hl.2.2.1
  exact currentChen_quotient_actualRosser_plus_main_and_errors N (fullPrefix t)
    (Nat.ceil (Z n N eta t)) (Z n N eta t) (D n N eta t) (Nat.le_ceil _) (fullPrefix_coprime_lowered_sieve hs hz)

theorem compiled_row_upper {n N : ℕ} (hN : 1<N) {E : ℕ×ℕ→Prop} {eta : ℚ}
    (heta : 0<eta) {t : Four} (ht : t∈ordinaryTuples n N E) :
    U11Adaptive.weight N t≤main n N eta t+signedAP n N eta t-signedCentre n N eta t := by
  have hs := (Finset.mem_filter.mp ht).1
  have hl := compiled_legality hN heta ht
  have h12 := (joint_carrier_order hs).2.2.2.2.1
  have hz2 : Z n N eta t≤(t.1.2:ℝ) := hl.2.2.1.trans (by exact_mod_cast h12.le)
  have hw : U11Adaptive.weight N t=((chenSiftedQuotientPrimeSource N (fullPrefix t) (t.1.2:ℝ)).card:ℝ) := by
    rw [fullPrefix_eq_multiplier];rfl
  have hcount : U11Adaptive.weight N t≤((chenSiftedQuotientPrimeSource N (fullPrefix t) (Z n N eta t)).card:ℝ) := by
    rw [hw]
    exact_mod_cast Finset.card_le_card (U11LoweredRosser.siftedSource_subset_lowered N _ _ _ hz2)
  have hu := currentChen_quotient_actualRosser_upper N (fullPrefix t) (Nat.ceil (Z n N eta t))
    (Z n N eta t) (D n N eta t) (Nat.le_ceil _) hl.2.1 hl.2.2.2
  exact (hcount.trans hu).trans_eq (compiled_estimator_identity hN heta ht)

theorem original_joint_source_upper {n N : ℕ} (hN : 1<N) (E : ℕ×ℕ→Prop) {eta : ℚ} (heta : 0<eta) :
    currentChenUpsilon10 N+currentChenUpsilon11 N E≤(∑t∈fallbackTuples n N E,U11Adaptive.weight N t)+
      ∑t∈ordinaryTuples n N E,main n N eta t+signedAP n N eta t-signedCentre n N eta t := by
  rw [U1011OriginalFifteenJointNativeRows.joint_count_identity hN E,
    U1011OriginalSixteenJointNativeCompiler.source_partition n N E]
  apply add_le_add_left
  exact Finset.sum_le_sum (fun t ht=>compiled_row_upper hN heta ht)

end
end ImbalancedChen.P5Z.U1011OriginalSixteenJointNearCapCompiler
