import ImbalancedChen.P5OriginalPresievedOuterDensitySeparation
import ImbalancedChen.P5JointPresievedSlotAffineRealization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

An independently smoothed outer prefix need not be an original joint mark.
Its frozen row nevertheless has a fixed-before-N bounded rough-slot model.
The literal selected-cell support bound, applied to the empty multiplier,
supplies the rank; no original tuple provenance or factorability is assumed.
The common beta sign and level are those of the SAME frozen coefficient.
-/

namespace ImbalancedChen.P5Z.OriginalIndependentFrozenSlotRealization
noncomputable section
open Classical
open scoped BigOperators
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenCommonSmallParameters (selectedCells mem_selectedCells)
open OriginalOrdinaryCommonBetaModel OriginalPresievedOuterAtomSupport
open OriginalPresievedOuterAtomArithmetic OriginalPresievedOuterAtomCoefficient
open OriginalCommonBetaActualParameters OriginalPresievedRoughRank
open OriginalPresievedRoughPrimeSlots OriginalPresievedRoughSlotCoefficient
open JointPresievedSlotAffineRealization PresievedRoughSlotAffineGates

private theorem selected_row_positive {n N:ℕ} {eta:ℚ} (hN:1<N) (heta:0<eta)
    (j:Grid n) (hj:j∈selectedCells n) :
    1<U1011OriginalSixteenJointNearCapCompiler.rowD
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta N ∧
    0<(U1011OriginalSixteenNearCapBoxProfiles.delta
      (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta:ℝ) := by
  have hcert:=(U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate (gridBox n j)
    ((mem_selectedCells j).mp hj)).2
  have hpars:=U1011OriginalSixteenNearCapBoxProfiles.rational_parameters
    (U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)) (gridBox n j) eta
    (gridBox_valid n j) (gridBox_lower_positive n j 3) hcert heta
  constructor
  · apply Real.one_lt_rpow (by exact_mod_cast hN)
    exact_mod_cast hpars.2.2.2.2.2.1
  · exact_mod_cast hpars.2.2.1

/-- This is the outside-source frozen-row analogue of the genuine joint
slot theorem. The cap, rank, actual upper gates, and coefficient identity
are all derived, including r=1 and rough rank zero. -/
theorem actual_independent_frozen_slot_realization {n N r:ℕ} {eta:ℚ}
    (hN:1<N) (heta:0<eta) (nu epsilon:ℝ) (hnu:0<nu) (he:0<epsilon)
    (heBudget:epsilon<epsilonBudget n eta nu) (j:Grid n) (hj:j∈selectedCells n)
    (hr:frozenCoefficient n eta j N ((N:ℝ)^(nu*epsilon^2)) (nu*epsilon) r≠0) :
    let p:=U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)
    let z:=U1011OriginalSixteenJointNearCapCompiler.rowZ p (gridBox n j) eta N
    let L:=U1011OriginalSixteenJointNearCapCompiler.rowD p (gridBox n j) eta N
    let w:=(N:ℝ)^(nu*epsilon^2)
    ∃e∈actualSmallRosserSupport N (Nat.ceil z) w,
      ∃d∈fixedRoughSupport (ordinaryRetainOdd L) N (Nat.ceil z) w z,
        r=e*d ∧ (e:ℝ)<(N:ℝ)^(nu*epsilon) ∧
        let ps:=canonicalSlots N (Nat.ceil z) w z d
        ps.Pairwise (· > ·) ∧ ps.Nodup ∧ ps.prod=d ∧ ps.length≤rankBound nu epsilon ∧
        (∀p∈ps,Nat.Prime p ∧ ¬p∣N ∧ w≤(p:ℝ) ∧ (p:ℝ)<z) ∧
        ps∈rankedOrderedSlots (rankBound nu epsilon) N (Nat.ceil z) w z L ∧
        actualPrimeTupleLog N (slotVector ps) ∈ region ps.length
          (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p (gridBox n j) eta:ℝ) ∧
        frozenCoefficient n eta j N w (nu*epsilon) r=
          signedSlotCoefficient (rankBound nu epsilon) N (Nat.ceil z) w z L d *
            commonSmallWeight N (Nat.ceil z) w z L ((N:ℝ)^(nu*epsilon)) d e := by
  let p:=U1011OriginalSixteenStaticNativeCompiler.boxPolicy (gridBox n j)
  let z:=U1011OriginalSixteenJointNearCapCompiler.rowZ p (gridBox n j) eta N
  let L:=U1011OriginalSixteenJointNearCapCompiler.rowD p (gridBox n j) eta N
  let w:=(N:ℝ)^(nu*epsilon^2)
  have hpos:=selected_row_positive hN heta j hj
  have hL:1<L:=hpos.1
  have hn:(1:ℝ)<N:=by exact_mod_cast hN
  have hn0:(0:ℝ)<N:=zero_lt_one.trans hn
  have hparams:=common_parameters_on_selected_cell hN hnu he heBudget j hj
  obtain ⟨e,heS,d,hd,her,heB,hdc⟩:=actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd L) N (Nat.ceil z) w z ((N:ℝ)^(nu*epsilon)) hr
  have hrCap:(r:ℝ)<(N:ℝ)^(153/256:ℝ):=by
    have hunit:∀i:Fin 4,((1:ℕ):ℝ)≤(N:ℝ)^(((gridBox n j).hi i:ℝ)+0):=by
      intro i
      apply Real.one_le_rpow hn.le
      have hhi:0≤(gridBox n j).hi i:=
        (gridBox_lower_positive n j i).le.trans (gridBox_valid n j i)
      have hhiR:(0:ℝ)≤((gridBox n j).hi i:ℝ):=by exact_mod_cast hhi
      simpa only [add_zero] using hhiR
    simpa only [Finset.prod_const_one,one_mul] using
      actual_padded_physical_support hN heta j hj w (nu*epsilon) 0 hparams.2
        (by linarith [hpos.2]) (fun _:Fin 4=>1) hunit hr
  have hepos:0<e:=Nat.pos_of_ne_zero (actualSmallRosserSupport_squarefree _ _ _ heS).ne_zero
  have hdr:d≤r:=by rw [her]; nlinarith
  have hdreal:(d:ℝ)≤r:=by exact_mod_cast hdr
  have hrho:0<roughExponent nu epsilon:=mul_pos hnu (sq_pos_of_pos he)
  have hlo:=P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
    (ordinaryRetainOdd L) N (Nat.ceil z) (Real.rpow_nonneg hn0.le _) z hd
  have hpow:(N:ℝ)^(roughExponent nu epsilon*(d.primeFactors.card:ℝ))≤(N:ℝ)^(5/8:ℝ):=by
    rw [Real.rpow_mul hn0.le,Real.rpow_natCast]
    exact hlo.trans (hdreal.trans (hrCap.le.trans
      (Real.rpow_le_rpow_of_exponent_le hn.le (by norm_num))))
  have hrank:d.primeFactors.card≤rankBound nu epsilon:=by
    have hc:=(Real.rpow_le_rpow_left_iff hn).mp hpow
    unfold rankBound actualRoughVectorRankBound
    apply (Nat.le_floor_iff (div_nonneg (by norm_num:(0:ℝ)≤5/8) hrho.le)).mpr
    apply (le_div_iff₀ hrho).mpr
    simpa only [mul_comm] using hc
  refine ⟨e,heS,d,hd,her,heB,canonicalSlots_descending _ _ _ _ _,
    canonicalSlots_nodup _ _ _ _ _,canonicalSlots_prod hd,?_,?_,
    canonicalSlots_mem_ranked hL hd hrank,?_,?_⟩
  · rw [canonicalSlots_length hd]
    exact hrank
  · intro q hq
    exact canonicalSlots_prime_data hq
  · exact retained_slots_log_region hN hL hd
  · rw [her]
    exact presieved_row_eq_signed_slots hL heS hd hrank

end
end ImbalancedChen.P5Z.OriginalIndependentFrozenSlotRealization
