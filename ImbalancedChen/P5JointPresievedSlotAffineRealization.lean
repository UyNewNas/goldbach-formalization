import ImbalancedChen.P5PresievedRoughSlotAffineGates
import ImbalancedChen.P5OriginalJointPresievedArithmeticSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The fixed-rank rough affine dictionary is bound to TRUE explicitly-new
ALL16 jointPresievedSigma, including W. Common beta stays at its original
independent physical level. Original arithmetic support supplies the rank;
no ordinary15 membership, factorability or PP premise is requested.
-/
namespace ImbalancedChen.P5Z.JointPresievedSlotAffineRealization
noncomputable section
open Classical
open scoped BigOperators
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalOrdinaryResidualArithmeticFactor OriginalCommonBetaActualParameters
open OriginalJointPresievedCompiler OriginalJointCommonBetaModel OriginalJointPresievedArithmeticSupport
open OriginalPresievedRoughRank OriginalPresievedRoughPrimeSlots OriginalPresievedRoughSlotCoefficient
open PresievedRoughSlotAffineGates

def slotVector (ps : List ℕ) (i : Fin ps.length) : ℕ := ps[i.val]

theorem ofFn_slotVector (ps : List ℕ) : List.ofFn (slotVector ps) = ps := List.ofFn_getElem

theorem retained_slots_log_region {N cap d : ℕ} (hN : 1 < N) {w Z ell : ℝ}
    (hL : 1 < (N : ℝ) ^ ell)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap w Z) :
    actualPrimeTupleLog N (slotVector (canonicalSlots N cap w Z d)) ∈
      region (canonicalSlots N cap w Z d).length ell := by
  have hp : ∀ i : Fin (canonicalSlots N cap w Z d).length,
      0 < slotVector (canonicalSlots N cap w Z d) i := by
    intro i
    exact (canonicalSlots_prime_data (List.getElem_mem i.isLt)).1.pos
  have hdesc : StrictAnti (slotVector (canonicalSlots N cap w Z d)) := by
    apply List.pairwise_ofFn.mp
    rw [ofFn_slotVector]
    exact canonicalSlots_descending N cap w Z d
  apply (original_upper_prefix_iff_log hN ell _ hp hdesc).mp
  rw [ofFn_slotVector]
  exact canonicalSlots_original_upper_gates hL hd

/-- Genuine ALL16 marks expose a bounded-rank ORIGINAL rough affine
slot vector and its exact original normalized coefficient. The tuple,
small e, rough d and complete q are those of this same new coefficient. -/
theorem actual_jointSigma_slot_affine_realization {n N q : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (nu0 betaEta : ℝ) (hnu : 0 < nu0) (hb : 0 < betaEta)
    (hbudget : betaEta < epsilonBudget n eta nu0) (E : ℕ × ℕ → Prop)
    (hq : jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2))
      ((N : ℝ) ^ (nu0 * betaEta)) E q ≠ 0) :
    ∃ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      ∃ e ∈ actualSmallRosserSupport N
          (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) ((N : ℝ) ^ (nu0 * betaEta ^ 2)),
        ∃ d ∈ fixedRoughSupport (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
            (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
            ((N : ℝ) ^ (nu0 * betaEta ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
          q = fullPrefix t * (e * d) ∧
          d.primeFactors.card ≤ rankBound nu0 betaEta ∧
          (actualPrimeTupleLog N (slotVector (rowSlots n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2)) t d)) ∈
            region (rowSlots n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2)) t d).length
              (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual
                (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t)
                (U1011OriginalSixteenStaticNativeCompiler.ownerBox n N t) eta : ℝ)) ∧
          jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2))
              ((N : ℝ) ^ (nu0 * betaEta)) E q =
            signedSlotCoefficient (rankBound nu0 betaEta) N
              (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
              ((N : ℝ) ^ (nu0 * betaEta ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
              (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d *
            commonSmallWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
              ((N : ℝ) ^ (nu0 * betaEta ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
              (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) ((N : ℝ) ^ (nu0 * betaEta)) d e := by
  have hw (t : Four) (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :=
    (parameters_on_joint_row hN heta hnu hb hbudget ht).1
  have hprofile := actual_joint_arithmetic_support hN heta hnu hb hbudget E hq
  have hmem : q ∈ jointSupport n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2)) E := by
    by_contra hn
    exact hq (jointSigma_zero_off_support n N eta _ _ E hn)
  obtain ⟨a, ha, hmod⟩ := Finset.mem_image.mp hmem
  obtain ⟨ht, hr⟩ := Finset.mem_sigma.mp ha
  have hrow : rowCoefficient n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2))
      ((N : ℝ) ^ (nu0 * betaEta)) a.1 a.2 ≠ 0 := by
    rw [← jointSigma_eq_row hN heta hw ha, hmod]
    exact hq
  have hL := (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1
  obtain ⟨e, he, d, hd, her, heB, hdc⟩ := actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta a.1)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta a.1))
    ((N : ℝ) ^ (nu0 * betaEta ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta a.1)
    ((N : ℝ) ^ (nu0 * betaEta)) hrow
  have hqed : q = fullPrefix a.1 * (e * d) := by rw [← hmod, modulus, her]
  have hepos : 0 < e := Nat.pos_of_ne_zero (actualSmallRosserSupport_squarefree _ _ _ he).ne_zero
  have hpref : 0 < fullPrefix a.1 := by
    rw [fullPrefix_eq_multiplier]
    exact joint_multiplier_pos (Finset.mem_filter.mp ht).1
  have hdq : d ≤ q := by
    rw [hqed]
    nlinarith
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans hn
  have hrho : 0 < roughExponent nu0 betaEta := mul_pos hnu (sq_pos_of_pos hb)
  have hlo := P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta a.1)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta a.1))
    (Real.rpow_nonneg hnpos.le _) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta a.1) hd
  have hdreal : (d : ℝ) ≤ q := by exact_mod_cast hdq
  have hpow : (N : ℝ) ^ (roughExponent nu0 betaEta * (d.primeFactors.card : ℝ)) ≤
      (N : ℝ) ^ (5 / 8 : ℝ) := by
    rw [Real.rpow_mul hnpos.le, Real.rpow_natCast]
    exact hlo.trans (hdreal.trans (hprofile.2.2.2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hn.le (by norm_num))))
  have hrank : d.primeFactors.card ≤ rankBound nu0 betaEta := by
    have hc := (Real.rpow_le_rpow_left_iff hn).mp hpow
    unfold rankBound actualRoughVectorRankBound
    apply (Nat.le_floor_iff (div_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8) hrho.le)).mpr
    apply (le_div_iff₀ hrho).mpr
    simpa only [mul_comm] using hc
  refine ⟨a.1, ht, e, he, d, hd, hqed, hrank, ?_, ?_⟩
  · exact retained_slots_log_region hN hL hd
  · rw [← hmod, jointSigma_eq_row hN heta hw ha, rowCoefficient, her]
    exact presieved_row_eq_signed_slots hL he hd hrank

end
end ImbalancedChen.P5Z.JointPresievedSlotAffineRealization
