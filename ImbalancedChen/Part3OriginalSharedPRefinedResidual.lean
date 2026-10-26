import ImbalancedChen.Part3OriginalActiveLcmResidual
import ImbalancedChen.Part3OriginalSharedWeightedBoundary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 5.

The shared p is active ONCE. Its lcm bound is REUSED from the public
sharedFirstFactor_lcm_le supplier, not re-proved. The original slice
gammaL1 has exactly one active first label, and only the two true tail
label carriers contribute cardinality. All original beta, gamma2,gamma3
coefficients and primitive p carrier remain literal. Outside moments
are the same actual betaL2*gamma1L2. Full spectral 7/32 remains OPEN.
-/

namespace ImbalancedChen.Part3.OriginalSharedPRefinedResidual20261026b
noncomputable section
open Classical Finset OriginalActiveLcmResidual20261026b
open OriginalMaskedWCoefficientMass20261026b OriginalSharedResidualBoundary20261026b
open OriginalSharedWeightedBoundary20261026b
open scoped BigOperators

theorem actual_slice_gammaL1_le_two_tail_carriers
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    gammaL1 (d.q1SliceAtom p).transposedAtom ≤ 4*d.Q2*d.Q3 := by
  have hpf := (Finset.mem_filter.mp hp).1
  have hfirst : (∑ q ∈ factorCarrier d.Q1, ‖(d.q1SliceAtom p).gamma1 q‖) = 1 := by
    simp [MediumAtom.q1SliceAtom,hpf]
  have hsum (Q : ℝ) (g : ℕ → ℂ) (hQ : 1 ≤ Q)
      (hg : ∀ q ∈ factorCarrier Q, ‖g q‖ ≤ 1) :
      (∑ q ∈ factorCarrier Q, ‖g q‖) ≤ 2*Q := by
    have hi := ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one
      (a := Q) (b := 2*Q) (by linarith) (by linarith)
    have hs : (∑ q ∈ factorCarrier Q, ‖g q‖) ≤ ((factorCarrier Q).card : ℝ) := by
      calc
        _ ≤ ∑ _q ∈ factorCarrier Q, (1 : ℝ) := Finset.sum_le_sum hg
        _ = _ := by simp
    change ((factorCarrier Q).card : ℝ) ≤ 2*Q-Q+1 at hi
    linarith
  have hkeep := hd
  obtain ⟨_, _, _, hQ2, hQ3, _, _, _, _, _, _, _, _, _, _, _, h2, h3⟩ := hkeep
  have hs2 := hsum d.Q2 d.gamma2 hQ2 (fun q hq => (h2 q hq).1)
  have hs3 := hsum d.Q3 d.gamma3 hQ3 (fun q hq => (h3 q hq).1)
  change gammaL1 (d.q1SliceAtom p) ≤ 4*d.Q2*d.Q3
  rw [gammaL1_eq_three_original_sums,hfirst,one_mul]
  calc
    _ ≤ (2*d.Q2)*(2*d.Q3) := mul_le_mul hs2 hs3
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by linarith)
    _ = _ := by ring

/-- Activation supplies the exact reduced rows consumed by the existing
single-shared-p lcm theorem. Inactive first labels are not counted. -/
theorem actual_slice_activeLcmCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) :
    ActiveLcmCap (d.q1SliceAtom p) (32*d.Q1*d.Q2^2*d.Q3^2) := by
  intro a ha b hb hga hgb n1 hn1 n2 hn2
  have hfa : a.1 = p := by
    by_contra hne
    apply hga
    simp [MediumAtom.complexFactorGamma,MediumAtom.q1SliceAtom,hne]
  have hfb : b.1 = p := by
    by_contra hne
    apply hgb
    simp [MediumAtom.complexFactorGamma,MediumAtom.q1SliceAtom,hne]
  have hla : (a.2,n1) ∈ d.sharedFirstFactorRows :=
    Finset.mem_product.mpr ⟨(Finset.mem_product.mp ha).2,hn1⟩
  have hlb : (b.2,n2) ∈ d.sharedFirstFactorRows :=
    Finset.mem_product.mpr ⟨(Finset.mem_product.mp hb).2,hn2⟩
  simpa only [complexFactorModulus,hfa,hfb,Nat.mul_assoc] using
    d.sharedFirstFactor_lcm_le hd hp hla hlb

theorem actual_refined_sharedResidual_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
        ‖sharedResidual d‖ ≤ C*d.U^2*d.Q1^2*d.Q2^4*d.Q3^4/d.V := by
  obtain ⟨C,hC,hactive⟩ := original_nonzero_activeLcm_bound
  refine ⟨4096*C,by positivity,fun B sigma kappa c0 d hd => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hQ2 : 0 < d.Q2 := zero_lt_one.trans_le hd.2.2.2.1
  have hQ3 : 0 < d.Q3 := zero_lt_one.trans_le hd.2.2.2.2.1
  have hslice (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖(d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart‖ ≤
        (2048*C)*d.U^2*d.Q1*d.Q2^4*d.Q3^4/d.V := by
    have h := hactive B sigma kappa c0 (d.q1SliceAtom p) (mediumAdmissible_q1SliceAtom hd hp)
      (32*d.Q1*d.Q2^2*d.Q3^2) (by positivity) (actual_slice_activeLcmCap hd hp)
    have hb := (actual_transposed_l1_bounds hd).1
    have hg := actual_slice_gammaL1_le_two_tail_carriers hd hp
    have hb0 : 0 ≤ betaL1 (d.q1SliceAtom p).transposedAtom :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hg0 : 0 ≤ gammaL1 (d.q1SliceAtom p).transposedAtom :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    calc
      _ ≤ (C*(32*d.Q1*d.Q2^2*d.Q3^2)/d.V) *
          ((betaL1 (d.q1SliceAtom p).transposedAtom)^2 *
            (gammaL1 (d.q1SliceAtom p).transposedAtom)^2) := h
      _ ≤ (C*(32*d.Q1*d.Q2^2*d.Q3^2)/d.V) *
          ((2*d.U)^2*(4*d.Q2*d.Q3)^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (pow_le_pow_left₀ hb0 hb 2) (pow_le_pow_left₀ hg0 hg 2)
          (sq_nonneg _) (sq_nonneg _)
      _ = (2048*C)*d.U^2*d.Q1*d.Q2^4*d.Q3^4/d.V := by ring
  have hpCard : (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2*d.Q1 := by
    have hc := Finset.card_le_card (Finset.filter_subset
      (fun p : ℕ => p.Coprime d.residue.natAbs) (factorCarrier d.Q1))
    have hi := ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one
      (a := d.Q1) (b := 2*d.Q1) (by linarith) (by linarith)
    have hh : (d.primitiveFirstFactorCarrier.card : ℝ) ≤ ((factorCarrier d.Q1).card : ℝ) :=
      by exact_mod_cast hc
    change ((factorCarrier d.Q1).card : ℝ) ≤ 2*d.Q1-d.Q1+1 at hi
    linarith [hd.2.2.1]
  unfold sharedResidual
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        ‖(d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier,
        (2048*C)*d.U^2*d.Q1*d.Q2^4*d.Q3^4/d.V := Finset.sum_le_sum hslice
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) *
        ((2048*C)*d.U^2*d.Q1*d.Q2^4*d.Q3^4/d.V) := by simp
    _ ≤ (2*d.Q1)*((2048*C)*d.U^2*d.Q1*d.Q2^4*d.Q3^4/d.V) :=
      mul_le_mul_of_nonneg_right hpCard (by positivity)
    _ = (4096*C)*d.U^2*d.Q1^2*d.Q2^4*d.Q3^4/d.V := by ring

theorem actual_refined_weighted_sharedResidual_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
        originalOutside d * ‖sharedResidual d‖ ≤
          C*d.U^2*d.Q1^3*d.Q2^4*d.Q3^4*originalBetaLogCost B d := by
  obtain ⟨C,hC,hbound⟩ := actual_refined_sharedResidual_bound
  refine ⟨4*C,by positivity,fun B sigma kappa c0 d hd => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hlog : 0 ≤ 1+Real.log (2*d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2*d.V by linarith [hd.2.1])]
  have hout := d.sharedFirstFactor_outside_le hd
  change originalOutside d ≤ 4*d.V*d.Q1*originalBetaLogCost B d at hout
  calc
    _ ≤ (4*d.V*d.Q1*originalBetaLogCost B d) *
        (C*d.U^2*d.Q1^2*d.Q2^4*d.Q3^4/d.V) :=
      mul_le_mul hout (hbound B sigma kappa c0 d hd) (norm_nonneg _)
        (by unfold originalBetaLogCost; positivity)
    _ = (4*C)*d.U^2*d.Q1^3*d.Q2^4*d.Q3^4*originalBetaLogCost B d := by
      field_simp [hV.ne']; ring

end
end ImbalancedChen.Part3.OriginalSharedPRefinedResidual20261026b
