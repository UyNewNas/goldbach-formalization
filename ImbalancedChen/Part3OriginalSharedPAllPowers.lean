import ImbalancedChen.Part3OriginalPoissonAllInversePowers
import ImbalancedChen.Part3OriginalSharedPRefinedResidual

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 6.
All-power active-lcm bound for the ACTUAL original source. The same
active original labels and the actual original Fourier kernel remain.
The fixed integer k precedes all atoms and coefficients. No spectral
estimate is an input. Full retained 7/32 remains OPEN.
-/
namespace ImbalancedChen.Part3.OriginalSharedPAllPowers20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff TransposedGCDPoissonMask
open OriginalActiveLcmResidual20261026b OriginalMaskedWCoefficientMass20261026b
open OriginalSharedPRefinedResidual20261026b OriginalSharedResidualBoundary20261026b
open OriginalSharedWeightedBoundary20261026b
open scoped BigOperators
theorem original_nonzero_activeLcm_allpowers (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ L : ℝ, 0 ≤ L → ActiveLcmCap d L →
        ‖d.transposedAtom.complexCRTSmoothNonzeroPart‖ ≤
          (C*(L/d.V)^k) * ((betaL1 d.transposedAtom)^2 * (gammaL1 d.transposedAtom)^2) := by
  obtain ⟨C,hC,hmesh⟩ := OriginalPoissonAllInversePowers20261026b.original_poisson_nonzero_all_inverse_powers k
  refine ⟨C,hC,fun B sigma kappa c0 d hd L hL0 hcap => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hK : 0 ≤ C*(L/d.V)^k := by positivity
  have hfactor (n1 : ℕ) (hn1 : n1 ∈ d.transposedAtom.betaCarrier)
      (n2 : ℕ) (hn2 : n2 ∈ d.transposedAtom.betaCarrier) :
      ‖d.transposedAtom.commonFactorPairNonzeroWeight n1 n2‖ ≤
        (C*(L/d.V)^k) * (gammaL1 d.transposedAtom)^2 := by
    unfold MediumAtom.commonFactorPairNonzeroWeight
    calc
      _ ≤ ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
          (C*(L/d.V)^k) * (‖d.complexFactorGamma a‖ * ‖d.complexFactorGamma b‖) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro a ha
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro b hb
        by_cases hga : d.complexFactorGamma a = 0
        · simp [hga]
        · by_cases hgb : d.complexFactorGamma b = 0
          · simp [hgb]
          · by_cases hc : ComplexCRT.Compatible (complexFactorModulus a) (complexFactorModulus b) n1 n2
            · have hqa := Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
                (Finset.mem_image_of_mem _ ha))
              have hqb := Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
                (Finset.mem_image_of_mem _ hb))
              have hLc : (0 : ℝ) < ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ) := by
                exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hqa.1.ne' hqb.1.ne')
              have hlevel := hcap a ha b hb hga hgb n1 hn1 n2 hn2
              have hrem :
                  ‖∑' h : ℤ, poissonNonzeroFrequency
                    (d.V / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ))
                    ((ComplexCRT.residue (complexFactorModulus a) (complexFactorModulus b)
                      n1 n2 d.residue : ℝ) / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ)) h‖ ≤ C*(L/d.V)^k := by
                calc
                  _ ≤ C / (d.V / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ))^k :=
                    hmesh _ (div_pos hV hLc) _
                  _ = C * ((((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ) : ℝ) / d.V)^k := by
                    simp only [div_pow,div_div]; ring
                  _ ≤ C*(L/d.V)^k := mul_le_mul_of_nonneg_left
                    (pow_le_pow_left₀ (div_nonneg hLc.le hV.le)
                      (div_le_div_of_nonneg_right hlevel hV.le) k) hC.le
              simp only [hc,if_true]
              rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
              have hh := mul_le_mul_of_nonneg_left
                ((Complex.abs_re_le_norm _).trans hrem)
                (norm_nonneg (d.complexFactorGamma a * star (d.complexFactorGamma b)))
              simpa only [norm_mul,norm_star,mul_comm] using hh
            · simp only [hc,if_false,Complex.ofReal_zero,mul_zero,norm_zero]
              positivity
      _ = (C*(L/d.V)^k) * (gammaL1 d.transposedAtom)^2 := by
        simp only [gammaL1,pow_two,Finset.sum_mul_sum,Finset.mul_sum,
          MediumAtom.transposedAtom,mul_assoc]
  rw [complexCRTSmoothNonzeroPart_eq_betaPairs]
  calc
    _ ≤ ∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
        (C*(L/d.V)^k) * (‖d.transposedAtom.beta n1‖ * ‖d.transposedAtom.beta n2‖) *
          (gammaL1 d.transposedAtom)^2 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n1 hn1
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n2 hn2
      rw [norm_mul]
      have hh := mul_le_mul_of_nonneg_left (hfactor n1 hn1 n2 hn2)
        (norm_nonneg (d.transposedAtom.beta n1 * star (d.transposedAtom.beta n2)))
      simpa only [norm_mul,norm_star,mul_assoc,mul_comm,mul_left_comm] using hh
    _ = (C*(L/d.V)^k) * ((betaL1 d.transposedAtom)^2 * (gammaL1 d.transposedAtom)^2) := by
      simp only [betaL1,pow_two,Finset.sum_mul_sum,Finset.mul_sum,Finset.sum_mul,mul_assoc]

def sharedPhysicalLcmCap (d : MediumAtom) : ℝ := 32*d.Q1*d.Q2^2*d.Q3^2

theorem original_shared_weighted_allpowers (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
        originalOutside d * ‖sharedResidual d‖ ≤
          C*d.V*d.U^2*d.Q1^2*d.Q2^2*d.Q3^2*originalBetaLogCost B d *
            (sharedPhysicalLcmCap d/d.V)^k := by
  obtain ⟨C,hC,hactive⟩ := original_nonzero_activeLcm_allpowers k
  refine ⟨512*C,by positivity,fun B sigma kappa c0 d hd => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hQ2 : 0 < d.Q2 := zero_lt_one.trans_le hd.2.2.2.1
  have hQ3 : 0 < d.Q3 := zero_lt_one.trans_le hd.2.2.2.2.1
  have hcap0 : 0 ≤ sharedPhysicalLcmCap d := by unfold sharedPhysicalLcmCap; positivity
  have hslice (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖(d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart‖ ≤
        (64*C)*d.U^2*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k := by
    have h := hactive B sigma kappa c0 (d.q1SliceAtom p) (mediumAdmissible_q1SliceAtom hd hp)
      (sharedPhysicalLcmCap d) hcap0 (actual_slice_activeLcmCap hd hp)
    have hb := (actual_transposed_l1_bounds hd).1
    have hg := actual_slice_gammaL1_le_two_tail_carriers hd hp
    have hb0 : 0 ≤ betaL1 (d.q1SliceAtom p).transposedAtom :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hg0 : 0 ≤ gammaL1 (d.q1SliceAtom p).transposedAtom :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    calc
      _ ≤ (C*(sharedPhysicalLcmCap d/d.V)^k) *
          ((betaL1 (d.q1SliceAtom p).transposedAtom)^2 *
            (gammaL1 (d.q1SliceAtom p).transposedAtom)^2) := h
      _ ≤ (C*(sharedPhysicalLcmCap d/d.V)^k)*((2*d.U)^2*(4*d.Q2*d.Q3)^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (pow_le_pow_left₀ hb0 hb 2) (pow_le_pow_left₀ hg0 hg 2)
          (sq_nonneg _) (sq_nonneg _)
      _ = (64*C)*d.U^2*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k := by ring
  have hpCard : (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2*d.Q1 := by
    have hc := Finset.card_le_card (Finset.filter_subset
      (fun p : ℕ => p.Coprime d.residue.natAbs) (factorCarrier d.Q1))
    have hi := ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one
      (a := d.Q1) (b := 2*d.Q1) (by linarith) (by linarith)
    have hh : (d.primitiveFirstFactorCarrier.card : ℝ) ≤ ((factorCarrier d.Q1).card : ℝ) :=
      by exact_mod_cast hc
    change ((factorCarrier d.Q1).card : ℝ) ≤ 2*d.Q1-d.Q1+1 at hi
    linarith [hd.2.2.1]
  have hshared : ‖sharedResidual d‖ ≤
      (128*C)*d.U^2*d.Q1*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k := by
    unfold sharedResidual
    calc
      _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
          ‖(d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier,
          (64*C)*d.U^2*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k := Finset.sum_le_sum hslice
      _ = (d.primitiveFirstFactorCarrier.card : ℝ) *
          ((64*C)*d.U^2*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k) := by simp
      _ ≤ (2*d.Q1)*((64*C)*d.U^2*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k) :=
        mul_le_mul_of_nonneg_right hpCard (by positivity)
      _ = (128*C)*d.U^2*d.Q1*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k := by ring
  have hlog : 0 ≤ 1+Real.log (2*d.V) := by
    linarith [Real.log_nonneg (show 1 ≤ 2*d.V by linarith [hd.2.1])]
  have hout := d.sharedFirstFactor_outside_le hd
  change originalOutside d ≤ 4*d.V*d.Q1*originalBetaLogCost B d at hout
  calc
    _ ≤ (4*d.V*d.Q1*originalBetaLogCost B d) *
        ((128*C)*d.U^2*d.Q1*d.Q2^2*d.Q3^2*(sharedPhysicalLcmCap d/d.V)^k) :=
      mul_le_mul hout hshared (norm_nonneg _) (by unfold originalBetaLogCost; positivity)
    _ = (512*C)*d.V*d.U^2*d.Q1^2*d.Q2^2*d.Q3^2*originalBetaLogCost B d *
        (sharedPhysicalLcmCap d/d.V)^k := by ring

/-- The fixed all-power gain pays a completely explicit original
polynomial source/outside budget. The only enlargement is x^4. -/
theorem original_shared_weighted_allpowers_scale (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      0 < sigma → MediumAdmissible B sigma kappa c0 d →
        originalOutside d * ‖sharedResidual d‖ ≤ C*d.scale^4*originalBetaLogCost B d *
          (sharedPhysicalLcmCap d/d.V)^k := by
  obtain ⟨C,hC,hbound⟩ := original_shared_weighted_allpowers k
  refine ⟨C,hC,fun B sigma kappa c0 d hsigma hd => ?_⟩
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ1 : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hQ2 : 0 < d.Q2 := zero_lt_one.trans_le hd.2.2.2.1
  have hQ3 : 0 < d.Q3 := zero_lt_one.trans_le hd.2.2.2.2.1
  have hx0 : 0 < d.scale := by unfold MediumAtom.scale; positivity
  have hcap := TransposedPrimitiveUPayment.physicalFactorCap_le_eight_scale hsigma hd
  have hprod : d.Q1*d.Q2*d.Q3 ≤ d.scale := by
    unfold MediumAtom.physicalFactorCap at hcap
    nlinarith
  have hp2 : d.Q1^2*d.Q2^2*d.Q3^2 ≤ d.scale^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ d.Q1*d.Q2*d.Q3) hprod 2
    simpa only [mul_pow] using h
  have huv : d.V*d.U^2 ≤ d.scale^2 := by
    calc
      _ ≤ d.V^2*d.U^2 := mul_le_mul_of_nonneg_right (by nlinarith [hd.2.1]) (sq_nonneg _)
      _ = _ := by unfold MediumAtom.scale; ring
  have hpoly : d.V*d.U^2*d.Q1^2*d.Q2^2*d.Q3^2 ≤ d.scale^4 := by
    calc
      _ = (d.V*d.U^2)*(d.Q1^2*d.Q2^2*d.Q3^2) := by ring
      _ ≤ d.scale^2*d.scale^2 := mul_le_mul huv hp2 (by positivity) (sq_nonneg _)
      _ = _ := by ring
  have hlog : 0 ≤ originalBetaLogCost B d := by
    unfold originalBetaLogCost
    have hb : 0 ≤ 1+Real.log (2*d.V) := by
      linarith [Real.log_nonneg (show 1 ≤ 2*d.V by linarith [hd.2.1])]
    exact pow_nonneg hb _
  have hratio : 0 ≤ (sharedPhysicalLcmCap d/d.V)^k := by unfold sharedPhysicalLcmCap; positivity
  calc
    _ ≤ C*d.V*d.U^2*d.Q1^2*d.Q2^2*d.Q3^2*originalBetaLogCost B d *
        (sharedPhysicalLcmCap d/d.V)^k := hbound B sigma kappa c0 d hd
    _ = (C*(d.V*d.U^2*d.Q1^2*d.Q2^2*d.Q3^2)) *
        (originalBetaLogCost B d*(sharedPhysicalLcmCap d/d.V)^k) := by ring
    _ ≤ (C*d.scale^4)*(originalBetaLogCost B d*(sharedPhysicalLcmCap d/d.V)^k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC.le) (mul_nonneg hlog hratio)
    _ = C*d.scale^4*originalBetaLogCost B d*(sharedPhysicalLcmCap d/d.V)^k := by ring

end
end ImbalancedChen.Part3.OriginalSharedPAllPowers20261026b
