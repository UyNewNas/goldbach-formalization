import ImbalancedChen.Part3OriginalMaskedWCoefficientMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 5.

An active-label physical-lcm primitive. Inactive gamma labels are exactly
zero, so their large moduli impose no condition on the decay cap. This
is needed for a genuine point-mass first-factor slice: its original label
carrier is unchanged but only one first factor is active. The inverse
mesh estimate is reused from the actual fixed Schwartz cutoff. No Cauchy,
canonical phase or complete-moment identity is re-proved or assumed.
-/

namespace ImbalancedChen.Part3.OriginalActiveLcmResidual20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff TransposedGCDPoissonMask
open OriginalMaskedWShortModulusBound20261026b OriginalMaskedWCoefficientMass20261026b
open scoped BigOperators

def ActiveLcmCap (d : MediumAtom) (L : ℝ) : Prop :=
  ∀ a ∈ d.complexFactorLabels, ∀ b ∈ d.complexFactorLabels,
    d.complexFactorGamma a ≠ 0 → d.complexFactorGamma b ≠ 0 →
    ∀ n1 ∈ d.transposedAtom.betaCarrier, ∀ n2 ∈ d.transposedAtom.betaCarrier,
      (((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ) : ℝ) ≤ L

theorem original_nonzero_activeLcm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ L : ℝ, 0 ≤ L → ActiveLcmCap d L →
        ‖d.transposedAtom.complexCRTSmoothNonzeroPart‖ ≤
          (C*L/d.V) * ((betaL1 d.transposedAtom)^2 * (gammaL1 d.transposedAtom)^2) := by
  obtain ⟨C,hC,hmesh⟩ := poisson_nonzero_inverse_mesh
  refine ⟨C,hC,fun B sigma kappa c0 d hd L hL0 hcap => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hK : 0 ≤ C*L/d.V := by positivity
  have hfactor (n1 : ℕ) (hn1 : n1 ∈ d.transposedAtom.betaCarrier)
      (n2 : ℕ) (hn2 : n2 ∈ d.transposedAtom.betaCarrier) :
      ‖d.transposedAtom.commonFactorPairNonzeroWeight n1 n2‖ ≤
        (C*L/d.V) * (gammaL1 d.transposedAtom)^2 := by
    unfold MediumAtom.commonFactorPairNonzeroWeight
    calc
      _ ≤ ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
          (C*L/d.V) * (‖d.complexFactorGamma a‖ * ‖d.complexFactorGamma b‖) := by
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
                      n1 n2 d.residue : ℝ) / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ)) h‖ ≤ C*L/d.V := by
                calc
                  _ ≤ C / (d.V / ((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ)) :=
                    hmesh _ (div_pos hV hLc) _
                  _ = C * (((complexFactorModulus a).lcm (complexFactorModulus b) : ℕ) : ℝ) / d.V := by
                    field_simp [hV.ne',hLc.ne']; ring
                  _ ≤ C*L/d.V := div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hlevel hC.le) hV.le
              simp only [hc,if_true]
              rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
              have hh := mul_le_mul_of_nonneg_left
                ((Complex.abs_re_le_norm _).trans hrem)
                (norm_nonneg (d.complexFactorGamma a * star (d.complexFactorGamma b)))
              simpa only [norm_mul,norm_star,mul_comm] using hh
            · simp only [hc,if_false,Complex.ofReal_zero,mul_zero,norm_zero]
              positivity
      _ = (C*L/d.V) * (gammaL1 d.transposedAtom)^2 := by
        simp only [gammaL1,pow_two,Finset.sum_mul_sum,Finset.mul_sum,
          MediumAtom.transposedAtom,mul_assoc]
  rw [complexCRTSmoothNonzeroPart_eq_betaPairs]
  calc
    _ ≤ ∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
        (C*L/d.V) * (‖d.transposedAtom.beta n1‖ * ‖d.transposedAtom.beta n2‖) *
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
    _ = (C*L/d.V) * ((betaL1 d.transposedAtom)^2 * (gammaL1 d.transposedAtom)^2) := by
      simp only [betaL1,pow_two,Finset.sum_mul_sum,Finset.mul_sum,Finset.sum_mul,mul_assoc]

end
end ImbalancedChen.Part3.OriginalActiveLcmResidual20261026b
