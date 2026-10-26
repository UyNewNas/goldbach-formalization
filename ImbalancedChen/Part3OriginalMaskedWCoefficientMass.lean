import ImbalancedChen.Part3OriginalMaskedWShortModulusBound
import ImbalancedChen.Part3ElementaryE1RealEndpoint

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 3.

The actual retained coefficient mass is now paid. The beta on the
transposed paired side is ORIGINAL alpha extended by zero, not original
divisor-bounded beta. Gamma is the original product of THREE coefficients.
The count is the cardinality of the THREE-LABEL product carrier, including
all factorizations of equal physical moduli. No prime restriction or
distinct-modulus count is substituted. The interval-point estimate is
reused from the public exact finite-interval supplier.
-/

namespace ImbalancedChen.Part3.OriginalMaskedWCoefficientMass20261026b
noncomputable section
open Classical Finset OriginalMaskedWShortModulusBound20261026b
open scoped BigOperators

def betaL1 (d : MediumAtom) : ℝ := ∑ n ∈ d.betaCarrier, ‖d.beta n‖
def gammaL1 (d : MediumAtom) : ℝ := ∑ a ∈ d.complexFactorLabels, ‖d.complexFactorGamma a‖

/-- The masks are kept in retainedMass and enlarged only in this proved
majorization. It does not change the signed source expression. -/
theorem retainedMass_le_actual_l1_energies (d : MediumAtom) (Y D : ℝ) :
    retainedMass d Y D ≤ (betaL1 d)^2 * (gammaL1 d)^2 := by
  have hfactor (n1 n2 : ℕ) : factorMass d D n1 n2 ≤ (gammaL1 d)^2 := by
    unfold factorMass
    calc
      _ ≤ ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
          ‖d.complexFactorGamma a‖ * ‖d.complexFactorGamma b‖ := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        split_ifs <;> simp only [norm_mul, norm_star] <;> positivity
      _ = (gammaL1 d)^2 := by
        simp only [gammaL1, pow_two, Finset.sum_mul_sum]
  unfold retainedMass
  calc
    _ ≤ ∑ n1 ∈ d.betaCarrier, ∑ n2 ∈ d.betaCarrier,
        (‖d.beta n1‖ * ‖d.beta n2‖) * (gammaL1 d)^2 := by
      apply Finset.sum_le_sum
      intro n1 hn1
      apply Finset.sum_le_sum
      intro n2 hn2
      split_ifs
      · positivity
      · simpa only [norm_mul, norm_star] using
          mul_le_mul_of_nonneg_left (hfactor n1 n2)
            (norm_nonneg (d.beta n1 * star (d.beta n2)))
    _ = (betaL1 d)^2 * (gammaL1 d)^2 := by
      simp only [betaL1, pow_two, Finset.sum_mul_sum, Finset.sum_mul]

/-- Exact factorization of the ORIGINAL labelled L1 sum. Multiplicities
are retained as labels, not bounded by the number of distinct moduli. -/
theorem gammaL1_eq_three_original_sums (d : MediumAtom) :
    gammaL1 d = (∑ q ∈ factorCarrier d.Q1, ‖d.gamma1 q‖) *
      ((∑ q ∈ factorCarrier d.Q2, ‖d.gamma2 q‖) *
        (∑ q ∈ factorCarrier d.Q3, ‖d.gamma3 q‖)) := by
  simp only [gammaL1, MediumAtom.complexFactorLabels, MediumAtom.complexFactorGamma,
    Finset.sum_product, norm_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem actual_transposed_l1_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    betaL1 d.transposedAtom ≤ 2*d.U ∧ gammaL1 d.transposedAtom ≤ d.physicalFactorCap := by
  have hcard (Q : ℝ) (hQ : 1 ≤ Q) : ((factorCarrier Q).card : ℝ) ≤ 2*Q := by
    have h := ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one
      (a := Q) (b := 2*Q) (by linarith) (by linarith)
    change ((factorCarrier Q).card : ℝ) ≤ 2*Q-Q+1 at h
    linarith
  have hbeta : betaL1 d.transposedAtom ≤ 2*d.U := by
    have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
      exact hAlpha
    calc
      _ ≤ ∑ _n ∈ d.transposedAtom.betaCarrier, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        change ‖if n ∈ d.alphaCarrier then d.alpha n else 0‖ ≤ 1
        split_ifs with hn
        · exact hAlpha n hn
        · simp
      _ = ((factorCarrier d.U).card : ℝ) := by simp [MediumAtom.transposedAtom_betaCarrier]
      _ ≤ 2*d.U := hcard d.U hd.1
  have hsum (Q : ℝ) (g : ℕ → ℂ)
      (hg : ∀ q ∈ factorCarrier Q, ‖g q‖ ≤ 1) :
      (∑ q ∈ factorCarrier Q, ‖g q‖) ≤ ((factorCarrier Q).card : ℝ) := by
    calc
      _ ≤ ∑ _q ∈ factorCarrier Q, (1 : ℝ) := Finset.sum_le_sum hg
      _ = _ := by simp
  have hkeep := hd
  obtain ⟨_, _, hQ1, hQ2, hQ3, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hkeep
  have hs1 := hsum d.Q1 d.gamma1 (fun q hq => (h1 q hq).1)
  have hs2 := hsum d.Q2 d.gamma2 (fun q hq => (h2 q hq).1)
  have hs3 := hsum d.Q3 d.gamma3 (fun q hq => (h3 q hq).1)
  have hgamma : gammaL1 d.transposedAtom ≤ d.physicalFactorCap := by
    change gammaL1 d ≤ d.physicalFactorCap
    rw [gammaL1_eq_three_original_sums]
    calc
      _ ≤ ((factorCarrier d.Q1).card : ℝ) *
          (((factorCarrier d.Q2).card : ℝ) * ((factorCarrier d.Q3).card : ℝ)) :=
        mul_le_mul hs1
          (mul_le_mul hs2 hs3 (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
            (Nat.cast_nonneg _))
          (mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
            (Finset.sum_nonneg (fun _ _ => norm_nonneg _))) (Nat.cast_nonneg _)
      _ ≤ (2*d.Q1) * ((2*d.Q2) * (2*d.Q3)) :=
        mul_le_mul (hcard d.Q1 hQ1)
          (mul_le_mul (hcard d.Q2 hQ2) (hcard d.Q3 hQ3)
            (Nat.cast_nonneg _) (by linarith))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
      _ = d.physicalFactorCap := by unfold MediumAtom.physicalFactorCap; ring
  exact ⟨hbeta,hgamma⟩

/-- Complete explicit mass payment on the ORIGINAL transposed source. -/
theorem actual_retainedMass_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Y D : ℝ) :
    retainedMass d.transposedAtom Y D ≤ 4*d.U^2*d.physicalFactorCap^2 := by
  obtain ⟨hb,hg⟩ := actual_transposed_l1_bounds hd
  have hb0 : 0 ≤ betaL1 d.transposedAtom := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hg0 : 0 ≤ gammaL1 d.transposedAtom := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (betaL1 d.transposedAtom)^2 * (gammaL1 d.transposedAtom)^2 :=
      retainedMass_le_actual_l1_energies _ Y D
    _ ≤ (2*d.U)^2 * d.physicalFactorCap^2 :=
      mul_le_mul (pow_le_pow_left₀ hb0 hb 2) (pow_le_pow_left₀ hg0 hg 2)
        (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalMaskedWCoefficientMass20261026b
