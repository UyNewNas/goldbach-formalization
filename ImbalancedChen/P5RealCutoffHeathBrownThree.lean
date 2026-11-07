import ImbalancedChen.P5RealTruncatedMobiusSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal order-three Heath--Brown coefficient identity at a REAL
closed cutoff. The primary identities zeta*Lambda=log and zeta*mu=delta
are used; no Heath--Brown identity is postulated. The input n<=y^3 is
unchanged, including its upper boundary and n=0/1.
-/
namespace ImbalancedChen.P5Z.RealCutoffHeathBrownThree
noncomputable section
open Classical
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open RealTruncatedMobiusSupport

/-- Index j=0,1,2 means the manuscript term with 1,2,3 Mobius slots. -/
def term (y : ℝ) (j : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.log * (ζ : ArithmeticFunction ℝ)^j * muTrunc y^(j+1)

private theorem polynomial_identity (y : ℝ) :
    ArithmeticFunction.vonMangoldt * remainder y^3 =
      ArithmeticFunction.vonMangoldt -
        (ArithmeticFunction.log*muTrunc y + ArithmeticFunction.log*muTrunc y +
          ArithmeticFunction.log*muTrunc y) +
        (ArithmeticFunction.log*(ζ : ArithmeticFunction ℝ)*muTrunc y^2 +
          ArithmeticFunction.log*(ζ : ArithmeticFunction ℝ)*muTrunc y^2 +
          ArithmeticFunction.log*(ζ : ArithmeticFunction ℝ)*muTrunc y^2) -
        ArithmeticFunction.log*(ζ : ArithmeticFunction ℝ)^2*muTrunc y^3 := by
  unfold remainder
  rw [← ArithmeticFunction.zeta_mul_vonMangoldt]
  ring

/-- The three coefficients are EXACTLY +3,-3,+1. -/
theorem three_term_identity {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : (n : ℝ) ≤ y^3) :
    ArithmeticFunction.vonMangoldt n =
      3*(ArithmeticFunction.log*muTrunc y) n -
        3*(ArithmeticFunction.log*(ζ : ArithmeticFunction ℝ)*muTrunc y^2) n +
        (ArithmeticFunction.log*(ζ : ArithmeticFunction ℝ)^2*muTrunc y^3) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (polynomial_identity y)
  have hz := vonMangoldt_remainder_cube_zero hy hn
  rw [hz] at h
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply] at h
  linarith

/-- Finite binomial spelling of manuscript current-HB. The index offset
avoids a spurious j=0 inverse power; j+1 runs through EXACTLY 1,2,3. -/
theorem order_three_identity {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : (n : ℝ) ≤ y^3) :
    ArithmeticFunction.vonMangoldt n =
      ∑ j ∈ Finset.range 3, (-1 : ℝ)^j * (Nat.choose 3 (j+1) : ℝ) * term y j n := by
  have h := three_term_identity hy hn
  rw [h]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, term, pow_zero, pow_one,
    Nat.choose, mul_one, one_mul, zero_add]
  ring

theorem identity_at_zero (y : ℝ) :
    (∑ j ∈ Finset.range 3, (-1 : ℝ)^j * (Nat.choose 3 (j+1) : ℝ) * term y j 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp

theorem identity_at_one {y : ℝ} (hy : 1 ≤ y) :
    (∑ j ∈ Finset.range 3, (-1 : ℝ)^j * (Nat.choose 3 (j+1) : ℝ) * term y j 1) = 0 := by
  have hcube : (1 : ℝ) ≤ y^3 := one_le_pow₀ hy
  simpa using (order_three_identity (by linarith : 0 ≤ y) hcube).symm

end
end ImbalancedChen.P5Z.RealCutoffHeathBrownThree
