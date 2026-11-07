import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED. CODE_ONLY, 2026-10-24.
An explicit weighted global bound for the literal real K profile jet
  (A(cosh u) + sinh u B(cosh u)) exp(-q cosh u), q > 0.
The constant is computed from the finite coefficient l1 masses, a polynomial
degree and a factorial/power of q. No bounded-growth, Schwartz, integrability
or spectral-estimate hypothesis occurs. No derivative in q or height-decay
claim is made. This supplier has Mathlib imports only and no draft dependency.
Its literal function is definitionally the derivative-polynomial worker's
jetValue after unfolding that worker's jetValue and profile definitions.
-/

namespace ImbalancedChen.Part3.KProfilePolynomialDecayP3SourceOnly
noncomputable section

open Classical Polynomial
open scoped BigOperators

/-- The finite coefficient l1 mass, including the zero polynomial. -/
def coefficientMass (P : ℝ[X]) : ℝ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|

/-- The sinh factor costs one additional cosh power. -/
def envelopeDegree (A B : ℝ[X]) : ℕ := max A.natDegree (B.natDegree + 1)

/-- Explicit constant for the M-th polynomial weight. -/
def decayConstant (q : ℝ) (A B : ℝ[X]) (M : ℕ) : ℝ :=
  (coefficientMass A + coefficientMass B) *
    (((M + envelopeDegree A B).factorial : ℝ) / q ^ (M + envelopeDegree A B))

theorem coefficientMass_nonneg (P : ℝ[X]) : 0 ≤ coefficientMass P := by
  exact Finset.sum_nonneg (fun i _hi => abs_nonneg (P.coeff i))

/-- Finite polynomial evaluation is bounded from its actual coefficients. -/
theorem polynomial_eval_abs_le_coefficientMass (P : ℝ[X])
    {y : ℝ} (hy : 1 ≤ y) :
    |P.eval y| ≤ coefficientMass P * y ^ P.natDegree := by
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  rw [Polynomial.eval_eq_sum_range]
  calc
    |∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * y ^ i| ≤
        ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i * y ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i| * y ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      have hiD : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [abs_mul, abs_of_nonneg (pow_nonneg hy0 i)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy hiD) (abs_nonneg _)
    _ = coefficientMass P * y ^ P.natDegree := by
      unfold coefficientMass
      rw [Finset.sum_mul]

/-- Exact hyperbolic identities give the global sinh envelope. -/
theorem abs_sinh_le_cosh (u : ℝ) : |Real.sinh u| ≤ Real.cosh u := by
  have hp : 0 ≤ Real.cosh u + Real.sinh u := by
    rw [Real.cosh_add_sinh]
    exact (Real.exp_pos u).le
  have hm : 0 ≤ Real.cosh u - Real.sinh u := by
    rw [Real.cosh_sub_sinh]
    exact (Real.exp_pos (-u)).le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- No restriction to a half-line is needed for the polynomial u weight. -/
theorem abs_self_le_cosh (u : ℝ) : |u| ≤ Real.cosh u := by
  calc
    |u| ≤ Real.sinh |u| := Real.self_le_sinh_iff.mpr (abs_nonneg u)
    _ = |Real.sinh u| := (Real.abs_sinh u).symm
    _ ≤ Real.cosh u := abs_sinh_le_cosh u

/-- A literal jet amplitude is controlled by one explicit cosh power. -/
theorem hyperbolic_polynomial_abs_le (A B : ℝ[X]) (u : ℝ) :
    |A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)| ≤
      (coefficientMass A + coefficientMass B) *
        Real.cosh u ^ envelopeDegree A B := by
  have hy1 : 1 ≤ Real.cosh u := Real.one_le_cosh u
  have hy0 : 0 ≤ Real.cosh u := (Real.cosh_pos u).le
  have hA := polynomial_eval_abs_le_coefficientMass A hy1
  have hB := polynomial_eval_abs_le_coefficientMass B hy1
  have hAdeg : A.natDegree ≤ envelopeDegree A B := le_max_left _ _
  have hBdeg : B.natDegree + 1 ≤ envelopeDegree A B := le_max_right _ _
  have hsB : |Real.sinh u * B.eval (Real.cosh u)| ≤
      coefficientMass B * Real.cosh u ^ (B.natDegree + 1) := by
    calc
      |Real.sinh u * B.eval (Real.cosh u)| =
          |Real.sinh u| * |B.eval (Real.cosh u)| := abs_mul _ _
      _ ≤ Real.cosh u * (coefficientMass B * Real.cosh u ^ B.natDegree) :=
        mul_le_mul (abs_sinh_le_cosh u) hB (abs_nonneg _) hy0
      _ = coefficientMass B * Real.cosh u ^ (B.natDegree + 1) := by
        rw [pow_succ]
        ring
  calc
    |A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)| ≤
        |A.eval (Real.cosh u)| + |Real.sinh u * B.eval (Real.cosh u)| :=
      abs_add_le _ _
    _ ≤ coefficientMass A * Real.cosh u ^ A.natDegree +
        coefficientMass B * Real.cosh u ^ (B.natDegree + 1) := add_le_add hA hsB
    _ ≤ coefficientMass A * Real.cosh u ^ envelopeDegree A B +
        coefficientMass B * Real.cosh u ^ envelopeDegree A B := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 hAdeg)
          (coefficientMass_nonneg A))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 hBdeg)
          (coefficientMass_nonneg B))
    _ = (coefficientMass A + coefficientMass B) *
        Real.cosh u ^ envelopeDegree A B := by ring

/-- Taylor's positive exponential term gives the explicit global power bound. -/
theorem pow_mul_exp_neg_le_factorial_div {q : ℝ} (hq : 0 < q)
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    y ^ n * Real.exp (-q * y) ≤ (n.factorial : ℝ) / q ^ n := by
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hbase : (q * y) ^ n ≤ Real.exp (q * y) * (n.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (mul_nonneg hq.le hy) n)
  have hexp : Real.exp (q * y) * Real.exp (-q * y) = 1 := by
    rw [← Real.exp_add, show q * y + -q * y = 0 by ring, Real.exp_zero]
  apply (le_div_iff₀ (pow_pos hq n)).mpr
  calc
    (y ^ n * Real.exp (-q * y)) * q ^ n =
        (q * y) ^ n * Real.exp (-q * y) := by
      rw [mul_pow]
      ring
    _ ≤ (Real.exp (q * y) * (n.factorial : ℝ)) * Real.exp (-q * y) :=
      mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (Real.exp (q * y) * Real.exp (-q * y)) := by ring
    _ = (n.factorial : ℝ) := by rw [hexp, mul_one]

theorem decayConstant_nonneg {q : ℝ} (hq : 0 < q)
    (A B : ℝ[X]) (M : ℕ) : 0 ≤ decayConstant q A B M := by
  unfold decayConstant
  exact mul_nonneg (add_nonneg (coefficientMass_nonneg A) (coefficientMass_nonneg B))
    (div_nonneg (by positivity) (pow_pos hq _).le)

/-- The actual all-real-u weighted polynomial-profile bound with explicit C. -/
theorem profile_polynomial_weighted_le {q : ℝ} (hq : 0 < q)
    (A B : ℝ[X]) (M : ℕ) (u : ℝ) :
    |u| ^ M *
      |(A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) *
        Real.exp (-q * Real.cosh u)| ≤ decayConstant q A B M := by
  have hy0 : 0 ≤ Real.cosh u := (Real.cosh_pos u).le
  have hu : |u| ^ M ≤ Real.cosh u ^ M :=
    pow_le_pow_left₀ (abs_nonneg u) (abs_self_le_cosh u) M
  have hshape := hyperbolic_polynomial_abs_le A B u
  have hmass : 0 ≤ coefficientMass A + coefficientMass B :=
    add_nonneg (coefficientMass_nonneg A) (coefficientMass_nonneg B)
  calc
    |u| ^ M *
        |(A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) *
          Real.exp (-q * Real.cosh u)| =
        (|u| ^ M * |A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)|) *
          Real.exp (-q * Real.cosh u) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ (Real.cosh u ^ M *
        ((coefficientMass A + coefficientMass B) *
          Real.cosh u ^ envelopeDegree A B)) * Real.exp (-q * Real.cosh u) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hu hshape (abs_nonneg _) (pow_nonneg hy0 M)) (Real.exp_pos _).le
    _ = (coefficientMass A + coefficientMass B) *
        (Real.cosh u ^ (M + envelopeDegree A B) * Real.exp (-q * Real.cosh u)) := by
      rw [pow_add]
      ring
    _ ≤ (coefficientMass A + coefficientMass B) *
        (((M + envelopeDegree A B).factorial : ℝ) / q ^ (M + envelopeDegree A B)) :=
      mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_le_factorial_div hq hy0 (M + envelopeDegree A B)) hmass
    _ = decayConstant q A B M := by rfl

/-- Existential form for direct use in the Schwartz bounded-growth field. -/
theorem profile_polynomial_weighted_decay {q : ℝ} (hq : 0 < q)
    (A B : ℝ[X]) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      |u| ^ M *
        |(A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) *
          Real.exp (-q * Real.cosh u)| ≤ C := by
  exact ⟨decayConstant q A B M, decayConstant_nonneg hq A B M,
    fun u => profile_polynomial_weighted_le hq A B M u⟩

/-- Norm formulation, with the literal jet expression and no derivative premise. -/
theorem profile_polynomial_weighted_norm_decay {q : ℝ} (hq : 0 < q)
    (A B : ℝ[X]) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖u‖ ^ M *
        ‖(A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) *
          Real.exp (-q * Real.cosh u)‖ ≤ C := by
  simpa only [Real.norm_eq_abs] using profile_polynomial_weighted_decay hq A B M

/-- The same explicit constant works for every q above a fixed positive a. -/
theorem profile_polynomial_weighted_decay_uniform {a : ℝ} (ha : 0 < a)
    (A B : ℝ[X]) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, a ≤ q → ∀ u : ℝ,
      |u| ^ M *
        |(A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) *
          Real.exp (-q * Real.cosh u)| ≤ C := by
  refine ⟨decayConstant a A B M, decayConstant_nonneg ha A B M, ?_⟩
  intro q hq u
  have he : Real.exp (-q * Real.cosh u) ≤ Real.exp (-a * Real.cosh u) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le
    linarith
  calc
    |u| ^ M *
        |(A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) *
          Real.exp (-q * Real.cosh u)| ≤
        |u| ^ M *
          |(A.eval (Real.cosh u) + Real.sinh u * B.eval (Real.cosh u)) *
            Real.exp (-a * Real.cosh u)| := by
      simp only [abs_mul,
        abs_of_pos (Real.exp_pos (-q * Real.cosh u)),
        abs_of_pos (Real.exp_pos (-a * Real.cosh u))]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (abs_nonneg _)) (pow_nonneg (abs_nonneg u) M)
    _ ≤ decayConstant a A B M := profile_polynomial_weighted_le ha A B M u

end
end ImbalancedChen.Part3.KProfilePolynomialDecayP3SourceOnly

/-!
All constants above are derived from q, A, B, M and actual finite
coefficients. No unknown envelope is supplied as a hypothesis. Derivative
polynomials can now instantiate A and B in the norm theorem; constructing
the SchwartzMap is the separate assembly worker's responsibility. No
claim about q derivatives, ODEs, height t^-2, Kuznetsov normalization,
Plancherel, large sieves or the manuscript endpoint is made here.
No Lean/lake/checker/audit/numerical/Git execution was performed.
-/
