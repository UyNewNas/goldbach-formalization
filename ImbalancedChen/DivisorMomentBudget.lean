import ImbalancedChen.TotientReciprocalBudget
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# An elementary fourth-divisor-moment budget on squarefree moduli

For any squarefree-support set `S ⊆ Icc 1 D`, this file proves the actual
finite bound

`∑ d ∈ S, τ(d)^4 / φ(d) ≤ (4 * (1 + log (max 1 D)))^16`.

The exponent sixteen comes from an exact identity: on squarefree inputs,
the sixteenth Dirichlet-convolution power of the actual reciprocal-totient
function equals `τ(d)^4 / φ(d)`. Nonnegativity lets each convolution sum
be enlarged from its hyperbolic region to a square. The already proved
elementary reciprocal-totient budget then completes the argument.

No divisor moment, prime-distribution estimate, or Euler-product asymptotic
is assumed. The final specialization retains the literal allowed divisors
of `sieveProduct`, including `d = 1` and the inclusive upper endpoint.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- A finite Dirichlet-convolution sum is at most the product of the two
finite sums, provided both functions are nonnegative. -/
theorem sum_arithmeticFunction_mul_le
    (f g : ArithmeticFunction ℝ)
    (hf : ∀ n : ℕ, 0 ≤ f n) (hg : ∀ n : ℕ, 0 ≤ g n) (D : ℕ) :
    (∑ n ∈ Finset.Icc 1 D, (f * g) n) ≤
      (∑ n ∈ Finset.Icc 1 D, f n) * (∑ n ∈ Finset.Icc 1 D, g n) := by
  have hI : Finset.Ioc 0 D = Finset.Icc 1 D := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hid := ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter f g D
  rw [hI] at hid
  rw [hid]
  calc
    _ ≤ ∑ x ∈ Finset.Icc 1 D ×ˢ Finset.Icc 1 D, f x.1 * g x.2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => mul_nonneg (hf x.1) (hg x.2))
    _ = _ := by rw [Finset.sum_product, Finset.sum_mul_sum]

/-- Dirichlet-convolution powers preserve pointwise nonnegativity. -/
theorem arithmeticFunction_pow_nonneg
    (f : ArithmeticFunction ℝ) (hf : ∀ n : ℕ, 0 ≤ f n) (k n : ℕ) :
    0 ≤ (f ^ k) n := by
  induction k generalizing n with
  | zero =>
      simp only [pow_zero, ArithmeticFunction.one_apply]
      split_ifs <;> norm_num
  | succ k ih =>
      rw [pow_succ, ArithmeticFunction.mul_apply]
      exact Finset.sum_nonneg fun x _ =>
        mul_nonneg (ih x.1) (hf x.2)

/-- Iterating the finite convolution inequality costs the corresponding
ordinary power of the original finite sum. The exponent is positive, so
this includes the empty interval `D = 0` without an exceptional case. -/
theorem sum_arithmeticFunction_pow_succ_le
    (f : ArithmeticFunction ℝ) (hf : ∀ n : ℕ, 0 ≤ f n) (k D : ℕ) :
    (∑ n ∈ Finset.Icc 1 D, (f ^ (k + 1)) n) ≤
      (∑ n ∈ Finset.Icc 1 D, f n) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        _ = ∑ n ∈ Finset.Icc 1 D, (f ^ (k + 1) * f) n := by rw [pow_succ]
        _ ≤ (∑ n ∈ Finset.Icc 1 D, (f ^ (k + 1)) n) *
            (∑ n ∈ Finset.Icc 1 D, f n) :=
          sum_arithmeticFunction_mul_le (f ^ (k + 1)) f
            (arithmeticFunction_pow_nonneg f hf (k + 1)) hf D
        _ ≤ (∑ n ∈ Finset.Icc 1 D, f n) ^ (k + 1) *
            (∑ n ∈ Finset.Icc 1 D, f n) :=
          mul_le_mul_of_nonneg_right ih (Finset.sum_nonneg fun n _ => hf n)
        _ = _ := (pow_succ _ (k + 1)).symm

/-- At a prime, the `k`-fold convolution has exactly `k` possible slots
for that prime; all other slots contribute the value one. -/
theorem halfProductDensity_pow_apply_prime (k : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    (halfProductDensity ^ k) p = (k : ℝ) * halfProductDensity p := by
  induction k with
  | zero => simp [hp.ne_one]
  | succ k ih =>
      have hunit : (halfProductDensity ^ k) 1 = 1 :=
        halfProductDensity_isMultiplicative.pow.map_one
      have hnot : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
        simpa only [Finset.mem_singleton] using hp.ne_one.symm
      rw [pow_succ, ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal
          (fun i j => (halfProductDensity ^ k) i * halfProductDensity j), hp.divisors]
      simp only [Finset.sum_insert hnot, Finset.sum_singleton,
        Nat.div_one, Nat.div_self hp.pos, hunit, halfProductDensity_one, one_mul,
        mul_one, ih, Nat.cast_succ]
      ring

/-- The elementary prime-factor formula for the divisor count on a
squarefree integer, expressed over the reals. -/
theorem squarefree_divisors_card_eq_prod_two {n : ℕ} (hn : Squarefree n) :
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, (2 : ℝ) := by
  rw [Nat.card_divisors hn.ne_zero, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_eq_one_of_squarefree hn
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
  norm_num

/-- The fourth divisor moment is an exact sixteenth convolution power
on squarefree inputs. -/
theorem halfProductDensity_pow_sixteen_apply_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    (halfProductDensity ^ 16) n =
      (n.divisors.card : ℝ) ^ 4 / (Nat.totient n : ℝ) := by
  have hpow : (n.divisors.card : ℝ) ^ 4 = ∏ p ∈ n.primeFactors, (16 : ℝ) := by
    rw [squarefree_divisors_card_eq_prod_two hn, ← Finset.prod_pow]
    norm_num
  rw [← halfProductDensity_isMultiplicative.pow.prod_primeFactors hn]
  calc
    _ = ∏ p ∈ n.primeFactors, (16 : ℝ) * halfProductDensity p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact halfProductDensity_pow_apply_prime 16 (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, (16 : ℝ)) * halfProductDensity n := by
      rw [Finset.prod_mul_distrib, halfProductDensity_isMultiplicative.prod_primeFactors hn]
    _ = _ := by rw [← hpow, halfProductDensity_apply]; ring

/-- The actual fourth divisor moment on any squarefree-support set is
bounded by a sixteenth power of the actual reciprocal-totient sum. -/
theorem sum_divisor_fourth_moment_le_reciprocal_totient_pow
    (S : Finset ℕ) (D : ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ)) ≤
      (∑ d ∈ Finset.Icc 1 D, 1 / (Nat.totient d : ℝ)) ^ 16 := by
  have hnonneg (n : ℕ) : 0 ≤ halfProductDensity n := by
    rw [halfProductDensity_apply]
    positivity
  calc
    _ = ∑ d ∈ S, (halfProductDensity ^ 16) d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (halfProductDensity_pow_sixteen_apply_of_squarefree (hsq d hd)).symm
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (halfProductDensity ^ 16) d :=
      Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun d _ _ => arithmeticFunction_pow_nonneg halfProductDensity hnonneg 16 d)
    _ ≤ _ := by
      simpa only [halfProductDensity_apply] using
        sum_arithmeticFunction_pow_succ_le halfProductDensity hnonneg 15 D

/-- An unconditional, explicit polylogarithmic fourth-divisor-moment
budget, with absolute constant `4^16` and logarithmic exponent sixteen. -/
theorem sum_divisor_fourth_moment_le_log
    (S : Finset ℕ) (D : ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (hsq : ∀ d ∈ S, Squarefree d) :
    (∑ d ∈ S, (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ)) ≤
      (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16 := by
  exact (sum_divisor_fourth_moment_le_reciprocal_totient_pow S D hS hsq).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => by positivity)
      (sum_reciprocal_totient_le_log D) 16)

/-- The squarefree-restricted interval form of the same elementary budget. -/
theorem sum_squarefree_divisor_fourth_moment_le_log (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D with Squarefree d,
      (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ)) ≤
      (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16 := by
  exact sum_divisor_fourth_moment_le_log _ D (Finset.filter_subset _ _)
    (fun d hd => (Finset.mem_filter.mp hd).2)

/-- The literal allowed-divisor moment needed by the actual lambda-square
sieve error. Squarefreeness is derived from the actual sieve product. -/
theorem sum_sieveProduct_divisor_fourth_moment_le_log (N z D : ℕ) :
    (∑ d ∈ (sieveProduct N z).divisors with d ≤ D,
      (d.divisors.card : ℝ) ^ 4 / (Nat.totient d : ℝ)) ≤
      (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16 := by
  apply sum_divisor_fourth_moment_le_log _ D
  · intro d hd
    have hmem := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hmem.1, hmem.2⟩
  · intro d hd
    exact (sieveProduct_squarefree N z).squarefree_of_dvd
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)

end

end ImbalancedChen
