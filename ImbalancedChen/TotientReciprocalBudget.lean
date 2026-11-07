import ImbalancedChen.CurvedRegionDiscrepancy
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite reciprocal-totient budget

For every natural cap `D`, including zero, the actual Euler totient satisfies

`∑ d ∈ Icc 1 D, 1 / φ(d) ≤ 4 * (1 + log (max 1 D))`.

The proof is entirely finite. Euler's product and the squarefree-divisor
expansion give `n / φ(n) ≤ 2 * ∑ d ∣ n, 1 / d`. The factor two follows from
the exact telescoping product over all integers from two to `n`. Finite
Dirichlet convolution then separates a harmonic sum and an inverse-square
sum. The latter is bounded by two by an elementary telescoping comparison.
No distribution theorem, asymptotic totient estimate, or hypothesis about
the desired budget is used. The final corollary applies this bound to the
actual finite curved-boundary discrepancy, giving its logarithmic mass cost.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The exact finite product underlying the uniform Euler-factor bound. -/
theorem totientBudget_integer_eulerProduct (k : ℕ) :
    (∏ j ∈ Finset.Icc 2 (k + 1), (1 - 1 / (j : ℝ) ^ 2)) =
      ((k : ℝ) + 2) / (2 * ((k : ℝ) + 1)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      have hk2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp [hk1, hk2]
      <;> ring

/-- Omitting factors between zero and one only increases this product. -/
theorem totientBudget_prime_eulerProduct_lower (n : ℕ) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  have hsub : n.primeFactors ⊆ Finset.Icc 2 (n + 1) := by
    intro p hp
    exact Finset.mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
        (Nat.le_of_mem_primeFactors hp).trans (Nat.le_succ n)⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one
    (f := fun p : ℕ => (1 - 1 / (p : ℝ) ^ 2)) hsub
    (fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
      have hpR : (0 : ℝ) < p := by linarith
      have hsq : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
      have hi : (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 :=
        (div_le_one (pow_pos hpR 2)).mpr hsq
      linarith)
    (fun p _ _ => sub_le_self _ (by positivity))
  rw [totientBudget_integer_eulerProduct] at hprod
  refine le_trans ?_ hprod
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
  linarith

/-- The prime-subset expansion is a literal sum over squarefree divisors. -/
theorem totientBudget_squarefree_expansion {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) =
      ∑ d ∈ n.divisors with Squarefree d, 1 / (d : ℝ) := by
  classical
  have hfac : (UniqueFactorizationMonoid.normalizedFactors n).toFinset =
      n.primeFactors := by
    ext p
    simp only [Multiset.mem_toFinset, Nat.factors_eq, Multiset.mem_coe,
      Nat.mem_primeFactors_iff_mem_primeFactorsList]
  rw [Finset.prod_one_add, Nat.sum_divisors_filter_squarefree hn, hfac]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_val]
  simp only [one_div, Finset.prod_inv_distrib, Nat.cast_prod, Function.id_def]

/-- A real-valued form of mathlib's rational Euler product formula. -/
theorem totientBudget_totient_product (n : ℕ) :
    (Nat.totient n : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod,
    Rat.cast_sub, Rat.cast_one, Rat.cast_inv, one_div] using h

/-- A pointwise divisor majorant for the actual reciprocal totient. -/
theorem reciprocal_totient_le_divisor_sum {n : ℕ} (hn : 0 < n) :
    1 / (Nat.totient n : ℝ) ≤
      2 * ((1 / (n : ℝ)) * ∑ d ∈ n.divisors, 1 / (d : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have heuler :
      (Nat.totient n : ℝ) * (∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))) =
        (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [totientBudget_totient_product, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    simp only [one_div, inv_pow]
    ring
  have hlower := mul_le_mul_of_nonneg_left
    (totientBudget_prime_eulerProduct_lower n) hnR.le
  rw [← heuler, totientBudget_squarefree_expansion hn.ne'] at hlower
  have hsum :
      (∑ d ∈ n.divisors with Squarefree d, 1 / (d : ℝ)) ≤
        ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsum hphi.le
  have hmain : (n : ℝ) ≤
      2 * ((Nat.totient n : ℝ) * ∑ d ∈ n.divisors, 1 / (d : ℝ)) := by
    nlinarith
  apply (div_le_iff₀ hphi).mpr
  calc
    1 = (n : ℝ) / (n : ℝ) := (div_self hnR.ne').symm
    _ ≤ (2 * ((Nat.totient n : ℝ) * ∑ d ∈ n.divisors, 1 / (d : ℝ))) /
        (n : ℝ) := div_le_div_of_nonneg_right hmain hnR.le
    _ = _ := by ring

/-- A finite inverse-square sum needs only a telescoping comparison. -/
theorem totientBudget_inverse_square_sum (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, 1 / (d : ℝ) ^ 2) ≤ 2 := by
  have hsharp : ∀ k : ℕ,
      (∑ d ∈ Finset.Icc 1 k, 1 / (d : ℝ) ^ 2) ≤
        2 - 2 / ((k : ℝ) + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
        have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hk' : (0 : ℝ) < (k : ℝ) + 1 + 1 := by positivity
        have hcomp : 1 / ((k : ℝ) + 1) ^ 2 ≤
            2 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1)) := by
          apply (div_le_div_iff₀ (pow_pos hk 2) (mul_pos hk hk')).mpr
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          nlinarith
        have htel : 2 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1)) =
            2 / ((k : ℝ) + 1) - 2 / ((k : ℝ) + 1 + 1) := by
          field_simp [hk.ne', hk'.ne']
          <;> ring
        rw [htel] at hcomp
        linarith
  exact (hsharp D).trans (sub_le_self _ (by positivity))

private def totientBudget_inv : ArithmeticFunction ℝ :=
  ⟨fun n => 1 / (n : ℝ), by simp⟩

private def totientBudget_invSq : ArithmeticFunction ℝ :=
  ⟨fun n => 1 / (n : ℝ) ^ 2, by simp⟩

private theorem totientBudget_convolution (n : ℕ) :
    (totientBudget_invSq * totientBudget_inv) n =
      (1 / (n : ℝ)) * ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun i j => totientBudget_invSq i * totientBudget_inv j), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change (1 / (d : ℝ) ^ 2) * (1 / ((n / d : ℕ) : ℝ)) =
    (1 / (n : ℝ)) * (1 / (d : ℝ))
  have heq : (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  rw [← heq]
  simp only [one_div, mul_inv_rev, inv_pow]
  ring

/-- Reindexing the divisor sums produces an inverse-square sum times a
harmonic sum. Dropping the hyperbolic constraint is justified by positivity. -/
theorem totientBudget_divisor_sum_le (D : ℕ) :
    (∑ n ∈ Finset.Icc 1 D,
      (1 / (n : ℝ)) * ∑ d ∈ n.divisors, 1 / (d : ℝ)) ≤
        2 * ∑ m ∈ Finset.Icc 1 D, 1 / (m : ℝ) := by
  have hI : Finset.Ioc 0 D = Finset.Icc 1 D := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hid := ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter
    totientBudget_invSq totientBudget_inv D
  rw [hI] at hid
  simp_rw [totientBudget_convolution] at hid
  rw [hid]
  calc
    _ ≤ ∑ x ∈ Finset.Icc 1 D ×ˢ Finset.Icc 1 D,
        totientBudget_invSq x.1 * totientBudget_inv x.2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => by change 0 ≤ (1 / (x.1 : ℝ) ^ 2) * (1 / (x.2 : ℝ)); positivity)
    _ = (∑ d ∈ Finset.Icc 1 D, 1 / (d : ℝ) ^ 2) *
        ∑ m ∈ Finset.Icc 1 D, 1 / (m : ℝ) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
      rfl
    _ ≤ 2 * ∑ m ∈ Finset.Icc 1 D, 1 / (m : ℝ) :=
      mul_le_mul_of_nonneg_right (totientBudget_inverse_square_sum D)
        (Finset.sum_nonneg fun m _ => by positivity)

/-- An explicit absolute bound, first expressed using the harmonic sum. -/
theorem sum_reciprocal_totient_le_four_harmonic (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, 1 / (Nat.totient d : ℝ)) ≤
      4 * (harmonic D : ℝ) := by
  have hpoint := Finset.sum_le_sum (s := Finset.Icc 1 D)
    (fun n hn => reciprocal_totient_le_divisor_sum
      (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega))
  rw [← Finset.mul_sum] at hpoint
  have hbound := mul_le_mul_of_nonneg_left (totientBudget_divisor_sum_le D)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hH : (∑ m ∈ Finset.Icc 1 D, 1 / (m : ℝ)) = (harmonic D : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hH] at hbound
  nlinarith

/-- The genuine reciprocal-totient logarithmic budget with absolute constant
four. The empty sum at `D = 0` is included without an extra hypothesis. -/
theorem sum_reciprocal_totient_le_log (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, 1 / (Nat.totient d : ℝ)) ≤
      4 * (1 + Real.log (max 1 (D : ℝ))) := by
  by_cases hD : D = 0
  · simp [hD]
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hD
  rw [max_eq_right hD1]
  exact (sum_reciprocal_totient_le_four_harmonic D).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (by norm_num))

/-- The same budget applies to any selected positive moduli below the cap. -/
theorem sum_reciprocal_totient_subset_le_log (S : Finset ℕ) (D : ℕ)
    (hS : S ⊆ Finset.Icc 1 D) :
    (∑ d ∈ S, 1 / (Nat.totient d : ℝ)) ≤
      4 * (1 + Real.log (max 1 (D : ℝ))) := by
  refine le_trans ?_ (sum_reciprocal_totient_le_log D)
  exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun d _ _ => by positivity)

/-- The finite curved-boundary transfer now pays an explicit logarithmic
cost for its actual total boundary mass. The residue may depend on `d`. -/
theorem sum_abs_finitePrimitiveDiscrepancy_le_log_sourceMass
    (D : ℕ) (S : Finset ℕ) (h u : ℕ → ℝ) (a : ℕ → ℕ)
    (hh : ∀ m ∈ S, 0 ≤ h m) (hhu : ∀ m ∈ S, h m ≤ u m) :
    (∑ d ∈ Finset.Icc 1 D, |finitePrimitiveDiscrepancy S h (a d) d|) ≤
      (∑ d ∈ Finset.Icc 1 D, |finitePrimitiveDiscrepancy S u (a d) d|) +
        4 * finiteSourceMass S u * (1 + Real.log (max 1 (D : ℝ))) := by
  have hmass : 0 ≤ finiteSourceMass S u :=
    Finset.sum_nonneg fun m hm => (hh m hm).trans (hhu m hm)
  have hbudget := mul_le_mul_of_nonneg_left (sum_reciprocal_totient_le_log D) hmass
  calc
    _ ≤ (∑ d ∈ Finset.Icc 1 D, |finitePrimitiveDiscrepancy S u (a d) d|) +
        finiteSourceMass S u * (∑ d ∈ Finset.Icc 1 D, 1 / (Nat.totient d : ℝ)) :=
      sum_abs_finitePrimitiveDiscrepancy_le_sourceMass (Finset.Icc 1 D) S h u a hh hhu
    _ ≤ (∑ d ∈ Finset.Icc 1 D, |finitePrimitiveDiscrepancy S u (a d) d|) +
        finiteSourceMass S u * (4 * (1 + Real.log (max 1 (D : ℝ)))) :=
      add_le_add le_rfl hbudget
    _ = _ := by ring

end

end ImbalancedChen
