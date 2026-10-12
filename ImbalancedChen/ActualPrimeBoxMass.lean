import ImbalancedChen.ActualPrimeReciprocalMass
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Actual reciprocal-prime mass on finite logarithmic boxes

The carrier consists of functions whose coordinates lie in the actual
target-linked prime intervals `[N ^ a i, N ^ b i)`. Each coordinate has its
own enumeration cap, while all coordinates exclude primes dividing the
same target `N`. The box mass is a sum over these functions, not a product
by definition. Its factorization is the finite distributive law.

Adjacent separated boxes force every tuple to be strictly decreasing,
including when consecutive boundary exponents agree. For these boxes,
the product summand is also the reciprocal totient of the tuple product.
The limiting statements allow arbitrary positive fixed exponents; the
upper exponents need not be at most one.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Filter Topology

/-- The actual finite carrier of prime tuples in a logarithmic box. -/
def actualPrimeBoxTuples (N : ℕ) {k : ℕ} (a b : Fin k → ℝ) :
    Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun i =>
    roughPrimeFinset N (Nat.ceil ((N : ℝ) ^ b i))
      ((N : ℝ) ^ a i) ((N : ℝ) ^ b i))

/-- Membership retains primality, the common target exclusion, and both
exact endpoints. Enumeration caps add no truncation. -/
theorem mem_actualPrimeBoxTuples_iff {N k : ℕ} {a b : Fin k → ℝ}
    {p : Fin k → ℕ} :
    p ∈ actualPrimeBoxTuples N a b ↔
      ∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
        (N : ℝ) ^ a i ≤ (p i : ℝ) ∧ (p i : ℝ) < (N : ℝ) ^ b i := by
  simp only [actualPrimeBoxTuples, Fintype.mem_piFinset,
    mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)]

/-- The mass is defined by a sum over actual function tuples. -/
def actualPrimeBoxMass (N : ℕ) {k : ℕ} (a b : Fin k → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N a b, ∏ i, 1 / ((p i : ℝ) - 1)

/-- Every actual tuple has a nonnegative reciprocal-prime product weight. -/
theorem actualPrimeBoxWeight_nonneg {N k : ℕ} {a b : Fin k → ℝ}
    {p : Fin k → ℕ} (hp : p ∈ actualPrimeBoxTuples N a b) :
    0 ≤ ∏ i, 1 / ((p i : ℝ) - 1) := by
  apply Finset.prod_nonneg
  intro i _
  have hpi : (1 : ℝ) < p i := by
    exact_mod_cast (mem_actualPrimeBoxTuples_iff.mp hp i).1.one_lt
  exact le_of_lt (one_div_pos.mpr (sub_pos.mpr hpi))

/-- The true box sum is nonnegative for every target and every box. -/
theorem actualPrimeBoxMass_nonneg (N : ℕ) {k : ℕ} (a b : Fin k → ℝ) :
    0 ≤ actualPrimeBoxMass N a b := by
  exact Finset.sum_nonneg (fun _ hp => actualPrimeBoxWeight_nonneg hp)

/-- Exact factorization by the finite product/sum distributive law. -/
theorem actualPrimeBoxMass_eq_prod (N : ℕ) {k : ℕ} (a b : Fin k → ℝ) :
    actualPrimeBoxMass N a b = ∏ i, actualPrimeReciprocalMass N (a i) (b i) := by
  classical
  exact (Finset.prod_univ_sum
    (fun i => roughPrimeFinset N (Nat.ceil ((N : ℝ) ^ b i))
      ((N : ℝ) ^ a i) ((N : ℝ) ^ b i))
    (fun _ p => 1 / ((p : ℝ) - 1))).symm

/-- A genuine finite-dimensional box limit, with no upper bound on the
fixed exponents. The zero-dimensional mass and limiting product are one. -/
theorem tendsto_actualPrimeBoxMass {k : ℕ} (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) :
    Tendsto (fun N : ℕ => actualPrimeBoxMass N a b) atTop
      (𝓝 (∏ i, Real.log (b i / a i))) := by
  simp only [actualPrimeBoxMass_eq_prod]
  exact tendsto_finsetProd Finset.univ (fun i _ =>
    tendsto_actualPrimeReciprocalMass (ha i) (hab i))

/-- Consecutive separated boxes produce strictly decreasing prime tuples.
The equality case of the separating exponents is included. -/
theorem actualPrimeBoxTuples_strictAnti {N k : ℕ} {a b : Fin (k + 1) → ℝ}
    {p : Fin (k + 1) → ℕ} (hN : 1 ≤ N)
    (hsep : ∀ i : Fin k, b i.succ ≤ a i.castSucc)
    (hp : p ∈ actualPrimeBoxTuples N a b) : StrictAnti p := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  have hp' := mem_actualPrimeBoxTuples_iff.mp hp
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp := Real.rpow_le_rpow_of_exponent_le hN' (hsep i)
  have hlt := (hp' i.succ).2.2.2.trans_le
    (hexp.trans (hp' i.castSucc).2.2.1)
  exact_mod_cast hlt

/-- No prime is repeated in a tuple from adjacent separated boxes. -/
theorem actualPrimeBoxTuples_injective {N k : ℕ} {a b : Fin (k + 1) → ℝ}
    {p : Fin (k + 1) → ℕ} (hN : 1 ≤ N)
    (hsep : ∀ i : Fin k, b i.succ ≤ a i.castSucc)
    (hp : p ∈ actualPrimeBoxTuples N a b) : Function.Injective p :=
  (actualPrimeBoxTuples_strictAnti hN hsep hp).injective

private theorem totient_primeTuple_cast {k : ℕ} (p : Fin k → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (s : Finset (Fin k)) :
    (Nat.totient (∏ i ∈ s, p i) : ℝ) = ∏ i ∈ s, ((p i : ℝ) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hcop : (p i).Coprime (∏ j ∈ s, p j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
      intro heq
      have hij := hinj heq
      exact hi (hij ▸ hj)
    rw [Finset.prod_insert hi, Nat.totient_mul hcop, Nat.cast_mul,
      ih, Finset.prod_insert hi, Nat.totient_prime (hprime i)]
    rw [Nat.cast_sub (hprime i).one_lt.le, Nat.cast_one]

/-- The summand equals the reciprocal totient of the actual squarefree
tuple product whenever the labels are distinct. -/
theorem actualPrimeBoxTuple_reciprocalTotient {N k : ℕ} {a b : Fin k → ℝ}
    {p : Fin k → ℕ} (hp : p ∈ actualPrimeBoxTuples N a b)
    (hinj : Function.Injective p) :
    1 / (Nat.totient (∏ i, p i) : ℝ) = ∏ i, 1 / ((p i : ℝ) - 1) := by
  classical
  rw [totient_primeTuple_cast p (fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1)
    hinj Finset.univ, Finset.prod_div_distrib]
  simp

/-- The actual tuple product is coprime to the common target. -/
theorem actualPrimeBoxTuple_product_coprime_target {N k : ℕ}
    {a b : Fin k → ℝ} {p : Fin k → ℕ}
    (hp : p ∈ actualPrimeBoxTuples N a b) : (∏ i, p i).Coprime N := by
  rw [Nat.coprime_fintype_prod_left_iff]
  intro i
  have hi := mem_actualPrimeBoxTuples_iff.mp hp i
  exact hi.1.coprime_iff_not_dvd.mpr hi.2.1

/-- A second actual sum, using the totient of the tuple product. For
overlapping boxes it need not equal the factorized box mass. -/
def actualPrimeBoxTotientMass (N : ℕ) {k : ℕ} (a b : Fin k → ℝ) : ℝ :=
  ∑ p ∈ actualPrimeBoxTuples N a b, 1 / (Nat.totient (∏ i, p i) : ℝ)

/-- Adjacent separation removes repeated prime factors, so the actual
reciprocal-totient sum equals the factorized mass exactly. -/
theorem actualPrimeBoxTotientMass_eq_mass {N k : ℕ} {a b : Fin (k + 1) → ℝ}
    (hN : 1 ≤ N) (hsep : ∀ i : Fin k, b i.succ ≤ a i.castSucc) :
    actualPrimeBoxTotientMass N a b = actualPrimeBoxMass N a b := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  exact actualPrimeBoxTuple_reciprocalTotient hp
    (actualPrimeBoxTuples_injective hN hsep hp)

/-- The reciprocal-totient mass of an adjacent separated fixed box has
the same explicit product of logarithms as its limit. -/
theorem tendsto_actualPrimeBoxTotientMass {k : ℕ} (a b : Fin (k + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hsep : ∀ i : Fin k, b i.succ ≤ a i.castSucc) :
    Tendsto (fun N : ℕ => actualPrimeBoxTotientMass N a b) atTop
      (𝓝 (∏ i, Real.log (b i / a i))) := by
  apply (tendsto_actualPrimeBoxMass a b ha hab).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (actualPrimeBoxTotientMass_eq_mass hN hsep).symm

end

end ImbalancedChen
