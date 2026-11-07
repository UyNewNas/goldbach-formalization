import ImbalancedChen.U9PreprimeLocalObstruction
import ImbalancedChen.ActualSelbergMain

/-!
# The matching ordinary integer-row sieve and its true Selberg factors

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The density is the arithmetic function nu(e)=1/e, with value zero at zero.
Allowed primes are precisely the strict-cap primes not dividing d*N;
two is allowed whenever it satisfies that same arithmetic condition.
The coefficient skeleton has no original row/factor/near-cap arguments.
Its Selberg terms on allowed divisors are 1/phi(e), not product1/(p-2).
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section
open Classical
open scoped BigOperators

def ordinaryDensity : ArithmeticFunction ℝ where
  toFun e := 1 / (e : ℝ)
  map_zero' := by simp

@[simp] theorem ordinaryDensity_apply (e : ℕ) : ordinaryDensity e = 1 / (e : ℝ) := rfl

theorem ordinaryDensity_multiplicative : ordinaryDensity.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [ordinaryDensity_apply, Nat.cast_mul, one_div, mul_inv_rev, mul_comm]

/-- This coefficient model is fixed before p,q,X and all original rows. -/
def ordinarySkeleton (M z : ℕ) : BoundingSieve where
  support := ∅
  prodPrimes := sieveProduct M z
  prodPrimes_squarefree := sieveProduct_squarefree M z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := 0
  nu := ordinaryDensity
  nu_mult := ordinaryDensity_multiplicative
  nu_pos_of_prime := fun _ hp _ => one_div_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro ell hell _
    change 1 / (ell : ℝ) < 1
    have hpos : (0 : ℝ) < ell := by exact_mod_cast hell.pos
    apply (div_lt_one hpos).mpr
    exact_mod_cast hell.one_lt

/-- All allowed prime divisors avoid the actual AP modulus and the centre.
There is no parity-based deletion of two in this integer-row model. -/
theorem allowed_prime_data {N d z ell : ℕ} (hell : Nat.Prime ell)
    (hdiv : ell ∣ (ordinarySkeleton (d * N) z).prodPrimes) :
    ell < z ∧ ¬ell ∣ d ∧ ¬ell ∣ N := by
  have hmem := mem_sievePrimes.mp (prime_mem_sievePrimes_of_dvd hell hdiv)
  refine ⟨hmem.1, ?_, ?_⟩
  · intro h
    exact hmem.2.2 (dvd_mul_of_dvd_left h N)
  · intro h
    exact hmem.2.2 (dvd_mul_of_dvd_right h d)

/-- Generic Selberg factors specialize to reciprocal totient for the
ordinary 1/e density, with allowed-divisor squarefreeness proved first. -/
theorem ordinary_selbergTerms (M z e : ℕ) (he : e ∣ sieveProduct M z) :
    (ordinarySkeleton M z).selbergTerms e = 1 / (Nat.totient e : ℝ) := by
  have hsq : Squarefree e := (sieveProduct_squarefree M z).squarefree_of_dvd he
  have hprimeProduct : (ordinarySkeleton M z).selbergTerms e =
      ∏ ell ∈ e.primeFactors, 1 / ((ell : ℝ) - 1) := by
    rw [BoundingSieve.selbergTerms_apply]
    change ordinaryDensity e *
      (∏ ell ∈ e.primeFactors, (1 - ordinaryDensity ell)⁻¹) = _
    rw [← ordinaryDensity_multiplicative.prod_primeFactors hsq,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ell hell
    have hp := Nat.prime_of_mem_primeFactors hell
    have hell0 : (ell : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hell1 : (ell : ℝ) - 1 ≠ 0 := by
      have hgt : (1 : ℝ) < ell := by exact_mod_cast hp.one_lt
      linarith
    simp only [ordinaryDensity_apply]
    have hfactor : 1 - 1 / (ell : ℝ) = ((ell : ℝ) - 1) / (ell : ℝ) := by
      field_simp [hell0] <;> ring
    rw [hfactor]
    field_simp [hell0, hell1] <;> ring
  rw [hprimeProduct]
  calc
    _ = ∏ ell ∈ e.primeFactors, halfProductDensity ell := by
      apply Finset.prod_congr rfl
      intro ell hell
      exact (halfProductDensity_prime (Nat.prime_of_mem_primeFactors hell)).symm
    _ = halfProductDensity e := halfProductDensity_isMultiplicative.prod_primeFactors hsq
    _ = _ := rfl

def ordinaryG (M z L : ℕ) : ℝ :=
  ∑ e ∈ (sieveProduct M z).divisors with e ≤ L, 1 / (Nat.totient e : ℝ)

theorem ordinary_normalizer (M z L : ℕ) :
    finiteSelbergNormalizer (ordinarySkeleton M z) L = ordinaryG M z L := by
  unfold finiteSelbergNormalizer ordinaryG
  apply Finset.sum_congr rfl
  intro e he
  exact ordinary_selbergTerms M z e (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he).1)

/-- These weights depend only on the external arithmetic modulus/centre,
cap and level. Both original complementary factors and X come later. -/
def ordinaryRho (N d z L : ℕ) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared (finiteSelbergWeight (ordinarySkeleton (d * N) z) L)

/-- Actual support and exact raw mass, with ordinary integer density. -/
def ordinaryRowSieve (N d z : ℕ) (X : ℝ) (p q : ℕ) : BoundingSieve :=
  { ordinarySkeleton (d * N) z with
    support := rowAPDiv N X p q d 1
    totalMass := ((rowAPDiv N X p q d 1).card : ℝ) }

theorem ordinaryRow_weight_eq (N d z L : ℕ) (X : ℝ) (p q : ℕ) :
    finiteSelbergWeight (ordinaryRowSieve N d z X p q) L =
      finiteSelbergWeight (ordinarySkeleton (d * N) z) L := rfl

theorem ordinaryRow_normalizer (N d z L : ℕ) (X : ℝ) (p q : ℕ) :
    finiteSelbergNormalizer (ordinaryRowSieve N d z X p q) L =
      ordinaryG (d * N) z L := ordinary_normalizer (d * N) z L

end
end ImbalancedChen.U9SemiprimeSwitch
