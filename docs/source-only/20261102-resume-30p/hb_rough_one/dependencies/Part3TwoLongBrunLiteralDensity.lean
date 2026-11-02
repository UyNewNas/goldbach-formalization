import Mathlib
import ImbalancedChen.Part3TwoLongActualBrunProfile

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This phase links the grouped binomial Brun coefficient from phase two to
the literal finite subset expansion of squarefree chart-prime divisors,
and records the exact finite reciprocal B2 density gap. A subset S of
the chart-prime alphabet represents d = product(S). Identifying all such
products with squarefree divisors in the physical coefficient still
requires the prime-factorization bridge in the caller.
-/

namespace ImbalancedChen.Part3.TwoLongBrunLiteralDensity

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongActualBrunProfile

noncomputable section

/-- Literal subset form of the truncated divisor coefficient evaluated at
n: only subsets whose every chart prime divides n appear. -/
def subsetBrunPolynomial (P : Finset ℕ) (n order : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (order + 1),
    ∑ S ∈ (P.filter (fun p => p ∣ n)).powersetCard k,
      (-1 : ℤ) ^ S.card

/-- Cardinality grouping recovers exactly the polynomial in phase two.
This is a finite identity, with no asymptotic or distribution input. -/
theorem subsetBrunPolynomial_eq (P : Finset ℕ) (n order : ℕ) :
    subsetBrunPolynomial P n order = brunPolynomial P n order := by
  unfold subsetBrunPolynomial brunPolynomial smallDivisorCount
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ S ∈ (P.filter (fun p => p ∣ n)).powersetCard k,
        (-1 : ℤ) ^ S.card)
      = ∑ S ∈ (P.filter (fun p => p ∣ n)).powersetCard k,
          (-1 : ℤ) ^ k := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [(Finset.mem_powersetCard.mp hS).2]
    _ = (-1 : ℤ) ^ k *
          (((P.filter (fun p => p ∣ n)).card).choose k : ℤ) := by
        simp [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_comm]

/-- Chart primes not dividing q are the only ones in the exact reciprocal
coprime density. This deletion works for every q, with no restriction on
the number or size of its factors. -/
def survivingPrimes (P : Finset ℕ) (q : ℕ) : Finset ℕ :=
  P.filter (fun p => ¬ p ∣ q)

def reciprocalSubsetMass (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (p : ℝ)⁻¹

/-- The exact elementary symmetric reciprocal mass at rank r. -/
def reciprocalSymmetric (P : Finset ℕ) (q r : ℕ) : ℝ :=
  ∑ S ∈ (survivingPrimes P q).powersetCard r,
    reciprocalSubsetMass S

/-- The literal truncated reciprocal A_q or its odd companion. -/
def reciprocalBrunDensity (P : Finset ℕ) (q order : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (order + 1),
    (-1 : ℝ) ^ k * reciprocalSymmetric P q k

def reciprocalUpper (j : ℕ) (P : Finset ℕ) (q : ℕ) : ℝ :=
  reciprocalBrunDensity P q (2 * j)

def reciprocalLower (j : ℕ) (P : Finset ℕ) (q : ℕ) : ℝ :=
  reciprocalBrunDensity P q (2 * j + 1)

/-- The manuscript's g_q is exactly the r=h+1 elementary symmetric sum,
before any H(z)^r/r! estimate is applied. -/
theorem reciprocalBrunGap_eq (j : ℕ) (P : Finset ℕ) (q : ℕ) :
    reciprocalUpper j P q - reciprocalLower j P q =
      reciprocalSymmetric P q (2 * j + 1) := by
  unfold reciprocalUpper reciprocalLower reciprocalBrunDensity
  rw [Finset.sum_range_succ]
  simp [pow_add, pow_mul]

theorem reciprocalSymmetric_nonneg (P : Finset ℕ) (q r : ℕ) :
    0 ≤ reciprocalSymmetric P q r := by
  unfold reciprocalSymmetric reciprocalSubsetMass
  positivity

theorem reciprocalBrunGap_nonneg (j : ℕ) (P : Finset ℕ) (q : ℕ) :
    0 ≤ reciprocalUpper j P q - reciprocalLower j P q := by
  rw [reciprocalBrunGap_eq]
  exact reciprocalSymmetric_nonneg P q _

/-- A genuine unit-sum smooth-core kernel. The right Fourier axis j=0
in the double Poisson identity cancels against the exact coprime mean.
The left axis uses inversion of the unit alphabet, stated separately
in the accompanying proof note. -/
def unitKloosterman {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (m n : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ,
    psi (m * (u : ZMod q) + n * ((u⁻¹ : (ZMod q)ˣ) : ZMod q))

def unitRamanujan {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (m : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, psi (m * (u : ZMod q))

theorem unitKloosterman_right_axis {q : ℕ} [NeZero q]
    (psi : ZMod q → ℂ) (m : ZMod q) :
    unitKloosterman psi m 0 = unitRamanujan psi m := by
  simp [unitKloosterman, unitRamanujan]

end

end ImbalancedChen.Part3.TwoLongBrunLiteralDensity
