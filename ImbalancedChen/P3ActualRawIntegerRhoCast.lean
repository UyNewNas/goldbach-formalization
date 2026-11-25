import ImbalancedChen.ActualSmallRoughAttachment
import Mathlib.Tactic

/-!
P3.6, frozen manuscript
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1,3(T),4(F).

The earlier small/rough attachment is a REAL function actualSmallRoughRho,
although its exact rough coefficient is integer Möbius (or zero), and its
two actual Rosser coefficients have only the values -1, 0, 1.

Here we construct an INTEGER coefficient on the identical original
small/rough physical modulus support, from the literal STRICT real-level
even/odd Rosser tests and the same retained first-exit rough coefficients.
We then prove its cast to the reals equals the EXISTING raw coefficient,
pointwise at every physical q, including q off support. This is not an
abstract integral-valuedness assumption and it does not change the policy,
physical modulus, multiplicity, or sign-sensitive small Rosser branch.

It does NOT identify the complete causal compiler's final integer rho_N
or its restoration scalars/global squarefree gate, and does not pay PP.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED pending pinned Lean checking.
-/

namespace ImbalancedChen.P3ActualRawIntegerRhoCast

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open MathlibNt.SieveTheory.LiLiuPrereqWF

/-- Literal integer lower Rosser coefficient. The STRICT real level L
and the provider's actual even-prefix cubic admissibility are unchanged. -/
def actualSmallRosserMinusInt (N cap : ℕ) (w L : ℝ) (a : ℕ) : ℤ :=
  if a ∈ (actualSmallPrimeProduct N cap w).divisors ∧ (a : ℝ) < L ∧
      SmallRosser.LowerAdmissibleSet L a.primeFactors
  then (-1 : ℤ) ^ a.primeFactors.card else 0

/-- Literal integer upper Rosser coefficient, with odd-prefix cubic test. -/
def actualSmallRosserPlusInt (N cap : ℕ) (w L : ℝ) (a : ℕ) : ℤ :=
  if a ∈ (actualSmallPrimeProduct N cap w).divisors ∧ (a : ℝ) < L ∧
      SmallRosser.UpperAdmissibleSet L a.primeFactors
  then (-1 : ℤ) ^ a.primeFactors.card else 0

theorem actualSmallRosserMinusInt_cast (N cap : ℕ) (w L : ℝ) (a : ℕ) :
    ((actualSmallRosserMinusInt N cap w L a : ℤ) : ℝ) =
      actualSmallRosserMinus N cap w L a := by
  by_cases h : a ∈ (actualSmallPrimeProduct N cap w).divisors ∧ (a : ℝ) < L ∧
      SmallRosser.LowerAdmissibleSet L a.primeFactors
  · simp [actualSmallRosserMinusInt, actualSmallRosserMinus,
      ActualSmallRosserProvider.lowerWeight, SmallRosser.lowerWeight_apply, h]
  · simp [actualSmallRosserMinusInt, actualSmallRosserMinus,
      ActualSmallRosserProvider.lowerWeight, SmallRosser.lowerWeight_apply, h]

theorem actualSmallRosserPlusInt_cast (N cap : ℕ) (w L : ℝ) (a : ℕ) :
    ((actualSmallRosserPlusInt N cap w L a : ℤ) : ℝ) =
      actualSmallRosserPlus N cap w L a := by
  by_cases h : a ∈ (actualSmallPrimeProduct N cap w).divisors ∧ (a : ℝ) < L ∧
      SmallRosser.UpperAdmissibleSet L a.primeFactors
  · simp [actualSmallRosserPlusInt, actualSmallRosserPlus,
      ActualSmallRosserProvider.upperWeight, SmallRosser.upperWeight_apply, h]
  · simp [actualSmallRosserPlusInt, actualSmallRosserPlus,
      ActualSmallRosserProvider.upperWeight, SmallRosser.upperWeight_apply, h]

/-- The actual selected rough coefficient, represented as the integer
Möbius coefficient that the original fixedRoughCoefficient casts to R. -/
def actualRoughInt (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (b : ℕ) : ℤ :=
  oddFirstExitRetainedCoefficient retainOdd (fun _ => (1 : ℝ))
    (roughPrimeUniverse N cap w z) b

theorem actualRoughInt_cast
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (b : ℕ) :
    ((actualRoughInt retainOdd N cap w z b : ℤ) : ℝ) =
      fixedRoughCoefficient retainOdd N cap w z b := by
  rfl

/-- SAME sign branch as signAttachedCoefficient:
positive rough coefficient selects the real Rosser UPPER coefficient,
negative rough coefficient selects the LOWER coefficient. -/
def actualRawPairInt (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (x : ℕ × ℕ) : ℤ :=
  actualRoughInt retainOdd N cap w z x.2 *
    (if 0 ≤ actualRoughInt retainOdd N cap w z x.2
     then actualSmallRosserPlusInt N cap w L x.1
     else actualSmallRosserMinusInt N cap w L x.1)

theorem actualRawPairInt_cast
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (x : ℕ × ℕ) :
    ((actualRawPairInt retainOdd N cap w z L x : ℤ) : ℝ) =
      smallRoughPairCoefficient
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) x := by
  by_cases h : 0 ≤ actualRoughInt retainOdd N cap w z x.2
  · have hr : 0 ≤ fixedRoughCoefficient retainOdd N cap w z x.2 := by
      rw [← actualRoughInt_cast]
      exact_mod_cast h
    simp [actualRawPairInt, smallRoughPairCoefficient,
      signAttachedCoefficient, h, hr, actualRoughInt_cast,
      actualSmallRosserPlusInt_cast]
  · have hr : ¬ 0 ≤ fixedRoughCoefficient retainOdd N cap w z x.2 := by
      intro hreal
      apply h
      rw [← actualRoughInt_cast] at hreal
      exact_mod_cast hreal
    simp [actualRawPairInt, smallRoughPairCoefficient,
      signAttachedCoefficient, h, hr, actualRoughInt_cast,
      actualSmallRosserMinusInt_cast]

/-- One actual INTEGER raw coefficient, on exactly the same noninjective
small/rough pair-fibre definition as the existing real physical rho.
This definition is total for every q and never evaluates the source integer. -/
def actualRawIntegerRho (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℤ :=
  ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w)
      (fixedRoughSupport retainOdd N cap w z) with x.1 * x.2 = q,
    actualRawPairInt retainOdd N cap w z L x

/-- Pointwise exact identity with the production REAL physical rho, not
merely equality of a bound or of its density. The same q, cutoff, labels,
pair multiplicities, first-exit policy and small Rosser signs are used. -/
theorem actualRawIntegerRho_cast
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    ((actualRawIntegerRho retainOdd N cap w z L q : ℤ) : ℝ) =
      actualSmallRoughRho retainOdd N cap w z L q := by
  simp only [actualRawIntegerRho, actualSmallRoughRho, smallRoughRho,
    Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact actualRawPairInt_cast retainOdd N cap w z L x

/-- Transfer the production one-bound to the genuine integer function. -/
theorem actualRawIntegerRho_abs_le_one
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    |actualRawIntegerRho retainOdd N cap w z L q| ≤ 1 := by
  have h := actualSmallRoughRho_abs_le_one retainOdd N cap w z L q
  rw [← actualRawIntegerRho_cast] at h
  exact_mod_cast h

/-- In fact the actual raw integer coefficient has precisely three possible
values. This is stronger than merely finding an integer in its real fibre. -/
theorem actualRawIntegerRho_trivalent
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    actualRawIntegerRho retainOdd N cap w z L q = -1 ∨
      actualRawIntegerRho retainOdd N cap w z L q = 0 ∨
      actualRawIntegerRho retainOdd N cap w z L q = 1 := by
  have h := actualRawIntegerRho_abs_le_one retainOdd N cap w z L q
  omega

/-- This SAME cast works inside the full physical signed sum. In
particular it does not replace rho by abs rho before applying the exact
coprime mean or change the original physical modulus family. -/
theorem actualRawIntegerRho_weighted_physical_sum
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (Q : Finset ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ Q, (actualRawIntegerRho retainOdd N cap w z L q : ℝ) * F q) =
      ∑ q ∈ Q, actualSmallRoughRho retainOdd N cap w z L q * F q := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [actualRawIntegerRho_cast]

end

end ImbalancedChen.P3ActualRawIntegerRhoCast
