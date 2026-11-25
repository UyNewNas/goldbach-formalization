import ImbalancedChen.ActualLowerSmallRoughAttachment
import ImbalancedChen.CurrentChenP5CausalRhoFactorization
import ImbalancedChen.P3ActualRawIntegerRhoCast
import Mathlib.Tactic

/-!
P3.6, manuscript frozen at
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1,3(T),4(F).

The previous P3 actual integer RAW attachment used the odd first-exit
UPPER sieve: nonnegative rough coefficients select upper Rosser.
The actual quotient/retained lower rows instead use EVEN first exits
and the OPPOSITE Rosser branch (nonnegative selects lower).
These physical coefficients must not be identified with each other.

This packet constructs the integer EVEN-EXIT LOWER coefficient from
the literal fixed even rough Möbius producer and original small Rosser
tests, proves its pointwise cast to actualLowerSmallRoughRho, and
identifies its signed physical-prefix expansion with the existing
P5CausalRhoFactorization coefficient and label set. The latter is
only read as a fixed source, not edited or re-proved here.

No assertion identifies this lower coefficient or the earlier upper
RAW coefficient with the full final compiler rho_N. No PP discrepancy
is assumed or paid. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEvenLowerIntegerRho
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRawIntegerRhoCast

/-- The original even first-exit retained rough Möbius atom, as an
integer before its real cast. This is NOT oddFirstExitRetainedCoefficient. -/
def actualEvenRoughInt (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (b : ℕ) : ℤ :=
  firstExitRetainedCoefficient (evenFirstExitPolicy retainEven)
    (roughPrimeUniverse N cap w z) b

theorem actualEvenRoughInt_cast
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (b : ℕ) :
    ((actualEvenRoughInt retainEven N cap w z b : ℤ) : ℝ) =
      fixedEvenRoughCoefficient retainEven N cap w z b := by
  rfl

/-- LOWER signed branch: c>=0 selects beta-minus, c<0 selects beta-plus.
The strict Rosser level and its original admissibility tests are reused
without a surrogate coefficient or new coefficient-size premise. -/
def actualEvenLowerPairInt (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (x : ℕ × ℕ) : ℤ :=
  actualEvenRoughInt retainEven N cap w z x.2 *
    (if 0 ≤ actualEvenRoughInt retainEven N cap w z x.2
     then actualSmallRosserMinusInt N cap w L x.1
     else actualSmallRosserPlusInt N cap w L x.1)

theorem actualEvenLowerPairInt_cast
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (x : ℕ × ℕ) :
    ((actualEvenLowerPairInt retainEven N cap w z L x : ℤ) : ℝ) =
      smallRoughPairCoefficient
        (fixedEvenRoughCoefficient retainEven N cap w z)
        (actualSmallRosserPlus N cap w L)
        (actualSmallRosserMinus N cap w L) x := by
  by_cases h : 0 ≤ actualEvenRoughInt retainEven N cap w z x.2
  · have hr : 0 ≤ fixedEvenRoughCoefficient retainEven N cap w z x.2 := by
      rw [← actualEvenRoughInt_cast]
      exact_mod_cast h
    simp [actualEvenLowerPairInt, smallRoughPairCoefficient,
      signAttachedCoefficient, h, hr, actualEvenRoughInt_cast,
      actualSmallRosserMinusInt_cast]
  · have hr : ¬ 0 ≤ fixedEvenRoughCoefficient retainEven N cap w z x.2 := by
      intro hreal
      apply h
      rw [← actualEvenRoughInt_cast] at hreal
      exact_mod_cast hreal
    simp [actualEvenLowerPairInt, smallRoughPairCoefficient,
      signAttachedCoefficient, h, hr, actualEvenRoughInt_cast,
      actualSmallRosserPlusInt_cast]

/-- All pair multiplicities at the same literal integer modulus q are
preserved. In the original disjoint small/rough support this fibre is
at most a singleton, but no injectivity assumption is needed here. -/
def actualEvenLowerIntegerRho (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℤ :=
  ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w)
      (fixedEvenRoughSupport retainEven N cap w z) with x.1 * x.2 = q,
    actualEvenLowerPairInt retainEven N cap w z L x

theorem actualEvenLowerIntegerRho_cast
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    ((actualEvenLowerIntegerRho retainEven N cap w z L q : ℤ) : ℝ) =
      actualLowerSmallRoughRho retainEven N cap w z L q := by
  simp only [actualEvenLowerIntegerRho, actualLowerSmallRoughRho,
    smallRoughRho, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact actualEvenLowerPairInt_cast retainEven N cap w z L x

/-- Exact integer one-bound is inherited from the actual even-exit
lower sieve, not from the preceding odd-exit upper coefficient. -/
theorem actualEvenLowerIntegerRho_abs_le_one
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    |actualEvenLowerIntegerRho retainEven N cap w z L q| ≤ 1 := by
  have h := actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q
  rw [← actualEvenLowerIntegerRho_cast] at h
  exact_mod_cast h

theorem actualEvenLowerIntegerRho_trivalent
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    actualEvenLowerIntegerRho retainEven N cap w z L q = -1 ∨
      actualEvenLowerIntegerRho retainEven N cap w z L q = 0 ∨
      actualEvenLowerIntegerRho retainEven N cap w z L q = 1 := by
  have h := actualEvenLowerIntegerRho_abs_le_one retainEven N cap w z L q
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  omega

/-- This is the EXISTING real even-exit lower PAIR coefficient used by
the actual causal quotient rows, not the old odd-exit upper coefficient. -/
theorem actualEvenLowerPairInt_eq_P5_coefficient
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (x : ℕ × ℕ) :
    ((actualEvenLowerPairInt retainEven N cap w z L x : ℤ) : ℝ) =
      ImbalancedChen.P5CausalRhoFactorization.coefficient
        retainEven N cap w z L x := by
  rw [actualEvenLowerPairInt_cast]
  rfl

/-- Real and integer even-exit lower sources have the SAME signed
coefficient on every physical q, including q outside support. -/
theorem actualEvenLowerIntegerRho_signed_sum
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (Q : Finset ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ Q, (actualEvenLowerIntegerRho retainEven N cap w z L q : ℝ) * F q) =
      ∑ q ∈ Q, actualLowerSmallRoughRho retainEven N cap w z L q * F q := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [actualEvenLowerIntegerRho_cast]

/-- The genuine labelled lower quotient expansion carries the physical
prefix b: the modulus remains b*s*r, with the original even retained
pair labels, multiplicities and signed weight. No coprime mean is
simplified or introduced by this finite reindexing. -/
theorem actualEvenLowerIntegerRho_prefix_fubini
    (retainEven : List ℕ → Bool) (N cap b : ℕ)
    (w z L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      (actualEvenLowerIntegerRho retainEven N cap w z L q : ℝ) *
        F (b * q)) =
      ∑ x ∈ ImbalancedChen.P5CausalRhoFactorization.pairs
          retainEven N cap w z,
        (actualEvenLowerPairInt retainEven N cap w z L x : ℝ) *
          F ((b * x.1) * x.2) := by
  calc
    _ = ∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
          actualLowerSmallRoughRho retainEven N cap w z L q *
            F (b * q) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [actualEvenLowerIntegerRho_cast]
    _ = ∑ x ∈ ImbalancedChen.P5CausalRhoFactorization.pairs
            retainEven N cap w z,
          ImbalancedChen.P5CausalRhoFactorization.coefficient
            retainEven N cap w z L x * F ((b * x.1) * x.2) :=
        ImbalancedChen.P5CausalRhoFactorization.signed_physical_sum_fubini
          retainEven N cap b w z L F
    _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [actualEvenLowerPairInt_eq_P5_coefficient]

end
end ImbalancedChen.P3ActualEvenLowerIntegerRho
