import ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Bounded finite-algebra continuation of the actual Δ8 measured k=1
mixed expectation. No analytic moment identity (M) is an assumption.
The fourth Dirichlet moment is reduced to its equality-partition kernel,
and the weighted kernel is expanded to the Phase14 signed coefficient.
This source has not been compiled or checked; all imports are held.
-/

namespace ImbalancedChen.P2Winner9MixedKOneFiniteCollapse

noncomputable section

open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9ActualEightSimplexMoment
open ImbalancedChen.P2Winner9NestedEightSimplexMoment
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
open ImbalancedChen.P2Winner9MixedZeroCoefficientCurvatureLink
open ImbalancedChen.P2Winner9MixedDegreeOnePolynomialMoment

def delta (i j : Fin 9) : ℤ := if i = j then 1 else 0

/-- Fifteen equality partitions of four labelled factors. -/
def kernel (a b c d : Fin 9) : ℤ :=
  1 + delta a b + delta a c + delta a d +
    delta b c + delta b d + delta c d +
    delta a b * delta c d +
    delta a c * delta b d +
    delta a d * delta b c +
    2 * (delta a b * delta a c + delta a b * delta a d +
      delta a c * delta a d + delta b c * delta b d) +
    6 * delta a b * delta a c * delta a d

/-- The degree is exactly four for every four labelled vertices, even
when indices repeat. This finite proof uses no certificate data. -/
theorem fourExponent_degree (a b c d : Fin 9) :
    fourExponent a b c d 0 +
      (List.ofFn (fun q : Fin 8 => fourExponent a b c d q.succ)).sum + 8 = 12 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    decide

/-- The factorial multiplicity is 1,2,4,6 or 24 according to the
equality partition. The 15-term kernel encodes all five cases. -/
theorem fourFactorial_kernel (a b c d : Fin 9) :
    (((fourExponent a b c d 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c d q.succ)) : Nat) : ℤ) =
      kernel a b c d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [kernel, delta, fourExponent, unitExponent,
      factorialProduct, List.ofFn]

/-- A bounded n=1 complete-homogeneous coefficient, independent of
moment calculus. -/
theorem homogeneous_one (y : Fin 9 → Nat) :
    (homogeneous y 1 : ℤ) = ∑ i : Fin 9, (y i : ℤ) := by
  classical
  simp [homogeneous, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-- Expand the equality-partition kernel under signed weights. The
right side is precisely the frozen degree-one coefficient, after the
source's finite `doubled_one` and `mixed_numerator_one` rewrites. -/
theorem weighted_kernel_mixedNumerator (d : SimplexData) (j : Fin 10) :
    (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
      (d.gaps a : ℤ) * (d.y b : ℤ) * d.deviations j c *
        d.deviations j e * kernel a b c e) =
      mixedNumerator d j 1 := by
  rw [mixed_numerator_one, doubled_one]
  rw [homogeneous_one]
  simp only [doubled, conv_zero, B1, B2, W0, W1, W2,
    Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, mul_one]
  simp [kernel, delta, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum, mul_add, add_mul, mul_ite] <;> ring

private theorem fourthMoment_kernel (a b c e : Fin 9) :
    (((fourExponent a b c e 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c e q.succ)) : Nat) : ℝ) /
        (((fourExponent a b c e 0) +
          (List.ofFn (fun q : Fin 8 => fourExponent a b c e q.succ)).sum + 8).factorial : ℝ) =
      (kernel a b c e : ℝ) / (12.factorial : ℝ) := by
  rw [fourExponent_degree]
  have h : (((fourExponent a b c e 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c e q.succ)) : Nat) : ℝ) =
      (kernel a b c e : ℝ) := by
    exact_mod_cast fourFactorial_kernel a b c e
  rw [h]

/-- Source-only candidate for the exact selected k=1 identity.
It uses the actual measured factorial sum and the bounded finite kernel,
not the analytic identity (M) as a hypothesis. -/
theorem actualMixedExpectation_eq_candidate (d : SimplexData) (j : Fin 10) :
    actualMixedExpectation d j =
      (mixedNumerator d j 1 : ℝ) /
        ((gapTotal d.gaps : ℝ) * d.U * d.L^2 * (10 * 11 * 12)) := by
  rw [actualMixedExpectation_eq_factorial_sum]
  simp_rw [fourthMoment_kernel]
  have hU : (d.U : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.UPos)
  have hL : (d.L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.LPos)
  have hG : (gapTotal d.gaps : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt d.gapsPos)
  rw [← weighted_kernel_mixedNumerator d j]
  simp only [gapVertices, yVertices, bVertices]
  push_cast
  field_simp [hU, hL, hG]
  ring

end

end ImbalancedChen.P2Winner9MixedKOneFiniteCollapse
