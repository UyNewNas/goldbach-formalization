import ImbalancedChen.P2OriginalI3ActualUpperContinuation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The upper quotient polynomials supplied by the actual I3 continuation are
literal original provider coefficients on their strict residual carrier.
This gives their genuine divisor count and reciprocal-totient mean, without
replacing the y-separated carrier by all primes below the endpoint.
-/
namespace ImbalancedChen.P2OriginalI3OrdinaryPlusCountDensity
noncomputable section
open scoped BigOperators

theorem ordinaryPlus_quotient_divisor_dictionary
    (R : ℝ) (carrier : List ℕ) (hR : 1 < R)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime)
    (n : ℤ) :
    firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy false R)
      (integerDivisorIndicator n) [] true 1 carrier =
      physicalDivisorSum (firstExitRetainedModuli (ordinaryRosserRetainedPolicy false R) carrier)
        (ordinaryRosserWeight false carrier.prod R) n.natAbs := by
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum _ _ _ hsort.nodup hprime]
  unfold physicalDivisorSum
  apply Finset.sum_congr rfl
  intro d hd
  have hsf := firstExitRetainedModuli_squarefree
    (ordinaryRosserRetainedPolicy false R) carrier hsort.nodup hprime hd
  rw [firstExitRetainedCoefficient_ordinaryRosser false R hR carrier hsort hprime d,
    primeFactors_prod_integerDivisorIndicator hsf n]
  by_cases hdn : d ∣ n.natAbs <;> simp [hdn]

theorem ordinaryPlus_quotient_density_dictionary
    (R : ℝ) (carrier : List ℕ) (hR : 1 < R)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime) :
    firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy false R)
      (fun p => 1 / ((p : ℝ)-1)) [] true 1 carrier =
      reciprocalTotientDensity
        (firstExitRetainedModuli (ordinaryRosserRetainedPolicy false R) carrier)
        (ordinaryRosserWeight false carrier.prod R) := by
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum _ _ _ hsort.nodup hprime]
  unfold reciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d hd
  have hsf := firstExitRetainedModuli_squarefree
    (ordinaryRosserRetainedPolicy false R) carrier hsort.nodup hprime hd
  rw [firstExitRetainedCoefficient_ordinaryRosser false R hR carrier hsort hprime d,
    primeFactors_prod_reciprocalTotient hsf]
  ring

end
end ImbalancedChen.P2OriginalI3OrdinaryPlusCountDensity
