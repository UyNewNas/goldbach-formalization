import ImbalancedChen.ActualPrimeBoxMass
import ImbalancedChen.RoughAbsoluteDensity

/-! Existing finite prime-interval supplier. Extracted without changing any
declaration or proof bytes from P15 c6b89774822580c731a236ac66dcd7466ac8a0e6.
Only dependency ownership is changed; formal acceptance remains pending. -/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
namespace P1OriginalFourthMovingPrimeIntervalBound

/-- The degree-zero and degree-one terms of the positive finite Euler
product. The proof does not invoke a prime-counting asymptotic. -/
private theorem one_add_reciprocal_sum_le_euler (S : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    1 + ∑ p ∈ S, 1 / ((p : ℝ) - 1) ≤
      ∏ p ∈ S, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (hprime p (Finset.mem_insert_self p S)).one_lt
    have hxp : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
    have hsum : 0 ≤ ∑ q ∈ S, 1 / ((q : ℝ) - 1) := by
      apply Finset.sum_nonneg
      intro q hq
      have hq1 : (1 : ℝ) < q := by
        exact_mod_cast (hprime q (Finset.mem_insert_of_mem hq)).one_lt
      positivity
    have hih : 1 + ∑ q ∈ S, 1 / ((q : ℝ) - 1) ≤
        ∏ q ∈ S, (1 + 1 / ((q : ℝ) - 1)) := by
      apply ih
      intro q hq
      exact hprime q (Finset.mem_insert_of_mem hq)
    rw [Finset.sum_insert hp, Finset.prod_insert hp]
    have hmul := mul_le_mul_of_nonneg_left hih (by linarith :
      0 ≤ 1 + 1 / ((p : ℝ) - 1))
    nlinarith [mul_nonneg hxp hsum]

/-- Uniform real-endpoint interval mass, valid when the last-prime
exponents move with `N`. The pinned constant precedes every target, cap,
and endpoint. The strict upper endpoint and target deletion are literal. -/
theorem exists_uniform_reciprocal_interval_bound :
    ∃ K : ℝ, 1 < K ∧ ∀ (N cap : ℕ), Even N →
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        (∑ p ∈ roughPrimeFinset N cap w z, 1 / ((p : ℝ) - 1)) ≤
          Real.log z / Real.log w * (1 + K / Real.log w) - 1 := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N cap hEven w z hw hwz
  let P := roughPrimeFinset N cap w z
  have hp : ∀ p ∈ P, Nat.Prime p ∧ 2 < p :=
    fun _ h => roughPrimeFinset_odd_of_even hEven h
  have hsum : 1 + ∑ p ∈ P, 1 / ((p : ℝ) - 1) ≤
      ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) :=
    one_add_reciprocal_sum_le_euler P (fun p h => (hp p h).1)
  have hprod := roughPrime_eulerProduct_le_inverseProduct N cap w z hEven
  have hM := hinterval P hp w z hw hwz
    (fun p h => (mem_roughPrimeFinset.mp h).2.2.2)
  change (∑ p ∈ P, 1 / ((p : ℝ) - 1)) ≤ _
  linarith [hsum.trans (hprod.trans hM)]

end P1OriginalFourthMovingPrimeIntervalBound
end
end ImbalancedChen
