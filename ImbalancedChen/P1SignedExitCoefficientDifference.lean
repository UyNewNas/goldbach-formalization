import ImbalancedChen.P1SignedExitPolicyComparison
import ImbalancedChen.FirstExitGenericModuli
import ImbalancedChen.PhysicalUpperWeightBridge

/-!
# One fixed modulus coefficient for a difference of historical policies

Both retained coefficients equal the same integer Möbius value at a common
modulus. Their difference therefore vanishes on the intersection and has
absolute value at most one on the union. This uses the actual supports fixed
with unit weights; the coefficient is not selected again for each evaluated
integer. The first-different-admission identity is transferred to that same
fixed modulus sum.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

def p1PolicyUnionModuli (oldPolicy newPolicy : Bool → List ℕ → Bool)
    (carrier : List ℕ) : Finset ℕ :=
  firstExitRetainedModuli newPolicy carrier ∪ firstExitRetainedModuli oldPolicy carrier

/-- A single fixed integer coefficient, with the new-minus-old orientation. -/
def p1PolicyCoefficientDifference (oldPolicy newPolicy : Bool → List ℕ → Bool)
    (carrier : List ℕ) (d : ℕ) : ℤ :=
  firstExitRetainedCoefficient newPolicy carrier d -
    firstExitRetainedCoefficient oldPolicy carrier d

theorem p1_policyCoefficientDifference_zero_on_intersection
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ)
    (hnew : d ∈ firstExitRetainedModuli newPolicy carrier)
    (hold : d ∈ firstExitRetainedModuli oldPolicy carrier) :
    p1PolicyCoefficientDifference oldPolicy newPolicy carrier d = 0 := by
  simp [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold]

theorem p1_policyCoefficientDifference_zero_outside_union
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ)
    (hd : d ∉ p1PolicyUnionModuli oldPolicy newPolicy carrier) :
    p1PolicyCoefficientDifference oldPolicy newPolicy carrier d = 0 := by
  have hnew : d ∉ firstExitRetainedModuli newPolicy carrier :=
    fun h => hd (Finset.mem_union_left _ h)
  have hold : d ∉ firstExitRetainedModuli oldPolicy carrier :=
    fun h => hd (Finset.mem_union_right _ h)
  simp [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold]

/-- Nonzero difference is supported only on the symmetric difference.
This support statement does not require prime or distinctness assumptions. -/
theorem p1_policyCoefficientDifference_ne_zero_mem_symmDifference
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ)
    (hd : p1PolicyCoefficientDifference oldPolicy newPolicy carrier d ≠ 0) :
    d ∈ (firstExitRetainedModuli newPolicy carrier \ firstExitRetainedModuli oldPolicy carrier) ∪
      (firstExitRetainedModuli oldPolicy carrier \ firstExitRetainedModuli newPolicy carrier) := by
  by_cases hnew : d ∈ firstExitRetainedModuli newPolicy carrier <;>
    by_cases hold : d ∈ firstExitRetainedModuli oldPolicy carrier
  · exact False.elim (hd (p1_policyCoefficientDifference_zero_on_intersection
      oldPolicy newPolicy carrier d hnew hold))
  · simp [hnew, hold]
  · simp [hnew, hold]
  · have hz : p1PolicyCoefficientDifference oldPolicy newPolicy carrier d = 0 := by
      simp [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold]
    exact False.elim (hd hz)

/-- The bound is one, since two occupied coefficients at the same modulus
are the identical Möbius value and cancel. -/
theorem p1_policyCoefficientDifference_abs_le_one
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ) :
    |p1PolicyCoefficientDifference oldPolicy newPolicy carrier d| ≤ 1 := by
  have hmu : |ArithmeticFunction.moebius d| ≤ (1 : ℤ) :=
    ArithmeticFunction.abs_moebius_le_one
  by_cases hnew : d ∈ firstExitRetainedModuli newPolicy carrier <;>
    by_cases hold : d ∈ firstExitRetainedModuli oldPolicy carrier
  · simp [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold]
  · simpa [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold] using hmu
  · simpa [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold] using hmu
  · simp [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold]

theorem p1_policyCoefficientDifference_real_abs_le_one
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ) :
    |(p1PolicyCoefficientDifference oldPolicy newPolicy carrier d : ℝ)| ≤ 1 := by
  exact_mod_cast p1_policyCoefficientDifference_abs_le_one oldPolicy newPolicy carrier d

/-- Padding both fixed supports into the union preserves the exact signed
finite sum, for any real modulus test. -/
theorem p1_fixedCoefficient_sub_eq_union_sum
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ firstExitRetainedModuli newPolicy carrier,
      (firstExitRetainedCoefficient newPolicy carrier d : ℝ) * f d) -
    (∑ d ∈ firstExitRetainedModuli oldPolicy carrier,
      (firstExitRetainedCoefficient oldPolicy carrier d : ℝ) * f d) =
    ∑ d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier,
      (p1PolicyCoefficientDifference oldPolicy newPolicy carrier d : ℝ) * f d := by
  have hnew :
      (∑ d ∈ firstExitRetainedModuli newPolicy carrier,
        (firstExitRetainedCoefficient newPolicy carrier d : ℝ) * f d) =
      ∑ d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier,
        (firstExitRetainedCoefficient newPolicy carrier d : ℝ) * f d := by
    apply Finset.sum_subset Finset.subset_union_left
    intro d _hd hnot
    simp [firstExitRetainedCoefficient, hnot]
  have hold :
      (∑ d ∈ firstExitRetainedModuli oldPolicy carrier,
        (firstExitRetainedCoefficient oldPolicy carrier d : ℝ) * f d) =
      ∑ d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier,
        (firstExitRetainedCoefficient oldPolicy carrier d : ℝ) * f d := by
    apply Finset.sum_subset Finset.subset_union_right
    intro d _hd hnot
    simp [firstExitRetainedCoefficient, hnot]
  rw [hnew, hold, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [p1PolicyCoefficientDifference, Int.cast_sub]
  ring

/-- Existing product injection is reused to transfer the two real tree
polynomials to the one fixed union coefficient. -/
theorem p1_retainedPolynomial_sub_eq_union_coefficient_sum
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hnodup : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) :
    firstExitRetainedPolynomial newPolicy h [] true 1 carrier -
      firstExitRetainedPolynomial oldPolicy h [] true 1 carrier =
    ∑ d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier,
      (p1PolicyCoefficientDifference oldPolicy newPolicy carrier d : ℝ) *
        d.primeFactors.prod h := by
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum newPolicy h carrier hnodup hprime,
    firstExitRetainedPolynomial_eq_retainedModuli_sum oldPolicy h carrier hnodup hprime]
  exact p1_fixedCoefficient_sub_eq_union_sum oldPolicy newPolicy carrier _

theorem p1_policyUnionModuli_squarefree
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p)
    {d : ℕ} (hd : d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier) : Squarefree d := by
  rcases Finset.mem_union.mp hd with hnew | hold
  · exact firstExitRetainedModuli_squarefree newPolicy carrier hnodup hprime hnew
  · exact firstExitRetainedModuli_squarefree oldPolicy carrier hnodup hprime hold

theorem p1_policyUnionModuli_primeFactors_mem
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p)
    {d p : ℕ} (hd : d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier)
    (hp : p ∈ d.primeFactors) : p ∈ carrier := by
  rcases Finset.mem_union.mp hd with hnew | hold
  · exact firstExitRetainedModuli_primeFactors_mem newPolicy carrier hnodup hprime hnew hp
  · exact firstExitRetainedModuli_primeFactors_mem oldPolicy carrier hnodup hprime hold hp

/-- For the actual distinct prime carrier the support is exactly the
symmetric difference, because every occupied modulus is squarefree. -/
theorem p1_policyCoefficientDifference_ne_zero_iff_mem_symmDifference
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p) (d : ℕ) :
    p1PolicyCoefficientDifference oldPolicy newPolicy carrier d ≠ 0 ↔
      d ∈ (firstExitRetainedModuli newPolicy carrier \ firstExitRetainedModuli oldPolicy carrier) ∪
        (firstExitRetainedModuli oldPolicy carrier \ firstExitRetainedModuli newPolicy carrier) := by
  constructor
  · exact p1_policyCoefficientDifference_ne_zero_mem_symmDifference oldPolicy newPolicy carrier d
  · intro hd
    rcases Finset.mem_union.mp hd with hnew | hold
    · obtain ⟨hnew, hold⟩ := Finset.mem_sdiff.mp hnew
      have hmu := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
        (firstExitRetainedModuli_squarefree newPolicy carrier hnodup hprime hnew)
      simpa [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold] using hmu
    · obtain ⟨hold, hnew⟩ := Finset.mem_sdiff.mp hold
      have hmu := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
        (firstExitRetainedModuli_squarefree oldPolicy carrier hnodup hprime hold)
      simpa [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold] using hmu

theorem p1_policyCoefficientDifference_abs_eq_one_on_symmDifference
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p) {d : ℕ}
    (hd : d ∈
      (firstExitRetainedModuli newPolicy carrier \ firstExitRetainedModuli oldPolicy carrier) ∪
        (firstExitRetainedModuli oldPolicy carrier \ firstExitRetainedModuli newPolicy carrier)) :
    |p1PolicyCoefficientDifference oldPolicy newPolicy carrier d| = 1 := by
  rcases Finset.mem_union.mp hd with hnew | hold
  · obtain ⟨hnew, hold⟩ := Finset.mem_sdiff.mp hnew
    have hmu := ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (firstExitRetainedModuli_squarefree newPolicy carrier hnodup hprime hnew)
    simpa [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold] using hmu
  · obtain ⟨hold, hnew⟩ := Finset.mem_sdiff.mp hold
    have hmu := ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (firstExitRetainedModuli_squarefree oldPolicy carrier hnodup hprime hold)
    simpa [p1PolicyCoefficientDifference, firstExitRetainedCoefficient, hnew, hold] using hmu

theorem p1_policyUnionModuli_coprime_target
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (N : ℕ) (hdeleted : ∀ p ∈ carrier, ¬p ∣ N)
    {d : ℕ} (hd : d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier) : d.Coprime N := by
  rw [← Nat.prod_primeFactors_of_squarefree
    (p1_policyUnionModuli_squarefree oldPolicy newPolicy carrier hnodup hprime hd),
    Nat.coprime_prod_left_iff]
  intro p hp
  have hpc := p1_policyUnionModuli_primeFactors_mem oldPolicy newPolicy carrier
    hnodup hprime hd hp
  exact (hprime p hpc).coprime_iff_not_dvd.mpr (hdeleted p hpc)

/-- One coefficient, fixed before `n`, evaluates every integer divisor
test, including `n = 0`. The same exact union is used for both sides. -/
theorem p1_retainedPolynomial_sub_eq_union_divisor_sum
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p) (n : ℤ) :
    firstExitRetainedPolynomial newPolicy (integerDivisorIndicator n) [] true 1 carrier -
      firstExitRetainedPolynomial oldPolicy (integerDivisorIndicator n) [] true 1 carrier =
    physicalDivisorSum (p1PolicyUnionModuli oldPolicy newPolicy carrier)
      (fun d => (p1PolicyCoefficientDifference oldPolicy newPolicy carrier d : ℝ)) n.natAbs := by
  rw [p1_retainedPolynomial_sub_eq_union_coefficient_sum
    oldPolicy newPolicy (integerDivisorIndicator n) carrier hnodup hprime]
  unfold physicalDivisorSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_integerDivisorIndicator
    (p1_policyUnionModuli_squarefree oldPolicy newPolicy carrier hnodup hprime hd) n]
  by_cases hdn : d ∣ n.natAbs <;> simp [hdn]

/-- The fixed union coefficient evaluates exactly the genuine first
different admissions, not a new coefficient chosen for the local weights. -/
theorem p1_union_coefficient_sum_eq_first_different_admissions
    (oldPolicy newPolicy : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hnodup : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) :
    (∑ d ∈ p1PolicyUnionModuli oldPolicy newPolicy carrier,
      (p1PolicyCoefficientDifference oldPolicy newPolicy carrier d : ℝ) *
        d.primeFactors.prod h) =
      let states := p1SignedExitStates (p1CommonAdmissionPolicy oldPolicy newPolicy)
        h [] true 1 carrier
      (((states.filter (p1AdmissionOnly newPolicy oldPolicy)).map
        (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) -
      (((states.filter (p1AdmissionOnly oldPolicy newPolicy)).map
        (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
          state.positive state.mass state.remaining)).sum) := by
  rw [← p1_retainedPolynomial_sub_eq_union_coefficient_sum
    oldPolicy newPolicy h carrier hnodup hprime]
  exact p1_policy_sub_eq_first_different_admissions oldPolicy newPolicy h [] carrier true 1

/-- The historical policies are evaluated on precisely the same T3-derived
prime tree and target-deleted rough carrier. -/
def p1HistoricalFourthFifthUnionModuli
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) : Finset ℕ :=
  p1PolicyUnionModuli (fourthCappedUpperPolicy base Q3 Q4)
    (fifthCappedUpperPolicy base Q3 Q5) (roughPrimeUniverse N cap 0 z)

def p1HistoricalFourthFifthCoefficientDifference
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (d : ℕ) : ℤ :=
  p1PolicyCoefficientDifference (fourthCappedUpperPolicy base Q3 Q4)
    (fifthCappedUpperPolicy base Q3 Q5) (roughPrimeUniverse N cap 0 z) d

theorem p1_actualHistoricalFourthFifth_difference_abs_le_one
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (d : ℕ) :
    |p1HistoricalFourthFifthCoefficientDifference base Q3 Q4 Q5 N cap z d| ≤ 1 := by
  exact p1_policyCoefficientDifference_abs_le_one _ _ _ d

theorem p1_actualHistoricalFourthFifth_difference_support
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (d : ℕ)
    (hd : p1HistoricalFourthFifthCoefficientDifference base Q3 Q4 Q5 N cap z d ≠ 0) :
    d ∈ (firstExitRetainedModuli (fifthCappedUpperPolicy base Q3 Q5)
        (roughPrimeUniverse N cap 0 z) \
        firstExitRetainedModuli (fourthCappedUpperPolicy base Q3 Q4)
          (roughPrimeUniverse N cap 0 z)) ∪
      (firstExitRetainedModuli (fourthCappedUpperPolicy base Q3 Q4)
        (roughPrimeUniverse N cap 0 z) \
        firstExitRetainedModuli (fifthCappedUpperPolicy base Q3 Q5)
          (roughPrimeUniverse N cap 0 z)) := by
  exact p1_policyCoefficientDifference_ne_zero_mem_symmDifference _ _ _ d hd

theorem p1_actualHistoricalFourthFifth_union_squarefree_coprime
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) {d : ℕ}
    (hd : d ∈ p1HistoricalFourthFifthUnionModuli base Q3 Q4 Q5 N cap z) :
    Squarefree d ∧ d.Coprime N := by
  constructor
  · exact p1_policyUnionModuli_squarefree _ _ _ (roughPrimeUniverse_nodup N cap 0 z)
      (fun _ hp => mem_roughPrimeUniverse_prime hp) hd
  · exact p1_policyUnionModuli_coprime_target _ _ _ (roughPrimeUniverse_nodup N cap 0 z)
      (fun _ hp => mem_roughPrimeUniverse_prime hp) N
      (fun _ hp => mem_roughPrimeUniverse_not_dvd hp) hd

theorem p1_actualHistoricalFourthFifth_polynomial_sub_eq_union_sum
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ) :
    firstExitRetainedPolynomial (fifthCappedUpperPolicy base Q3 Q5)
        h [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fourthCappedUpperPolicy base Q3 Q4)
        h [] true 1 (roughPrimeUniverse N cap 0 z) =
    ∑ d ∈ p1HistoricalFourthFifthUnionModuli base Q3 Q4 Q5 N cap z,
      (p1HistoricalFourthFifthCoefficientDifference base Q3 Q4 Q5 N cap z d : ℝ) *
        d.primeFactors.prod h := by
  exact p1_retainedPolynomial_sub_eq_union_coefficient_sum _ _ h _
    (roughPrimeUniverse_nodup N cap 0 z) (fun _ hp => mem_roughPrimeUniverse_prime hp)

theorem p1_actualHistoricalFourthFifth_integer_evaluation
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (n : ℤ) :
    firstExitRetainedPolynomial (fifthCappedUpperPolicy base Q3 Q5)
        (integerDivisorIndicator n) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fourthCappedUpperPolicy base Q3 Q4)
        (integerDivisorIndicator n) [] true 1 (roughPrimeUniverse N cap 0 z) =
    physicalDivisorSum (p1HistoricalFourthFifthUnionModuli base Q3 Q4 Q5 N cap z)
      (fun d => (p1HistoricalFourthFifthCoefficientDifference base Q3 Q4 Q5 N cap z d : ℝ))
      n.natAbs := by
  exact p1_retainedPolynomial_sub_eq_union_divisor_sum _ _ _
    (roughPrimeUniverse_nodup N cap 0 z) (fun _ hp => mem_roughPrimeUniverse_prime hp) n

end

end ImbalancedChen
