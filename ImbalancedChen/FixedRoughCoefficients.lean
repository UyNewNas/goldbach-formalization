import ImbalancedChen.RoughPrimeUniverse
import ImbalancedChen.SmallRoughAttachment
import Mathlib.Tactic

/-!
# Rough coefficients fixed independently of the evaluated integer

The retained leaf records contain local masses, but the retained prime
selections depend only on the causal policy. We prove this independence
before evaluating the polynomial at divisibility indicators. Consequently
one fixed modulus support and one fixed coefficient function work for every
integer, including zero. No distribution or density estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The tree topology does not depend on local weights or incoming mass. -/
theorem firstExitRetainedLeaves_selected_independent
    {α : Type*} (retained : Bool → List α → Bool) (h₁ h₂ : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass₁ mass₂ : ℝ) :
    (firstExitRetainedLeaves retained h₁ selectedPrefix positive mass₁ remaining).map
        FirstExitLeaf.selected =
      (firstExitRetainedLeaves retained h₂ selectedPrefix positive mass₂ remaining).map
        FirstExitLeaf.selected := by
  induction remaining generalizing selectedPrefix positive mass₁ mass₂ with
  | nil => simp [firstExitRetainedLeaves]
  | cons p ps ih =>
      by_cases hr : retained (!positive) (p :: selectedPrefix) = true
      · simp only [firstExitRetainedLeaves, hr, if_true, List.map_append]
        rw [ih selectedPrefix positive mass₁ mass₂,
          ih (p :: selectedPrefix) (!positive) (mass₁ * h₁ p) (mass₂ * h₂ p)]
      · simp only [firstExitRetainedLeaves, if_neg hr, List.append_nil]
        exact ih selectedPrefix positive mass₁ mass₂

/-- The natural modulus carrier is independent of the local test function. -/
theorem oddFirstExitRetainedModuli_independent
    (retainOdd : List ℕ → Bool) (h₁ h₂ : ℕ → ℝ) (carrier : List ℕ) :
    oddFirstExitRetainedModuli retainOdd h₁ carrier =
      oddFirstExitRetainedModuli retainOdd h₂ carrier := by
  have h := congrArg (fun xs : List (List ℕ) => (xs.map List.prod).toFinset)
    (firstExitRetainedLeaves_selected_independent (oddFirstExitPolicy retainOdd)
      h₁ h₂ [] carrier true 1 1)
  simpa only [List.map_map, Function.comp_def, oddFirstExitRetainedModuli,
    oddFirstExitRetainedLeaves] using h

theorem oddFirstExitRetainedCoefficient_independent
    (retainOdd : List ℕ → Bool) (h₁ h₂ : ℕ → ℝ) (carrier : List ℕ) (d : ℕ) :
    oddFirstExitRetainedCoefficient retainOdd h₁ carrier d =
      oddFirstExitRetainedCoefficient retainOdd h₂ carrier d := by
  unfold oddFirstExitRetainedCoefficient
  rw [oddFirstExitRetainedModuli_independent retainOdd h₁ h₂ carrier]

/-- The fixed rough support, before any integer is evaluated. -/
def fixedRoughSupport (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  oddFirstExitRetainedModuli retainOdd (fun _ => 1) (roughPrimeUniverse N cap w z)

/-- Möbius on the fixed retained support and zero off it. -/
def fixedRoughCoefficient (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (d : ℕ) : ℝ :=
  (oddFirstExitRetainedCoefficient retainOdd (fun _ => 1)
    (roughPrimeUniverse N cap w z) d : ℝ)

theorem fixedRoughSupport_squarefree
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) : Squarefree d :=
  mem_oddFirstExitRetainedModuli_squarefree retainOdd (fun _ => 1)
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) d hd

/-- Each prime factor of a supported modulus belongs to the actual carrier. -/
theorem fixedRoughSupport_primeFactors_mem
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d p : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) (hp : p ∈ d.primeFactors) :
    p ∈ roughPrimeUniverse N cap w z := by
  rcases (mem_oddFirstExitRetainedModuli retainOdd (fun _ => 1)
    (roughPrimeUniverse N cap w z) d).mp hd with ⟨leaf, hleaf, rfl⟩
  rw [mem_oddFirstExitRetainedLeaves_primeFactors_selectedProd retainOdd (fun _ => 1)
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) leaf hleaf] at hp
  have hsub := mem_oddFirstExitRetainedLeaves_selected_reverse_sublist retainOdd
    (fun _ => 1) (roughPrimeUniverse N cap w z) leaf hleaf
  exact hsub.subset (by simpa using hp)

theorem fixedRoughSupport_roughPrimeSupportedAt
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) : RoughPrimeSupportedAt w d := by
  refine ⟨(fixedRoughSupport_squarefree retainOdd N cap w z hd).ne_zero, ?_⟩
  intro p hp
  exact mem_roughPrimeUniverse_lower
    (fixedRoughSupport_primeFactors_mem retainOdd N cap w z hd hp)

theorem fixedRoughSupport_coprime_target
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) : d.Coprime N := by
  rw [← Nat.prod_primeFactors_of_squarefree
    (fixedRoughSupport_squarefree retainOdd N cap w z hd), Nat.coprime_prod_left_iff]
  intro p hp
  have hpc := fixedRoughSupport_primeFactors_mem retainOdd N cap w z hd hp
  exact (mem_roughPrimeUniverse_prime hpc).coprime_iff_not_dvd.mpr
    (mem_roughPrimeUniverse_not_dvd hpc)

theorem fixedRoughCoefficient_abs_le_one
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    |fixedRoughCoefficient retainOdd N cap w z d| ≤ 1 := by
  unfold fixedRoughCoefficient oddFirstExitRetainedCoefficient
  split
  · exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  · norm_num

/-- Squarefreeness makes divisibility equivalent to divisibility by each
prime factor, including when the dividend is zero. -/
theorem squarefree_dvd_iff_primeFactors_dvd {d n : ℕ} (hd : Squarefree d) :
    d ∣ n ↔ ∀ p ∈ d.primeFactors, p ∣ n := by
  constructor
  · intro h p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.prod_primeFactors_dvd_iff hn]
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, h p hp, hn⟩

/-- The local indicator product is exactly the modulus divisibility test. -/
theorem primeFactors_prod_integerDivisorIndicator
    {d : ℕ} (hd : Squarefree d) (n : ℤ) :
    d.primeFactors.prod (integerDivisorIndicator n) =
      if d ∣ n.natAbs then (1 : ℝ) else 0 := by
  classical
  by_cases hdn : d ∣ n.natAbs
  · rw [if_pos hdn]
    apply Finset.prod_eq_one
    intro p hp
    have hpn := (squarefree_dvd_iff_primeFactors_dvd hd).mp hdn p hp
    simp [integerDivisorIndicator, Int.natCast_dvd, hpn]
  · rw [if_neg hdn]
    have hnot : ¬∀ p ∈ d.primeFactors, p ∣ n.natAbs :=
      fun h => hdn ((squarefree_dvd_iff_primeFactors_dvd hd).mpr h)
    push Not at hnot
    rcases hnot with ⟨p, hp, hpn⟩
    exact Finset.prod_eq_zero hp (by simp [integerDivisorIndicator, Int.natCast_dvd, hpn])

/-- Evaluating the rough tree equals a divisor sum with fixed coefficients. -/
theorem oddFirstExitRetainedPolynomial_eq_fixedRoughDivisorSum
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (n : ℤ) :
    oddFirstExitRetainedPolynomial retainOdd (integerDivisorIndicator n)
        (roughPrimeUniverse N cap w z) =
      supportedDivisorSum (fixedRoughSupport retainOdd N cap w z)
        (fixedRoughCoefficient retainOdd N cap w z) n.natAbs := by
  rw [oddFirstExitRetainedPolynomial_eq_leaves_sum,
    roughPrimeRetainedLeaves_sum_eq_retainedModuli_sum,
    oddFirstExitRetainedModuli_independent retainOdd (integerDivisorIndicator n)
      (fun _ => 1)]
  unfold supportedDivisorSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_integerDivisorIndicator
    (fixedRoughSupport_squarefree retainOdd N cap w z hd) n,
    oddFirstExitRetainedCoefficient_independent retainOdd (integerDivisorIndicator n)
      (fun _ => 1)]
  by_cases hdn : d ∣ n.natAbs <;> simp [hdn, fixedRoughCoefficient]

/-- The fixed divisor coefficient majorizes the literal rough-prime
indicator on every integer. It is not selected anew for each argument. -/
theorem roughIndicator_le_fixedRoughDivisorSum
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    (@ite ℝ (∀ p, (p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) →
      ¬(p : ℤ) ∣ n) (Classical.propDecidable _) 1 0) ≤
      supportedDivisorSum (fixedRoughSupport retainOdd N cap w z)
        (fixedRoughCoefficient retainOdd N cap w z) n.natAbs := by
  rw [← oddFirstExitRetainedPolynomial_eq_fixedRoughDivisorSum]
  exact manuscriptRoughIndicator_le_oddFirstExitRetainedPolynomial
    retainOdd N cap w z hzcap n

end

end ImbalancedChen
