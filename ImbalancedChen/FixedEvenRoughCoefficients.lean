import ImbalancedChen.FirstExitGenericModuli
import ImbalancedChen.ActualPrimePresieveSplit
import ImbalancedChen.ActualSmallRoughAttachment

/-!
# Fixed actual coefficients with even first exits

The support is selected once using the exact even-exit policy on the actual
rough prime carrier. It is independent of the integer later tested. The
same Mobius coefficient has a genuine divisor-sum minorant and an exact
reciprocal-totient density dictionary. Neither the lower divisor sum nor
the lower small-prime weight is asserted to be nonnegative.
-/

namespace ImbalancedChen

noncomputable section

/-- The actual fixed support for a policy that may reject even prefixes. -/
def fixedEvenRoughSupport (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  firstExitRetainedModuli (evenFirstExitPolicy retainEven) (roughPrimeUniverse N cap w z)

/-- The literal Mobius coefficient on this fixed support, zero elsewhere. -/
def fixedEvenRoughCoefficient (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) : ℝ :=
  (firstExitRetainedCoefficient (evenFirstExitPolicy retainEven)
    (roughPrimeUniverse N cap w z) d : ℝ)

theorem fixedEvenRoughSupport_squarefree
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedEvenRoughSupport retainEven N cap w z) : Squarefree d :=
  firstExitRetainedModuli_squarefree (evenFirstExitPolicy retainEven)
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
    (fun _ hp => mem_roughPrimeUniverse_prime hp) hd

theorem fixedEvenRoughSupport_primeFactors_mem
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d p : ℕ}
    (hd : d ∈ fixedEvenRoughSupport retainEven N cap w z) (hp : p ∈ d.primeFactors) :
    p ∈ roughPrimeUniverse N cap w z :=
  firstExitRetainedModuli_primeFactors_mem (evenFirstExitPolicy retainEven)
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
    (fun _ hq => mem_roughPrimeUniverse_prime hq) hd hp

theorem fixedEvenRoughSupport_roughPrimeSupportedAt
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedEvenRoughSupport retainEven N cap w z) : RoughPrimeSupportedAt w d := by
  refine ⟨(fixedEvenRoughSupport_squarefree retainEven N cap w z hd).ne_zero, ?_⟩
  intro p hp
  exact mem_roughPrimeUniverse_lower
    (fixedEvenRoughSupport_primeFactors_mem retainEven N cap w z hd hp)

theorem fixedEvenRoughSupport_coprime_target
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedEvenRoughSupport retainEven N cap w z) : d.Coprime N := by
  rw [← Nat.prod_primeFactors_of_squarefree
    (fixedEvenRoughSupport_squarefree retainEven N cap w z hd), Nat.coprime_prod_left_iff]
  intro p hp
  have hpc := fixedEvenRoughSupport_primeFactors_mem retainEven N cap w z hd hp
  exact (mem_roughPrimeUniverse_prime hpc).coprime_iff_not_dvd.mpr
    (mem_roughPrimeUniverse_not_dvd hpc)

theorem fixedEvenRoughCoefficient_abs_le_one
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    |fixedEvenRoughCoefficient retainEven N cap w z d| ≤ 1 := by
  unfold fixedEvenRoughCoefficient
  exact_mod_cast firstExitRetainedCoefficient_abs_le_one
    (evenFirstExitPolicy retainEven) (roughPrimeUniverse N cap w z) d

/-- The same fixed coefficients represent every integer test, including zero. -/
theorem evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDivisorSum
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (n : ℤ) :
    evenFirstExitRetainedPolynomial retainEven (integerDivisorIndicator n)
        (roughPrimeUniverse N cap w z) =
      supportedDivisorSum (fixedEvenRoughSupport retainEven N cap w z)
        (fixedEvenRoughCoefficient retainEven N cap w z) n.natAbs := by
  rw [evenFirstExitRetainedPolynomial,
    firstExitRetainedPolynomial_eq_retainedModuli_sum (evenFirstExitPolicy retainEven)
      (integerDivisorIndicator n) (roughPrimeUniverse N cap w z)
      (roughPrimeUniverse_nodup N cap w z) (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  unfold supportedDivisorSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_integerDivisorIndicator
    (fixedEvenRoughSupport_squarefree retainEven N cap w z hd) n]
  by_cases hdn : d ∣ n.natAbs <;> simp [hdn, fixedEvenRoughCoefficient]

/-- Even first exits subtract nonnegative exit masses from the Euler product. -/
theorem evenFirstExitRetainedPolynomial_le_product
    {α : Type*} (retainEven : List α → Bool) (h : α → ℝ) (carrier : List α)
    (hh : ∀ p ∈ carrier, 0 ≤ h p ∧ h p ≤ 1) :
    evenFirstExitRetainedPolynomial retainEven h carrier ≤
      (carrier.map fun p => 1 - h p).prod := by
  rw [evenFirstExitRetainedPolynomial,
    firstExitRetainedPolynomial_eq_product_add_correction]
  simp only [signedTreeCoefficient_true, one_mul]
  exact add_le_of_nonpos_right (firstExitCorrection_nonpos_of_odd_retained
    (evenFirstExitPolicy retainEven) h [] carrier true 1
    (evenFirstExitPolicy_odd retainEven) zero_le_one hh)

/-- The actual fixed divisor sum is a minorant of the full half-open rough
interval indicator, with no positivity restriction on the tested integer. -/
theorem fixedEvenRoughDivisorSum_le_roughIndicator
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    supportedDivisorSum (fixedEvenRoughSupport retainEven N cap w z)
        (fixedEvenRoughCoefficient retainEven N cap w z) n.natAbs ≤
      actualIntervalRoughIndicator N w z n := by
  classical
  rw [← evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDivisorSum]
  have h := evenFirstExitRetainedPolynomial_le_product retainEven
    (integerDivisorIndicator n) (roughPrimeUniverse N cap w z) (by
      intro p _hp
      by_cases hpn : (p : ℤ) ∣ n <;> simp [integerDivisorIndicator, hpn])
  change evenFirstExitRetainedPolynomial retainEven (integerDivisorIndicator n)
      (roughPrimeUniverse N cap w z) ≤
    finiteIntegerRoughIndicator (roughPrimeUniverse N cap w z) n at h
  rw [finiteIntegerRoughIndicator_eq_indicator] at h
  simpa only [actualIntervalRoughIndicator,
    mem_roughPrimeUniverse_iff_of_cutoff_le_cap (N := N) (w := w) hzcap] using h

/-- The actual lower tree density uses its same fixed support and coefficients. -/
theorem evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    evenFirstExitRetainedPolynomial retainEven
        (fun p => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap w z)
        (fixedEvenRoughCoefficient retainEven N cap w z) := by
  rw [evenFirstExitRetainedPolynomial,
    firstExitRetainedPolynomial_eq_retainedModuli_sum (evenFirstExitPolicy retainEven)
      (fun p => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap w z)
      (roughPrimeUniverse_nodup N cap w z) (fun _ hp => mem_roughPrimeUniverse_prime hp)]
  unfold reciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro d hd
  rw [primeFactors_prod_reciprocalTotient
    (fixedEvenRoughSupport_squarefree retainEven N cap w z hd)]
  simp only [fixedEvenRoughCoefficient, div_eq_mul_inv, one_mul]

end

end ImbalancedChen
