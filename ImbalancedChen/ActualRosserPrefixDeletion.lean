import ImbalancedChen.ActualSmallRosserDensity

/-!
# Selected prefix primes do not change the strict residual carrier

Every selected prefix prime is at least the residual cutoff `y`, whereas
the ordinary residual uses only primes strictly below `y`. Thus its moduli
are already coprime to the prefix product. Explicitly deleting those prefix
primes gives exactly the same prime carrier, weights, densities and Euler
product, at the same real level. This is a finite identity, with no change
to the target used for subsequent singular-series normalization.
-/

namespace ImbalancedChen

noncomputable section

theorem prime_below_cutoff_coprime_prefix
    (pre : List ℕ) (y : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ))
    {p : ℕ} (hp : p.Prime) (hpy : (p : ℝ) < y) : p.Coprime pre.prod := by
  rw [Nat.coprime_list_prod_right_iff]
  intro q hq
  apply (Nat.coprime_primes hp (hprefix q hq).1).mpr
  have hpq : (p : ℝ) < q := hpy.trans_le (hprefix q hq).2
  exact ne_of_lt (by exact_mod_cast hpq)

/-- A repeated factor from the selected prefix cannot enter any displayed
residual modulus, irrespective of the real Rosser level. -/
theorem actualSmallRosserSupport_coprime_prefix
    (N cap : ℕ) (pre : List ℕ) (y : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ))
    {d : ℕ} (hd : d ∈ actualSmallRosserSupport N cap y) : d.Coprime pre.prod := by
  rw [← Nat.prod_primeFactors_of_squarefree (actualSmallRosserSupport_squarefree N cap y hd),
    Nat.coprime_prod_left_iff]
  intro p hp
  exact prime_below_cutoff_coprime_prefix pre y hprefix
    (Nat.prime_of_mem_primeFactors hp)
    ((actualSmallRosserSupport_smallPrimeSupportedAt N cap y hd).2 p hp)

/-- Adding the already selected prime product to the excluded primes leaves
the residual carrier exactly unchanged, including the boundary `p=y`. -/
theorem actualSmallPrimeFinset_mul_prefix
    (N cap : ℕ) (pre : List ℕ) (y : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ)) :
    actualSmallPrimeFinset (N * pre.prod) cap y = actualSmallPrimeFinset N cap y := by
  ext p
  simp only [mem_actualSmallPrimeFinset]
  constructor
  · rintro ⟨hcap, hp, hnot, hpy⟩
    exact ⟨hcap, hp, fun hdiv => hnot (dvd_mul_of_dvd_left hdiv _), hpy⟩
  · rintro ⟨hcap, hp, hnot, hpy⟩
    refine ⟨hcap, hp, ?_, hpy⟩
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with hleft | hright
    · exact hnot hleft
    · exact (hp.coprime_iff_not_dvd.mp
        (prime_below_cutoff_coprime_prefix pre y hprefix hp hpy)) hright

theorem actualSmallRosserSupport_mul_prefix
    (N cap : ℕ) (pre : List ℕ) (y : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ)) :
    actualSmallRosserSupport (N * pre.prod) cap y = actualSmallRosserSupport N cap y := by
  simp only [actualSmallRosserSupport, actualSmallPrimeProduct,
    actualSmallPrimeFinset_mul_prefix N cap pre y hprefix]

theorem actualSmallRosserPlus_mul_prefix
    (N cap : ℕ) (pre : List ℕ) (y R : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ)) :
    actualSmallRosserPlus (N * pre.prod) cap y R = actualSmallRosserPlus N cap y R := by
  simp only [actualSmallRosserPlus, actualSmallPrimeProduct,
    actualSmallPrimeFinset_mul_prefix N cap pre y hprefix]

theorem actualSmallRosserMinus_mul_prefix
    (N cap : ℕ) (pre : List ℕ) (y R : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ)) :
    actualSmallRosserMinus (N * pre.prod) cap y R = actualSmallRosserMinus N cap y R := by
  simp only [actualSmallRosserMinus, actualSmallPrimeProduct,
    actualSmallPrimeFinset_mul_prefix N cap pre y hprefix]

theorem actualSmallRosserPlusDensity_mul_prefix
    (N cap : ℕ) (pre : List ℕ) (y R : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ)) :
    actualSmallRosserPlusDensity (N * pre.prod) cap y R =
      actualSmallRosserPlusDensity N cap y R := by
  simp only [actualSmallRosserPlusDensity,
    actualSmallRosserSupport_mul_prefix N cap pre y hprefix,
    actualSmallRosserPlus_mul_prefix N cap pre y R hprefix]

theorem actualSmallRosserMinusDensity_mul_prefix
    (N cap : ℕ) (pre : List ℕ) (y R : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ)) :
    actualSmallRosserMinusDensity (N * pre.prod) cap y R =
      actualSmallRosserMinusDensity N cap y R := by
  simp only [actualSmallRosserMinusDensity,
    actualSmallRosserSupport_mul_prefix N cap pre y hprefix,
    actualSmallRosserMinus_mul_prefix N cap pre y R hprefix]

theorem actualSmallEulerProduct_mul_prefix
    (N cap : ℕ) (pre : List ℕ) (y : ℝ)
    (hprefix : ∀ q ∈ pre, q.Prime ∧ y ≤ (q : ℝ)) :
    actualSmallEulerProduct (N * pre.prod) cap y = actualSmallEulerProduct N cap y := by
  simp only [actualSmallEulerProduct,
    actualSmallPrimeFinset_mul_prefix N cap pre y hprefix]

end

end ImbalancedChen
