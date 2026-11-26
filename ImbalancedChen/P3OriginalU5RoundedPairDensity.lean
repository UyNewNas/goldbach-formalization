import ImbalancedChen.P2LowerCanonicalRetainedTrace
import ImbalancedChen.P3OriginalU5RoundedCountInsertion

/-!
# Full-modulus density for the rounded original U5 rows

The rounded carrier uses the complete rough universe. Every prime of a
displayed quotient is strictly below the cutoff, so the external pair is
coprime to every displayed quotient. The reciprocal-totient sum at the
full modulus consequently factors for an arbitrary signed coefficient.
-/

namespace ImbalancedChen.P3OriginalU5RoundedPairDensity

noncomputable section
open scoped BigOperators
open P2LowerCanonicalRetainedTrace (canonical_subword_of_universe)
open P3OriginalU5RoundedCountInsertion (roundedRho roundedSupport)
open P5OriginalU5CausalFinite (attachment_gates cutoff pairSupport row_multiplier_rough)
open P5OriginalU5PlateauPrimeBV (fullModulus markedProduct)

/-- The external pair is coprime to each quotient in the complete rounded carrier. -/
theorem pair_coprime_of_mem_roundedSupport {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ} (hk : k ∈ roundedSupport N epsilon) :
    (t.1 * t.2).Coprime k := by
  obtain ⟨⟨s, r⟩, hsr, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hs, hr⟩ := Finset.mem_product.mp hsr
  have hwz := (attachment_gates hN hepsilon hepsilon8).2.2
  have hrough := row_multiplier_rough ht
  have hprimeCoprime (p : ℕ) (hp : p.Prime) (hpz : (p : ℝ) < cutoff N) :
      (t.1 * t.2).Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (fun hpd => (not_lt_of_ge (hrough p hp hpd)) hpz)).symm
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · rw [← Nat.prod_primeFactors_of_squarefree (actualSmallRosserSupport_squarefree _ _ _ hs)]
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact hprimeCoprime p (Nat.prime_of_mem_primeFactors hp)
      (((actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hs).2 p hp).trans_le hwz)
  · obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe _ _ _ _ hr
    rw [← hprod]
    apply Nat.coprime_list_prod_right_iff.mpr
    intro p hp
    have hpCarrier := hsub.subset hp
    exact hprimeCoprime p (mem_roughPrimeUniverse_prime hpCarrier)
      (mem_roughPrimeUniverse_upper hpCarrier)

/-- The reciprocal-totient sum retains both external primes in the denominator. -/
theorem fullModulus_density_eq {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (rho : ℕ → ℝ) :
    (∑ k ∈ roundedSupport N epsilon, rho k / (Nat.totient (fullModulus t k) : ℝ)) =
      physicalDensitySum (roundedSupport N epsilon) rho / (Nat.totient (t.1 * t.2) : ℝ) := by
  rw [physicalDensitySum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fullModulus, markedProduct,
    Nat.totient_mul (pair_coprime_of_mem_roundedSupport hN hepsilon hepsilon8 ht hk),
    Nat.cast_mul, div_mul_eq_div_div_swap]

/-- The same identity on the existing signed rounded output. -/
theorem roundedRho_fullModulus_density_eq {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (tau : ℝ) (policy : List ℕ → Bool) :
    (∑ k ∈ roundedSupport N epsilon,
      roundedRho N epsilon tau policy k / (Nat.totient (fullModulus t k) : ℝ)) =
      physicalDensitySum (roundedSupport N epsilon) (roundedRho N epsilon tau policy) /
        (Nat.totient (t.1 * t.2) : ℝ) :=
  fullModulus_density_eq hN hepsilon hepsilon8 ht (roundedRho N epsilon tau policy)

end
end ImbalancedChen.P3OriginalU5RoundedPairDensity
