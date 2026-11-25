import ImbalancedChen.ChenPooledQuotientAP
import ImbalancedChen.CurrentChenP5OriginalU5CausalFinite
import ImbalancedChen.P3TaggedPhysicalRhoPushforward
import ImbalancedChen.P3ActualEvenLowerIntegerRho

/-!
# The original U5 physical integer rho

The definitions and fibre proofs are extracted verbatim from
P5OriginalU5PlateauPrimeBV, preserving that namespace and the original rho.
Source only; elaboration and kernel verification are pending.
-/
namespace ImbalancedChen.P5OriginalU5PlateauPrimeBV

noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P5OriginalU5CausalFinite
open P3ActualEvenLowerIntegerRho (actualEvenLowerIntegerRho actualEvenLowerIntegerRho_cast)
open P3ActualU6PhysicalRhoPushforward (taggedPhysicalModuli taggedPhysicalIntegerRho
  tagged_physical_mem tagged_physical_pushforward_identity)

abbrev Policy := (ℕ × ℕ) → List ℕ → Bool
abbrev markedProduct (t : ℕ × ℕ) := t.1 * t.2
abbrev fullModulus (t : ℕ × ℕ) (k : ℕ) := markedProduct t * k
abbrev primorial (N : ℕ) := sieveProduct N (Nat.ceil (cutoff N))

abbrev rowInteger (N : ℕ) (e : ℝ) (P : Policy) (t : ℕ × ℕ) (k : ℕ) : ℤ :=
  actualEvenLowerIntegerRho (P t) N (Nat.ceil (cutoff N))
    (smallCutoff N e) (cutoff N) (smallLevel N e) k

abbrev moduli (N : ℕ) (e : ℝ) (P : Policy) : Finset ℕ :=
  taggedPhysicalModuli (pairSupport N) (fun t => support N e (P t)) fullModulus

abbrev integerRho (N : ℕ) (e : ℝ) (P : Policy) : ℕ → ℤ :=
  taggedPhysicalIntegerRho (pairSupport N) (fun t => support N e (P t))
    fullModulus (rowInteger N e P)

/-- Every quotient in the displayed even-first-exit support divides the
original strict primorial, including rows with zero coefficient. -/
theorem quotient_mem_primorial {N : ℕ} {e : ℝ} (P : List ℕ → Bool)
    (hw : smallCutoff N e ≤ cutoff N) {k : ℕ} (hk : k ∈ support N e P) :
    k ∈ (primorial N).divisors := by
  rcases Finset.mem_image.mp hk with ⟨⟨s, r⟩, hsr, rfl⟩
  obtain ⟨hs, hr⟩ := Finset.mem_product.mp hsr
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hs)
    (fixedEvenRoughSupport_roughPrimeSupportedAt _ _ _ _ _ hr)
  have hrough : r ∣ primorial N := by
    apply (squarefree_dvd_iff_primeFactors_dvd
      (fixedEvenRoughSupport_squarefree _ _ _ _ _ hr)).mpr
    intro p hp
    have h := fixedEvenRoughSupport_primeFactors_mem _ _ _ _ _ hr hp
    have hmem : p ∈ sievePrimes N (Nat.ceil (cutoff N)) :=
      mem_sievePrimes.mpr ⟨Nat.lt_ceil.mpr (mem_roughPrimeUniverse_upper h),
        mem_roughPrimeUniverse_prime h, mem_roughPrimeUniverse_not_dvd h⟩
    exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem
  exact Nat.mem_divisors.mpr ⟨hcop.mul_dvd_of_dvd_of_dvd
    (actualSmallRosserSupport_dvd_sieveProduct_ceil _ _ _ _ hw hs) hrough,
    (sieveProduct_squarefree N (Nat.ceil (cutoff N))).ne_zero⟩

/-- In the actual U5 family the full modulus determines both ordered outer
labels and the quotient. The lower small/rough coefficient still includes
its own complete signed occurrence sum. -/
theorem original_fibre_unique {N : ℕ} {e : ℝ} (P : Policy)
    (hw : smallCutoff N e ≤ cutoff N) {t u : ℕ × ℕ} {k l : ℕ}
    (ht : t ∈ pairSupport N) (hk : k ∈ support N e (P t))
    (hu : u ∈ pairSupport N) (hl : l ∈ support N e (P u))
    (heq : fullModulus t k = fullModulus u l) : t = u ∧ k = l := by
  obtain ⟨hprod, hkl⟩ := chenQuotient_product_factors_unique
    (chenY5PrimeSelector_sieve_data ht).2.2 (chenY5PrimeSelector_sieve_data hu).2.2
    (quotient_mem_primorial (P t) hw hk) (quotient_mem_primorial (P u) hw hl) heq
  exact ⟨chenY5PrimeSelector_multiplier_injOn N _ _ ht hu hprod, hkl⟩

/-- Evaluate the pre-existing integer fibre sum at an actual complete
modulus. This supplies the BV one-bound even after all tags are pooled. -/
theorem integerRho_at_original {N : ℕ} {e : ℝ} (P : Policy)
    (hw : smallCutoff N e ≤ cutoff N) {t : ℕ × ℕ} {k : ℕ}
    (ht : t ∈ pairSupport N) (hk : k ∈ support N e (P t)) :
    integerRho N e P (fullModulus t k) = rowInteger N e P t k := by
  change (∑ u ∈ pairSupport N, ∑ l ∈ support N e (P u),
    if fullModulus u l = fullModulus t k then rowInteger N e P u l else 0) = _
  calc
    _ = ∑ l ∈ support N e (P t),
          if fullModulus t l = fullModulus t k then rowInteger N e P t l else 0 := by
        apply Finset.sum_eq_single_of_mem t ht
        intro u hu hne
        apply Finset.sum_eq_zero
        intro l hl
        exact if_neg (fun h => hne (original_fibre_unique P hw hu hl ht hk h).1)
    _ = (if fullModulus t k = fullModulus t k then rowInteger N e P t k else 0) := by
        apply Finset.sum_eq_single_of_mem k hk
        intro l hl hne
        exact if_neg (fun h => hne (original_fibre_unique P hw ht hl ht hk h).2)
    _ = _ := if_pos rfl

end
end ImbalancedChen.P5OriginalU5PlateauPrimeBV
