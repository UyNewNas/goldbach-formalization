import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.CoprimeRecentering

/-!
# P4B: attached-modulus coprimality on the actual real source

SOURCE-ONLY / YELLOW / UNCOMPILED.

Every displayed modulus is covered, including displayed zero coefficients.
The source, coefficient, sieve ceiling, and manuscript lower cutoff are
exactly those in ActualUpperCountingInputs. The existing theorem for the
whole coprime correction is neither assumed nor modified here.
-/

namespace ImbalancedChen.P4BCoprimeArithmetic

noncomputable section
open Filter Topology
open scoped BigOperators

/-- The attached displayed carrier divides the very same sieve product;
no covering assumption on the enumeration cap is needed. -/
theorem attachedModulus_dvd_sieveProduct
    {nu r epsilon : ℝ} (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N d : ℕ} (hN : 1 ≤ N)
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    d ∣ sieveProduct N (Nat.ceil ((N : ℝ) ^ (nu * r))) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact actualSmallRoughModuli_dvd_sieveProduct_ceil (retain N) N (cap N) _ _
    (Real.rpow_le_rpow_of_exponent_le hNreal
      (mul_le_mul_of_nonneg_left hepsilonR hnu.le)) hd

/-- This is pointwise coprimality of the literal source integer, rather
than merely cancellation after summing correction terms. -/
theorem source_coprime_attachedModulus_of_gate
    {b T nu r epsilon : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N m d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ T ^ (b / (1 + b)))
    (hm : m ∈ realHalfProductSource b N T)
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    Nat.Coprime m d := by
  exact realHalfProductSource_coprime_of_dvd_sieveProduct hb hT hgate hm
    (attachedModulus_dvd_sieveProduct hnu hepsilonR retain cap hN hd)

/-- The coprime mask deletes no member, for each displayed modulus. -/
theorem source_filter_coprime_eq_self_of_gate
    {b T nu r epsilon : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ T ^ (b / (1 + b)))
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    (realHalfProductSource b N T).filter (fun m => Nat.Coprime m d) =
      realHalfProductSource b N T := by
  classical
  apply Finset.filter_eq_self.mpr
  intro m hm
  exact source_coprime_attachedModulus_of_gate hb hT hnu hepsilonR
    retain cap hN hgate hm hd

/-- The actual per-modulus coprime mass is the full source cardinality. -/
theorem coprimeMass_eq_card_of_gate
    {b T nu r epsilon : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ T ^ (b / (1 + b)))
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    realHalfProductCoprimeMass b N T d =
      ((realHalfProductSource b N T).card : ℝ) := by
  exact realHalfProductCoprimeMass_eq_card_of_gate hb hT hgate
    (attachedModulus_dvd_sieveProduct hnu hepsilonR retain cap hN hd)

/-- Each literal correction summand vanishes separately, without any
nonzero-coefficient assumption or sign restriction. -/
theorem correction_summand_eq_zero_of_gate
    {b T nu r epsilon : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ T ^ (b / (1 + b)))
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    attachedUpperCoefficient nu r epsilon retain cap N d *
      ((realHalfProductCoprimeMass b N T d -
        ((realHalfProductSource b N T).card : ℝ)) / (Nat.totient d : ℝ)) = 0 := by
  rw [coprimeMass_eq_card_of_gate hb hT hnu hepsilonR retain cap hN hgate hd]
  simp only [sub_self, zero_div, mul_zero]

/-- The generic weighted interface, for any signed source weight, loses
its coprime mask as well. -/
theorem finiteCoprimeMass_eq_sourceMass_of_gate
    {b T nu r epsilon : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ T ^ (b / (1 + b)))
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N)
    (weight : ℕ → ℝ) :
    finiteCoprimeMass (realHalfProductSource b N T) weight d =
      finiteSourceMass (realHalfProductSource b N T) weight := by
  unfold finiteCoprimeMass finiteSourceMass
  rw [source_filter_coprime_eq_self_of_gate hb hT hnu hepsilonR
    retain cap hN hgate hd]

/-- On the actual source the corrected progression is exactly the
uncorrected progression centered by total source mass. All residues,
including the moving residue N, are allowed. -/
theorem primitiveDiscrepancy_eq_uncorrected_of_gate
    {b T nu r epsilon : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ T ^ (b / (1 + b)))
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N)
    (weight : ℕ → ℝ) (a : ℕ) :
    finitePrimitiveDiscrepancy (realHalfProductSource b N T) weight a d =
      finiteCongruenceMass (realHalfProductSource b N T) weight a d -
        finiteSourceMass (realHalfProductSource b N T) weight / (Nat.totient d : ℝ) := by
  unfold finitePrimitiveDiscrepancy
  rw [finiteCoprimeMass_eq_sourceMass_of_gate hb hT hnu hepsilonR
    retain cap hN hgate hd weight]

/-- The same attached signed distribution sum can therefore be written
using total source cardinality at each modulus. -/
theorem distribution_eq_uncorrected_of_gate
    {b T nu r epsilon : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ T ^ (b / (1 + b))) :
    realPhysicalDistributionError b N T
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) =
      ∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d *
          (realHalfProductCongruenceMass b N T d -
            ((realHalfProductSource b N T).card : ℝ) / (Nat.totient d : ℝ)) := by
  unfold realPhysicalDistributionError
  apply Finset.sum_congr rfl
  intro d hd
  rw [coprimeMass_eq_card_of_gate hb hT hnu hepsilonR retain cap hN hgate hd]

/-- The manuscript exponent gap supplies the gate for every source
member and every displayed attached modulus at once. This strengthens
whole-sum correction vanishing without taking that theorem as a premise. -/
theorem eventually_manuscript_attached_coprime_identities
    {b kappa nu r epsilon : ℝ} (hb : 0 < b) (hnu : 0 < nu)
    (hr : 0 ≤ r) (hepsilonR : epsilon ^ 2 ≤ r)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        (∀ m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N),
          Nat.Coprime m d) ∧
        realHalfProductCoprimeMass b N (manuscriptHalfProductCutoff kappa N) d =
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) ∧
        attachedUpperCoefficient nu r epsilon retain cap N d *
          ((realHalfProductCoprimeMass b N (manuscriptHalfProductCutoff kappa N) d -
            ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ)) /
              (Nat.totient d : ℝ)) = 0 ∧
        (∀ (weight : ℕ → ℝ) (a : ℕ),
          finitePrimitiveDiscrepancy
              (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
              weight a d =
            finiteCongruenceMass
                (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
                weight a d -
              finiteSourceMass
                  (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
                  weight / (Nat.totient d : ℝ)) := by
  filter_upwards [eventually_manuscript_sieve_gate hb (mul_nonneg hnu.le hr) hgap,
    eventually_ge_atTop (1 : ℕ)] with N hgate hN
  intro d hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    exact source_coprime_attachedModulus_of_gate hb hgate.1 hnu hepsilonR
      retain cap hN hgate.2 hm hd
  · exact coprimeMass_eq_card_of_gate hb hgate.1 hnu hepsilonR
      retain cap hN hgate.2 hd
  · exact correction_summand_eq_zero_of_gate hb hgate.1 hnu hepsilonR
      retain cap hN hgate.2 hd
  · intro weight a
    exact primitiveDiscrepancy_eq_uncorrected_of_gate hb hgate.1 hnu hepsilonR
      retain cap hN hgate.2 hd weight a

end
end ImbalancedChen.P4BCoprimeArithmetic
