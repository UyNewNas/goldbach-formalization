import ImbalancedChen.P3ActualWeightedFineSameRho

/-!
P3.6 / exact original sorted-prime product-fibre uniqueness.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The original prime-labelled sorted source has an INJECTIVE complete-product
map, using the existing fixed-library theorem for strictly decreasing prime
tuples. Thus an arbitrary tuple-dependent geometric W, if pointwise
one-bounded on this actual source, gives a one-bounded sorted product fibre.
No assumption that W depends only on its product is needed.

This result does NOT make the fibre a separated convolution of the original
three gamma groups, does not bound a complete-modulus discrepancy, and does
not identify all physical W_T / rho_T compiler cases.
-/

namespace ImbalancedChen.P3ActualWeightedFibreInjective
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho

/-- The actual sorted source has exactly one tuple above each of its
complete products. This uses the genuine sorted PRIME product injectivity,
not a fictitious one-tuple-per-fibre premise. -/
theorem weightedFineFibre_mem_eq
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (W : List ℕ → ℝ) (ps : List ℕ)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τ blocks) :
    weightedFineFibre N τ blocks W ps.prod = W ps := by
  unfold weightedFineFibre
  have hsingle :
      (actualPrimeFineLabelSortedTuples N τ blocks).filter
        (fun qs => qs.prod = ps.prod) = {ps} := by
    ext qs
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hqs, hprod⟩
      exact actualPrimeFineLabelSortedTuples_product_injective
        N τ blocks qs hqs ps hps hprod
    · intro h
      subst qs
      exact ⟨hps, rfl⟩
  rw [hsingle]
  simp

/-- Off the ORIGINAL sorted prime-product support, the weighted fibre
vanishes without using a squarefree estimate or Fourier assumption. -/
theorem weightedFineFibre_zero_off
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (W : List ℕ → ℝ) (n : ℕ)
    (hn : n ∉ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod) :
    weightedFineFibre N τ blocks W n = 0 := by
  unfold weightedFineFibre
  apply Finset.sum_eq_zero
  intro ps hps
  exfalso
  obtain ⟨hsource, hprod⟩ := Finset.mem_filter.mp hps
  apply hn
  exact Finset.mem_image.mpr ⟨ps, hsource, hprod⟩

/-- Pointwise one-bounded ORIGINAL geometric weights stay one-bounded
after pushing to original sorted complete-product fibres. This is a
useful finite norm fact, but NOT a proof of gamma separation or PP. -/
theorem weightedFineFibre_abs_le_one
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (W : List ℕ → ℝ)
    (hW : ∀ ps ∈ actualPrimeFineLabelSortedTuples N τ blocks, |W ps| ≤ 1)
    (n : ℕ) :
    |weightedFineFibre N τ blocks W n| ≤ 1 := by
  by_cases hn : n ∈ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod
  · obtain ⟨ps, hps, hprod⟩ := Finset.mem_image.mp hn
    rw [← hprod, weightedFineFibre_mem_eq N τ blocks W ps hps]
    exact hW ps hps
  · rw [weightedFineFibre_zero_off N τ blocks W n hn]
    norm_num

end
end ImbalancedChen.P3ActualWeightedFibreInjective
