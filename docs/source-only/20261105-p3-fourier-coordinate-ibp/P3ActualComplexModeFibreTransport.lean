import ImbalancedChen.P3ActualComplexPositionalGammaModes
import ImbalancedChen.P3ActualWeightedFineSameRho

/-!
P3.6 — exact finite transport of genuine COMPLEX positional Fourier modes.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
The previous source bounds complex gamma fibres pointwise. This file proves
the missing finite identity moving an arbitrary ordered-slot complex Fourier
mode (and a finite sum of such modes) through its literal full-product fibres.
It keeps each ORIGINAL repeated-label factorial, the exact physical modulus
kernel, and the SAME signed integer rho in count and coprime mean.

The weight is NOT assumed constant under within-label permutations; no
sorted-original W_T identity, triple-group factorisation, continuous Fourier
inversion, arithmetic error estimate or outside (M) input is asserted.
-/

namespace ImbalancedChen.P3ActualComplexModeFibreTransport
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualComplexPositionalGammaModes
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- True finite product-fibre partition for COMPLEX, ordered-tuple weights.
The mode can depend on every physical occurrence position. -/
theorem complex_weighted_sum_by_product
    (S : Finset (List ℕ)) (v : List ℕ → ℂ) (H : ℕ → ℂ) :
    (∑ ps ∈ S, v ps * H ps.prod) =
      ∑ n ∈ S.image List.prod,
        (∑ ps ∈ S.filter (fun ps => ps.prod = n), v ps) * H n := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun ps hps => Finset.mem_image_of_mem List.prod hps)
    (fun ps => v ps * H ps.prod)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ps hps
  rw [(Finset.mem_filter.mp hps).2]

/-- Exact complex normalized group transport: no change from original
M_group = product of the label factorials to a total-slot factorial. -/
theorem complexWeightedLabelGamma_sum_by_product
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : List ℕ → ℂ) (H : ℕ → ℂ) :
    (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
      v ps * H ps.prod) /
        (actualPrimeLabelBlocksFactorial blocks : ℂ) =
    ∑ n ∈ (actualPrimeSlotBox B
      (actualPrimeLabelBlocksWord blocks)).image List.prod,
        complexWeightedLabelGamma B blocks v n * H n := by
  let S := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  change (∑ ps ∈ S, v ps * H ps.prod) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ) =
    ∑ n ∈ S.image List.prod, complexWeightedLabelGamma B blocks v n * H n
  rw [complex_weighted_sum_by_product S v H, ← Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [complexWeightedLabelGamma]
  ring

/-- Finite Fourier amplitude sums commute with each ORIGINAL product fibre.
This is not the false assertion that a positional mode depends only on
the product; it is the literal finite sum over all ordered tuples. -/
theorem complexWeightedLabelGamma_modes
    {κ : Type*} (K : Finset κ) (amp : κ → ℂ)
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : κ → List ℕ → ℂ) (n : ℕ) :
    complexWeightedLabelGamma B blocks
      (fun ps => ∑ k ∈ K, amp k * v k ps) n =
    ∑ k ∈ K, amp k * complexWeightedLabelGamma B blocks (v k) n := by
  classical
  let S := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  let F := S.filter (fun ps => ps.prod = n)
  change (∑ ps ∈ F, ∑ k ∈ K, amp k * v k ps) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ) =
    ∑ k ∈ K, amp k *
      ((∑ ps ∈ F, v k ps) /
        (actualPrimeLabelBlocksFactorial blocks : ℂ))
  calc
    _ = (∑ k ∈ K, ∑ ps ∈ F, amp k * v k ps) /
        (actualPrimeLabelBlocksFactorial blocks : ℂ) := by
          rw [Finset.sum_comm]
    _ = ∑ k ∈ K,
          ((∑ ps ∈ F, amp k * v k ps) /
            (actualPrimeLabelBlocksFactorial blocks : ℂ)) := by
          rw [← Finset.sum_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum]
      ring

/-- An exact non-tautological finite-mode interchange: a literal sum of
COMPLEX positional weights is transported through the actual original
prime-label group with M_group exactly once, without an H^m mode-count
payment or a product-only-weight assumption. -/
theorem complex_finite_modes_group_transport
    {κ : Type*} (K : Finset κ) (amp : κ → ℂ)
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : κ → List ℕ → ℂ) (H : ℕ → ℂ) :
    (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
      (∑ k ∈ K, amp k * v k ps) * H ps.prod) /
        (actualPrimeLabelBlocksFactorial blocks : ℂ) =
    ∑ n ∈ (actualPrimeSlotBox B
      (actualPrimeLabelBlocksWord blocks)).image List.prod,
        (∑ k ∈ K,
          amp k * complexWeightedLabelGamma B blocks (v k) n) * H n := by
  calc
    _ = ∑ n ∈ (actualPrimeSlotBox B
        (actualPrimeLabelBlocksWord blocks)).image List.prod,
          complexWeightedLabelGamma B blocks
            (fun ps => ∑ k ∈ K, amp k * v k ps) n * H n :=
      complexWeightedLabelGamma_sum_by_product B blocks
        (fun ps => ∑ k ∈ K, amp k * v k ps) H
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [complexWeightedLabelGamma_modes K amp B blocks v n]

/-- SAME literal integer rho multiplies the full q-count-minus-exact-mean
kernel on both sides. The real fineKernel is cast unchanged to Complex.
This is a SINGLE GROUP finite identity; it does not claim that the original
W_T is a finite separated mode, or that all PP atoms are admitted. -/
theorem complex_finite_modes_same_rho_group
    {κ : Type*} (K : Finset κ) (amp : κ → ℂ)
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : κ → List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (T : ℕ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ((∑ ps ∈ actualPrimeSlotBox B
            (actualPrimeLabelBlocksWord blocks),
          (∑ k ∈ K, amp k * v k ps) *
            ((fineKernel T q ps.prod : ℝ) : ℂ)) /
        (actualPrimeLabelBlocksFactorial blocks : ℂ))) =
    ∑ q ∈ Q, (rho q : ℂ) *
      (∑ n ∈ (actualPrimeSlotBox B
          (actualPrimeLabelBlocksWord blocks)).image List.prod,
        (∑ k ∈ K, amp k *
          complexWeightedLabelGamma B blocks (v k) n) *
            ((fineKernel T q n : ℝ) : ℂ)) := by
  apply Finset.sum_congr rfl
  intro q hq
  exact congrArg (fun z : ℂ => (rho q : ℂ) * z)
    (complex_finite_modes_group_transport K amp B blocks v
      (fun n => ((fineKernel T q n : ℝ) : ℂ)))

end
end ImbalancedChen.P3ActualComplexModeFibreTransport
