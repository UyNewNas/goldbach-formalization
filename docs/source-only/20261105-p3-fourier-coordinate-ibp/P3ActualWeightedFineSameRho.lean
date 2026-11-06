import ImbalancedChen.ActualPrimeFineLabelSortedSelector
import ImbalancedChen.P3FullSignedModulusTail

/-!
P3.6 / original actual fine-label PP source, same integer rho.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Previous three-gamma identities transport tests F of the COMPLETE product,
but the original geometric W_T is a function of labelled PRIME TUPLES.
In particular it need not be invariant under permutations within a repeated
label. It must NOT be inserted into the previous product-only H lemma.

This packet instead pushes the ACTUAL strictly sorted original fine prime
tuples to their product fibres, retaining arbitrary tuple weight W, their
full Möbius factor, the original signed c and the exact SAME physical
congruence-minus-coprime-mean test for every q and integer rho(q).

No gamma one-bound is claimed for a weighted fibre. Connecting the separated
Fourier profiles to one-bounded physical atom coefficients remains internal.
No original PP source family is enlarged by this finite identity.
-/

namespace ImbalancedChen.P3ActualWeightedFineSameRho
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3PhysicalOriginalWInsertion

/-- The exact original product test. Fin 1 only records the full integer
product as one coordinate; it does not replace the actual physical modulus. -/
def fineKernel (T q n : ℕ) : ℝ :=
  exactCoprimeTest T q (fun _ : Fin 1 => n)

/-- The exact coprime mean is retained; no unrestricted 1/phi(q) is used. -/
theorem fineKernel_literal (T q n : ℕ) :
    fineKernel T q n =
      (if n % q = T % q then (1 : ℝ) else 0) -
        (if Nat.Coprime n q then (Nat.totient q : ℝ)⁻¹ else 0) := by
  simp [fineKernel, exactCoprimeTest]

theorem fineKernel_exact (T q : ℕ) (hcop : Nat.Coprime T q) :
    fineKernel T q T = 1 - (Nat.totient q : ℝ)⁻¹ := by
  rw [fineKernel_literal]
  simp [hcop]

/-- Original strictly decreasing labelled tuples, not an unrestricted
Cartesian product divided by M_J. Sorting and tuple-dependent W must not
be interchanged without a genuine permutation-invariance proof. -/
def weightedFineFibre (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (W : List ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τ blocks).filter
    (fun ps => ps.prod = n), W ps

/-- Direct, finite product-fibre pushforward preserving the weight on
each original tuple. This is valid even if W is not product-dependent. -/
theorem weighted_sum_by_product
    (S : Finset (List ℕ)) (W : List ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ ps ∈ S, W ps * F ps.prod) =
      ∑ n ∈ S.image List.prod,
        (∑ ps ∈ S.filter (fun ps => ps.prod = n), W ps) * F n := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun ps hps => Finset.mem_image_of_mem List.prod hps)
    (fun ps => W ps * F ps.prod)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ps hps
  rw [(Finset.mem_filter.mp hps).2]

/-- The actual original sorted prime tuple source with arbitrary labelled
W, original outside integer r in mu(r*n), and signed scalar c.
Both the count and mean use exactly the same rho and physical q. -/
def weightedSortedPP
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    ∑ ps ∈ actualPrimeFineLabelSortedTuples N τ blocks,
      (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
        W ps * fineKernel T q ps.prod

/-- The genuine arbitrary geometric weight is pushed to its OWN original
product fibres. Unlike the prior product-only gamma tensor, there is no
requirement W ps = F ps.prod, no artificial fibrewise one-bound, and
no replacement of the exact coprime mean. -/
theorem weightedSortedPP_fibre
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ) :
    weightedSortedPP N τ blocks Q rho T r c W =
      ∑ q ∈ Q, rho q *
        ∑ n ∈ (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod,
          (c * (ArithmeticFunction.moebius (r * n) : ℝ) *
            weightedFineFibre N τ blocks W n) * fineKernel T q n := by
  unfold weightedSortedPP
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  let S := actualPrimeFineLabelSortedTuples N τ blocks
  calc
    (∑ ps ∈ S,
      (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
        W ps * fineKernel T q ps.prod) =
      ∑ ps ∈ S, W ps *
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ) *
          fineKernel T q ps.prod) := by
        apply Finset.sum_congr rfl
        intro ps hps
        ring
    _ = ∑ n ∈ S.image List.prod,
      (∑ ps ∈ S.filter (fun ps => ps.prod = n), W ps) *
        (c * (ArithmeticFunction.moebius (r * n) : ℝ) *
          fineKernel T q n) :=
        weighted_sum_by_product S W
          (fun n => c * (ArithmeticFunction.moebius (r * n) : ℝ) *
            fineKernel T q n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      change (weightedFineFibre N τ blocks W n) *
        (c * (ArithmeticFunction.moebius (r * n) : ℝ) *
          fineKernel T q n) = _
      ring

/-- The exact complete-product=T contribution is factored AFTER the
original complete modulus sum. There is no tau(0), no claim that its
mass is small, and every q retains the original exact coprime mean. -/
theorem weightedSortedPP_exact_product
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ)
    (hcop : ∀ q ∈ Q, Nat.Coprime T q) :
    (∑ q ∈ Q, rho q *
      ∑ n ∈ ((actualPrimeFineLabelSortedTuples N τ blocks).image
        List.prod).filter (fun n => n = T),
        (c * (ArithmeticFunction.moebius (r * n) : ℝ) *
          weightedFineFibre N τ blocks W n) * fineKernel T q n) =
    (∑ q ∈ Q, rho q * (1 - (Nat.totient q : ℝ)⁻¹)) *
      (∑ n ∈ ((actualPrimeFineLabelSortedTuples N τ blocks).image
        List.prod).filter (fun n => n = T),
        c * (ArithmeticFunction.moebius (r * n) : ℝ) *
          weightedFineFibre N τ blocks W n) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hT : n = T := (Finset.mem_filter.mp hn).2
  subst n
  rw [fineKernel_exact T q (hcop q hq)]
  ring

end
end ImbalancedChen.P3ActualWeightedFineSameRho
