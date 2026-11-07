import ImbalancedChen.P3ActualTaggedUnsortedSameRho
import ImbalancedChen.P3ActualWeightedFineSameRho

/-!
P3.6 / manuscript §§3 (T), 4 (F) — MARKED RESIDUAL source arithmetic.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

A marked prime factor r remains OUTSIDE the residual prime-word factorial:
the residual labels alone determine M_res. The literal Möbius factor
mu(r * product) is retained on the COMPLETE marked integer product r * residualProduct.
Both the residue count and exact coprime mean test r * residualProduct
against T with the same signed integer rho.

This packet isolates the FULL product r*n=T exceptional fibre AFTER the full
signed physical-modulus sum, without tau(0). It proves the factorization,
NOT a small bound for that exceptional fibre. The original marked-atom
compiler's scalar, occurrence word and physical Q_T/rho_T are not
identified here; nor is continuous W_T Fourier inversion established.
-/

namespace ImbalancedChen.P3ActualMarkedResidualExactProduct
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualTaggedUnsortedSameRho
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3ActualFrozenCanonicalUnsortedGamma
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- Exactly the original marked Möbius coefficient on the *complete*
marked integer product, with the actual count-minus-coprime-mean kernel.
The marked prime product r does NOT enter the residual factorial. -/
def markedResidualKernel (r T q n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius (r * n) : ℝ) : ℂ) *
    ((fineKernel T q (r * n) : ℝ) : ℂ)

/-- The exact physical coprime factor is real-valued, not 1/phi(q)
unconditionally: the coprimality indicator remains in fineKernel. -/
def exactCoprimeFactor (q : ℕ) : ℂ :=
  (((1 : ℝ) - (Nat.totient q : ℝ)⁻¹) : ℂ)

/-- On the exceptional product=T fibre the indicator is 1, provided the
ORIGINAL physical modulus is coprime to T. No estimate is asserted. -/
theorem markedResidualKernel_exact (r T q n : ℕ)
    (hfull : r * n = T) (hcop : Nat.Coprime T q) :
    markedResidualKernel r T q n =
      ((ArithmeticFunction.moebius T : ℝ) : ℂ) *
        exactCoprimeFactor q := by
  unfold markedResidualKernel exactCoprimeFactor
  rw [hfull, fineKernel_exact T q hcop]

/-- Split a finite genuine signed source into exact product=T and
nonzero product-minus-T fibres, retaining the SAME rho and precise
coprime mean in each term. This step does not use tau(product-T). -/
theorem marked_source_split_exact_off {ι : Type*}
    (S : Finset ι) (product : ι → ℕ) (weight : ι → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (r T : ℕ) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ t ∈ S, weight t * markedResidualKernel r T q (product t)) =
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ t ∈ S.filter (fun t => r * product t = T),
        weight t * markedResidualKernel r T q (product t)) +
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ t ∈ S.filter (fun t => r * product t ≠ T),
        weight t * markedResidualKernel r T q (product t)) := by
  classical
  calc
    _ = ∑ q ∈ Q, (rho q : ℂ) *
      ((∑ t ∈ S.filter (fun t => r * product t = T),
          weight t * markedResidualKernel r T q (product t)) +
       (∑ t ∈ S.filter (fun t => r * product t ≠ T),
          weight t * markedResidualKernel r T q (product t))) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]

/-- Once the physical coprimality hypothesis is checked, the exceptional
fibre factors *after* the whole signed modulus sum, for arbitrary complex
Fourier weights (no positivity or symmetry). This does NOT bound its mass.
The modulus factor may be signed; absolute values cannot be dropped. -/
theorem marked_exact_product_after_modulus {ι : Type*}
    (S : Finset ι) (product : ι → ℕ) (weight : ι → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (r T : ℕ)
    (hcop : ∀ q ∈ Q, Nat.Coprime T q) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ t ∈ S.filter (fun t => r * product t = T),
        weight t * markedResidualKernel r T q (product t)) =
    (((ArithmeticFunction.moebius T : ℝ) : ℂ) *
      (∑ q ∈ Q, (rho q : ℂ) * exactCoprimeFactor q)) *
      (∑ t ∈ S.filter (fun t => r * product t = T), weight t) := by
  classical
  let ST := S.filter (fun t => r * product t = T)
  let mu : ℂ := ((ArithmeticFunction.moebius T : ℝ) : ℂ)
  have hinner (q : ℕ) (hq : q ∈ Q) :
      (∑ t ∈ ST, weight t * markedResidualKernel r T q (product t)) =
        (∑ t ∈ ST, weight t) * (mu * exactCoprimeFactor q) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    have htT : r * product t = T := (Finset.mem_filter.mp ht).2
    rw [markedResidualKernel_exact r T q (product t) htT (hcop q hq)]
    rfl
  calc
    _ = ∑ q ∈ Q, (rho q : ℂ) *
      ((∑ t ∈ ST, weight t) * (mu * exactCoprimeFactor q)) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [hinner q hq]
    _ = ∑ q ∈ Q, (mu * ((rho q : ℂ) * exactCoprimeFactor q)) *
        (∑ t ∈ ST, weight t) := by
        apply Finset.sum_congr rfl
        intro q hq
        ring
    _ = (mu * (∑ q ∈ Q, (rho q : ℂ) * exactCoprimeFactor q)) *
        (∑ t ∈ ST, weight t) := by
        rw [Finset.sum_mul, Finset.mul_sum]
    _ = _ := rfl

/-- A marked full-product exception is possible only if its outside marked
factor divides T. This is a genuine restriction, not a divisor-moment bound. -/
theorem marked_exact_fibre_empty_of_not_dvd {ι : Type*}
    (S : Finset ι) (product : ι → ℕ) (r T : ℕ)
    (hnot : ¬ r ∣ T) :
    S.filter (fun t => r * product t = T) = ∅ := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ht
  exact hnot ⟨product t, ht.2.symm⟩

/-- Consequently no signed-rho marked exact-product contribution survives
when r does not divide T; no condition on the Fourier weights is needed. -/
theorem marked_exact_product_zero_of_not_dvd {ι : Type*}
    (S : Finset ι) (product : ι → ℕ) (weight : ι → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (r T : ℕ)
    (hnot : ¬ r ∣ T) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ t ∈ S.filter (fun t => r * product t = T),
        weight t * markedResidualKernel r T q (product t)) = 0 := by
  classical
  rw [marked_exact_fibre_empty_of_not_dvd S product r T hnot]
  simp

/-- TRUE three frozen residual physical boxes, original ID-position modes
and M_res computed from the residual label word only. r is the separate
marked product, and c is its (not yet compiler-identified) external signed
restoring scalar. No marked labels are silently folded into M_res.
The exact r * residualProduct = T exception is retained, not bounded. -/
theorem actual_frozen_marked_residual_exact_T {n : ℕ} {κ : Type*}
    (K : Finset κ) (amp : κ → ℂ)
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upperLabel : ℕ → ℕ)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n)) (eta : κ → Fin n → ℝ)
    (U : Fin n → ℝ) (c : ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (r T : ℕ)
    (hcop : ∀ q ∈ Q, Nat.Coprime T q) :
    let pLabel : Fin 3 → ℕ := fun j => label (p j)
    let tailLabel := tail.map label
    let residualBlocks := canonicalFineBlocks
      (pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel)
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let B := actualPrimeFineLabelFinset N τ
    let S₀ := actualPrimeSlotBox B (ids.1.map label)
    let S₁ := actualPrimeSlotBox B (ids.2.1.map label)
    let S₂ := actualPrimeSlotBox B (ids.2.2.map label)
    let source := S₀.product (S₁.product S₂)
    let residualProduct : (List ℕ × (List ℕ × List ℕ)) → ℕ :=
      fun ps => ps.1.prod * ps.2.1.prod * ps.2.2.prod
    let w : (List ℕ × (List ℕ × List ℕ)) → ℂ :=
      fun ps => (c / (actualPrimeLabelBlocksFactorial residualBlocks : ℂ)) *
        (∑ k ∈ K, amp k *
          (positionalGroupMode (eta k) U ids.1 ps.1 *
            (positionalGroupMode (eta k) U ids.2.1 ps.2.1 *
              positionalGroupMode (eta k) U ids.2.2 ps.2.2)))
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ ps ∈ source.filter (fun ps => r * residualProduct ps = T),
        w ps * markedResidualKernel r T q (residualProduct ps)) =
      (((ArithmeticFunction.moebius T : ℝ) : ℂ) *
        (∑ q ∈ Q, (rho q : ℂ) * exactCoprimeFactor q)) *
        (∑ ps ∈ source.filter (fun ps => r * residualProduct ps = T), w ps) := by
  dsimp only
  exact marked_exact_product_after_modulus
    _ _ _ Q rho r T hcop

end
end ImbalancedChen.P3ActualMarkedResidualExactProduct
