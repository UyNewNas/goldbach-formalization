import ImbalancedChen.P3ActualU8StrictSmoothBoundary
import Mathlib.Tactic

/-!
P3.6 — after the complete physical q sum, localize the actual strict U8
smoothing cost by ORIGINAL labelled prime sources. This is not a PP estimate.

The previous boundary theorem had q on the outside. Here finite Fubini
puts the full absolute physical-modulus response back at each original
label, without changing rho, replacing the exact coprime mean, or
collapsing repeated products. Its congruence and coprime contributions
are separated *after* this reindexing.

There is also a precise full-product=N exception check: the true strict
U8 source has product<N. Any proposed smooth W that has nonzero weight
at a target-product label must therefore charge that label in B. No
smallness of this exceptional mass, arithmetic boundary mass, or
smooth-W admissibility is inferred. SOURCE_ONLY pending Lean elaboration.
-/

namespace ImbalancedChen.P3ActualU8StrictBoundarySourcewise

noncomputable section
open scoped BigOperators
open Classical
open ImbalancedChen.P3ActualU8StrictPhysicalPP
open ImbalancedChen.P3ActualU8StrictSmoothBoundary

/-- No actual strict U8 source label has its full product equal to N.
This is the existing genuine strict-source <N gate, not a convention
about a divisor function at zero. -/
theorem strict_weight_zero_at_exact_target (N : ℕ)
    (u : Fin 3 → Fin (N + 1))
    (hproduct : Part3.labelledProduct u = N) :
    strictPhysicalWeight N u = 0 := by
  by_contra hnonzero
  have hlt : Part3.labelledProduct u < N :=
    (strictPhysicalWeight_support_data hnonzero).2.2.1
  omega

/-- If a replacement W agrees with the ACTUAL strict source off B, a
nonzero full-product=N label of W must belong to B. This identifies
an exceptional arithmetic obligation; it does not pay its mass. -/
theorem smooth_target_product_forced_into_boundary
    (N : ℕ) (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (B : Finset (Fin 3 → Fin (N + 1)))
    (houtside : ∀ u ∈ Part3.labelledPrimeTuples 3 N,
      u ∉ B → strictPhysicalWeight N u = W u)
    (u : Fin 3 → Fin (N + 1))
    (hu : u ∈ Part3.labelledPrimeTuples 3 N)
    (hproduct : Part3.labelledProduct u = N)
    (hW : W u ≠ 0) : u ∈ B := by
  by_contra hnot
  have heq := houtside u hu hnot
  have hzero := strict_weight_zero_at_exact_target N u hproduct
  exact hW (heq.symm.trans hzero)

/-- Finite Fubini reorders the *actual absolute physical modulus*
budget, without replacing congruence by a pointwise divisor heuristic.
Each occurrence of a labelled prime tuple is retained. -/
theorem boundary_budget_sum_by_labels (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (B : Finset (Fin 3 → Fin (N + 1))) :
    (∑ q ∈ Q, |rho q| *
      ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
        |strictPhysicalWeight N u - W u| * physicalKernelBudget N q u) =
    ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
      |strictPhysicalWeight N u - W u| *
        (∑ q ∈ Q, |rho q| * physicalKernelBudget N q u) := by
  calc
    _ = ∑ q ∈ Q,
      ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
        |rho q| * (|strictPhysicalWeight N u - W u| *
          physicalKernelBudget N q u) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
    _ = ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
      ∑ q ∈ Q,
        |rho q| * (|strictPhysicalWeight N u - W u| *
          physicalKernelBudget N q u) := by
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring

/-- The complete per-label physical budget separates into the
literal congruence contribution and the EXACT primitive coprime mean.
The q=0 case remains totalized as in the original Part3 definition. -/
theorem physical_kernel_budget_split (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (u : Fin 3 → Fin (N + 1)) :
    (∑ q ∈ Q, |rho q| * physicalKernelBudget N q u) =
      (∑ q ∈ Q, |rho q| *
        (if Nat.ModEq q (Part3.labelledProduct u) N
          then (1 : ℝ) else 0)) +
      (∑ q ∈ Q, |rho q| *
        ((if Nat.Coprime (Part3.labelledProduct u) q
          then (1 : ℝ) else 0) / (Nat.totient q : ℝ))) := by
  simp only [physicalKernelBudget, mul_add, Finset.sum_add_distrib]

/-- Source-wise boundary cost with the ACTUAL congruence indicator
and exact coprime mean, both under one and the same signed rho.
Neither term is claimed to have an arbitrary-log bound. -/
theorem strict_smoothing_boundary_sourcewise_split
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (B : Finset (Fin 3 → Fin (N + 1)))
    (houtside : ∀ u ∈ Part3.labelledPrimeTuples 3 N,
      u ∉ B → strictPhysicalWeight N u = W u) :
    |Part3.primeProductSignedError 3 N N Q rho (strictPhysicalWeight N) -
      Part3.primeProductSignedError 3 N N Q rho W| ≤
    ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
      |strictPhysicalWeight N u - W u| *
        ((∑ q ∈ Q, |rho q| *
          (if Nat.ModEq q (Part3.labelledProduct u) N
            then (1 : ℝ) else 0)) +
         (∑ q ∈ Q, |rho q| *
          ((if Nat.Coprime (Part3.labelledProduct u) q
            then (1 : ℝ) else 0) / (Nat.totient q : ℝ)))) := by
  calc
    _ ≤ ∑ q ∈ Q, |rho q| *
      ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
        |strictPhysicalWeight N u - W u| *
          physicalKernelBudget N q u :=
      strict_minus_smooth_boundary_bound N Q rho W B houtside
    _ = ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
      |strictPhysicalWeight N u - W u| *
        (∑ q ∈ Q, |rho q| * physicalKernelBudget N q u) :=
      boundary_budget_sum_by_labels N Q rho W B
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [physical_kernel_budget_split]

end
end ImbalancedChen.P3ActualU8StrictBoundarySourcewise
