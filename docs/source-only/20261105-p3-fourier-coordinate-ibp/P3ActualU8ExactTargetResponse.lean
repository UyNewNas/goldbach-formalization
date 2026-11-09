import ImbalancedChen.P3ActualU8StrictBoundarySourcewise
import Mathlib.Tactic

/-!
P3.6 — exact full-product=N response of the ORIGINAL labelled U8
rank-three smooth-boundary comparison.

At an actual prime label with complete product=N every physical
congruence test is true (including the totalized modulus-zero test).
The strict U8 weight is zero there. Consequently the full signed
physical-modulus response factors as a single finite coefficient
independent of the label times the smooth W mass on target-product
labels. If W equals strict off B, only labels in B contribute.

This is an exact signed identity, not an estimate of the arithmetic
boundary mass, a bound on the exceptional labels, or a PP saving.
The q sum retains the original physical Q and rho, and the mean
retains the literal coprime indicator and totient. No labels are
identified by their product. Compilation remains to be checked.
-/

namespace ImbalancedChen.P3ActualU8ExactTargetResponse

noncomputable section
open scoped BigOperators
open Classical
open ImbalancedChen.P3ActualU8StrictPhysicalPP
open ImbalancedChen.P3ActualU8StrictSmoothBoundary
open ImbalancedChen.P3ActualU8StrictBoundarySourcewise

/-- The actual labelled Part3 prime tuples whose COMPLETE product is N.
Different labelled tuples with the same product remain different elements. -/
def targetProductLabels (N : ℕ) : Finset (Fin 3 → Fin (N + 1)) :=
  (Part3.labelledPrimeTuples 3 N).filter
    (fun u => Part3.labelledProduct u = N)

/-- A single literal physical signed coefficient for the target product.
The leading 1 is the exact true congruence indicator at product=N,
not a divisor-bound heuristic. The coprime mean is unchanged. -/
def targetResponse (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    (1 - (if Nat.Coprime N q then (1 : ℝ) else 0) /
      (Nat.totient q : ℝ))

/-- For a full product equal to N the congruence kernel is identically
one, while the primitive mean still depends on the physical modulus. -/
theorem physicalKernel_at_target (N q : ℕ)
    (u : Fin 3 → Fin (N + 1))
    (hproduct : Part3.labelledProduct u = N) :
    physicalKernel N q u =
      1 - (if Nat.Coprime N q then (1 : ℝ) else 0) /
        (Nat.totient q : ℝ) := by
  have hmod : Nat.ModEq q N N := by rfl
  simp only [physicalKernel, hproduct, if_pos hmod]

/-- The exceptional scalar is exact congruence mass MINUS the exact
coprime mean. It is not replaced by its absolute mass. -/
theorem targetResponse_split (N : ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) :
    targetResponse N Q rho =
      (∑ q ∈ Q, rho q) -
      (∑ q ∈ Q, rho q *
        ((if Nat.Coprime N q then (1 : ℝ) else 0) /
          (Nat.totient q : ℝ))) := by
  simp only [targetResponse, mul_sub, mul_one, Finset.sum_sub_distrib]

/-- Exact factorization of the signed difference on full-product=N
labels. The strict term vanishes by its genuine original product<N
gate; NO physical modulus, signed rho, label or exact mean is changed. -/
theorem target_product_signed_factor (N : ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (W : (Fin 3 → Fin (N + 1)) → ℝ) :
    (∑ q ∈ Q, rho q *
      ∑ u ∈ targetProductLabels N,
        (strictPhysicalWeight N u - W u) * physicalKernel N q u) =
      -(∑ u ∈ targetProductLabels N, W u) *
        targetResponse N Q rho := by
  have hterm (q : ℕ) :
      (∑ u ∈ targetProductLabels N,
        (strictPhysicalWeight N u - W u) * physicalKernel N q u) =
        -(∑ u ∈ targetProductLabels N, W u) *
          (1 - (if Nat.Coprime N q then (1 : ℝ) else 0) /
            (Nat.totient q : ℝ)) := by
    calc
      _ = ∑ u ∈ targetProductLabels N,
        (-W u) *
          (1 - (if Nat.Coprime N q then (1 : ℝ) else 0) /
            (Nat.totient q : ℝ)) := by
          apply Finset.sum_congr rfl
          intro u hu
          have hp : Part3.labelledProduct u = N :=
            (Finset.mem_filter.mp hu).2
          rw [strict_weight_zero_at_exact_target N u hp,
              physicalKernel_at_target N q u hp]
          ring
      _ = (∑ u ∈ targetProductLabels N, -W u) *
          (1 - (if Nat.Coprime N q then (1 : ℝ) else 0) /
            (Nat.totient q : ℝ)) := by
          rw [Finset.sum_mul]
      _ = _ := by
          rw [Finset.sum_neg_distrib]
  calc
    _ = ∑ q ∈ Q, rho q *
      (-(∑ u ∈ targetProductLabels N, W u) *
        (1 - (if Nat.Coprime N q then (1 : ℝ) else 0) /
          (Nat.totient q : ℝ))) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [hterm q]
    _ = _ := by
          unfold targetResponse
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring

/-- Under genuine off-B agreement, the exact target-product W mass
is supported on original labelled tuples in B. No smallness is assumed. -/
theorem target_weight_sum_boundary (N : ℕ)
    (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (B : Finset (Fin 3 → Fin (N + 1)))
    (houtside : ∀ u ∈ Part3.labelledPrimeTuples 3 N,
      u ∉ B → strictPhysicalWeight N u = W u) :
    (∑ u ∈ targetProductLabels N, W u) =
      ∑ u ∈ (targetProductLabels N).filter (fun u => u ∈ B),
        W u := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hb : u ∈ B
  · simp [hb]
  · have hl : u ∈ Part3.labelledPrimeTuples 3 N :=
      (Finset.mem_filter.mp hu).1
    have hp : Part3.labelledProduct u = N :=
      (Finset.mem_filter.mp hu).2
    have hzero : W u = 0 :=
      (houtside u hl hb).symm.trans
        (strict_weight_zero_at_exact_target N u hp)
    simp [hb, hzero]

/-- Complete physical-modulus signed diagonal response, now factored
through only the boundary's actual TARGET-PRODUCT labelled W mass.
This is a localization identity, not payment of that mass. -/
theorem target_product_signed_boundary_factor
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (B : Finset (Fin 3 → Fin (N + 1)))
    (houtside : ∀ u ∈ Part3.labelledPrimeTuples 3 N,
      u ∉ B → strictPhysicalWeight N u = W u) :
    (∑ q ∈ Q, rho q *
      ∑ u ∈ targetProductLabels N,
        (strictPhysicalWeight N u - W u) * physicalKernel N q u) =
      -(∑ u ∈ (targetProductLabels N).filter (fun u => u ∈ B),
        W u) * targetResponse N Q rho := by
  calc
    _ = -(∑ u ∈ targetProductLabels N, W u) *
          targetResponse N Q rho :=
      target_product_signed_factor N Q rho W
    _ = _ := by
      rw [target_weight_sum_boundary N W B houtside]

end
end ImbalancedChen.P3ActualU8ExactTargetResponse
