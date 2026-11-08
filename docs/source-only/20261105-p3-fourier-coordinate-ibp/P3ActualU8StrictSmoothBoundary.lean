import ImbalancedChen.P3ActualU8StrictPhysicalPP
import Mathlib.Tactic

/-!
P3.6: exact same-rho arithmetic cost of replacing the literal strict U8
rank-three sharp weight by a proposed geometric weight.

This is a finite, label-preserving comparison in the REAL physical modulus
family. It does NOT assert that the sharp arithmetic indicator belongs to
the manuscript's allowed smooth W class. The boundary/smoothing error is
an INTERNAL arithmetic obligation and is NOT paid by a small geometric
wall volume alone. In particular, a large signed coefficient cannot be
discarded before the complete q sum.

No external PP theorem, cancellation hypothesis, new axiom, or numerical
producer is used. SOURCE_ONLY pending matching Lean elaboration.
-/

namespace ImbalancedChen.P3ActualU8StrictSmoothBoundary

noncomputable section
open scoped BigOperators
open Classical
open ImbalancedChen.P3ActualU8StrictPhysicalPP

/-- The literal current Part3 congruence-minus-EXACT-coprime-mean kernel.
The full rank-three labelled product is used at both occurrences. -/
def physicalKernel (N q : ℕ) (u : Fin 3 → Fin (N + 1)) : ℝ :=
  (if Nat.ModEq q (Part3.labelledProduct u) N then (1 : ℝ) else 0) -
    (if Nat.Coprime (Part3.labelledProduct u) q then (1 : ℝ) else 0) /
      (Nat.totient q : ℝ)

/-- Nonnegative pointwise absolute-kernel budget; this is NOT a relative
error bound in any sparse root fibre. -/
def physicalKernelBudget (N q : ℕ) (u : Fin 3 → Fin (N + 1)) : ℝ :=
  (if Nat.ModEq q (Part3.labelledProduct u) N then (1 : ℝ) else 0) +
    (if Nat.Coprime (Part3.labelledProduct u) q then (1 : ℝ) else 0) /
      (Nat.totient q : ℝ)

theorem physicalKernel_abs_le_budget (N q : ℕ)
    (u : Fin 3 → Fin (N + 1)) :
    |physicalKernel N q u| ≤ physicalKernelBudget N q u := by
  let A : ℝ :=
    if Nat.ModEq q (Part3.labelledProduct u) N then 1 else 0
  let B : ℝ :=
    (if Nat.Coprime (Part3.labelledProduct u) q then (1 : ℝ) else 0) /
      (Nat.totient q : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    split_ifs <;> norm_num
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (by split_ifs <;> norm_num) (Nat.cast_nonneg _)
  change |A - B| ≤ A + B
  calc
    |A - B| ≤ |A| + |B| := abs_sub_le A B
    _ = A + B := by rw [abs_of_nonneg hA, abs_of_nonneg hB]

/-- An exact finite algebraic comparison of the SAME labelled strict
sharp source and an arbitrary proposed geometric W. BOTH terms use
identical Q, rho, target N, primitive mean and complete product. -/
theorem strict_minus_smooth_exact (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin 3 → Fin (N + 1)) → ℝ) :
    Part3.primeProductSignedError 3 N N Q rho (strictPhysicalWeight N) -
      Part3.primeProductSignedError 3 N N Q rho W =
    ∑ q ∈ Q, rho q *
      ∑ u ∈ Part3.labelledPrimeTuples 3 N,
        (strictPhysicalWeight N u - W u) * physicalKernel N q u := by
  unfold Part3.primeProductSignedError
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  unfold physicalKernel
  ring

/-- Exact selective boundary payment AFTER the full physical modulus
weight has been retained. For W agreeing with the strict arithmetic
indicator off B on the ORIGINAL labelled-prime source, only B is charged.
The theorem DOES NOT assert B has small mass, nor that W is admissible.
Those are independent manuscript-internal obligations. -/
theorem strict_minus_smooth_boundary_bound (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (B : Finset (Fin 3 → Fin (N + 1)))
    (houtside : ∀ u ∈ Part3.labelledPrimeTuples 3 N,
      u ∉ B → strictPhysicalWeight N u = W u) :
    |Part3.primeProductSignedError 3 N N Q rho (strictPhysicalWeight N) -
      Part3.primeProductSignedError 3 N N Q rho W| ≤
    ∑ q ∈ Q, |rho q| *
      ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
        |strictPhysicalWeight N u - W u| * physicalKernelBudget N q u := by
  rw [strict_minus_smooth_exact]
  calc
    |∑ q ∈ Q, rho q *
      ∑ u ∈ Part3.labelledPrimeTuples 3 N,
        (strictPhysicalWeight N u - W u) * physicalKernel N q u| ≤
      ∑ q ∈ Q, |rho q *
        ∑ u ∈ Part3.labelledPrimeTuples 3 N,
          (strictPhysicalWeight N u - W u) * physicalKernel N q u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Q, |rho q| *
      ∑ u ∈ Part3.labelledPrimeTuples 3 N,
        |strictPhysicalWeight N u - W u| * physicalKernelBudget N q u := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        |∑ u ∈ Part3.labelledPrimeTuples 3 N,
          (strictPhysicalWeight N u - W u) * physicalKernel N q u| ≤
          ∑ u ∈ Part3.labelledPrimeTuples 3 N,
            |(strictPhysicalWeight N u - W u) * physicalKernel N q u| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ u ∈ Part3.labelledPrimeTuples 3 N,
          |strictPhysicalWeight N u - W u| * |physicalKernel N q u| := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [abs_mul]
        _ ≤ ∑ u ∈ Part3.labelledPrimeTuples 3 N,
          |strictPhysicalWeight N u - W u| * physicalKernelBudget N q u := by
            apply Finset.sum_le_sum
            intro u hu
            exact mul_le_mul_of_nonneg_left
              (physicalKernel_abs_le_budget N q u) (abs_nonneg _)
    _ = ∑ q ∈ Q, |rho q| *
      ∑ u ∈ (Part3.labelledPrimeTuples 3 N).filter (fun u => u ∈ B),
        |strictPhysicalWeight N u - W u| * physicalKernelBudget N q u := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hb : u ∈ B
      · simp [hb]
      · have hz : strictPhysicalWeight N u - W u = 0 :=
          sub_eq_zero.mpr (houtside u hu hb)
        simp [hb, hz]

end
end ImbalancedChen.P3ActualU8StrictSmoothBoundary
