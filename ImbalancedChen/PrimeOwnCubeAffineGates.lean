import ImbalancedChen.AffinePrimeGates
import ImbalancedChen.ActualPrimeBoxOwnCubeResidual

/-!
# Adding the strict own-cube gate to a finite affine region

The last-prime cube is one nonzero linear form in the logarithmic tuple.
Its row is retained independently for each frozen level. No arithmetic
parent region is identified with an affine region by this module.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Set

def primeOwnCubeLinearForm (k : ℕ) : (Fin (k + 1) → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin (k + 1), ContinuousLinearMap.proj i) +
    (2 : ℝ) • ContinuousLinearMap.proj (Fin.last k)

@[simp] theorem primeOwnCubeLinearForm_apply (k : ℕ) (t : Fin (k + 1) → ℝ) :
    primeOwnCubeLinearForm k t = primeTupleOwnCubeForm t := by
  simp [primeOwnCubeLinearForm, primeTupleOwnCubeForm]

theorem primeOwnCubeLinearForm_ne_zero (k : ℕ) : primeOwnCubeLinearForm k ≠ 0 := by
  intro h
  have hh := congrArg (fun F : (Fin (k + 1) → ℝ) →L[ℝ] ℝ => F (fun _ => 1)) h
  simp only [primeOwnCubeLinearForm_apply, primeTupleOwnCubeForm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, zero_apply] at hh
  have hp : (0 : ℝ) < (k + 1 : ℕ) + 2 := by positivity
  exact (ne_of_gt hp) hh

def primeOwnCubeGateForms {k r : ℕ}
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) :
    Fin (r + 1) → (Fin (k + 1) → ℝ) →L[ℝ] ℝ :=
  Fin.cons (primeOwnCubeLinearForm k) L

def primeOwnCubeGateBounds {r : ℕ} (lambda : ℝ) (c : Fin r → ℝ) : Fin (r + 1) → ℝ :=
  Fin.cons lambda c

theorem primeOwnCubeGateForms_ne_zero {k r : ℕ}
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (hL : ∀ j, L j ≠ 0) :
    ∀ j, primeOwnCubeGateForms L j ≠ 0 := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact primeOwnCubeLinearForm_ne_zero k
  · exact hL i

theorem mem_primeOwnCubeGateRegion {k r : ℕ}
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (lambda : ℝ)
    (t : Fin (k + 1) → ℝ) :
    t ∈ primeAffineGateRegion (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c) ↔
      primeTupleOwnCubeForm t < lambda ∧ t ∈ primeAffineGateRegion L c := by
  simp [primeAffineGateRegion, primeOwnCubeGateForms, primeOwnCubeGateBounds, Fin.forall_fin_succ]

/-- The combined indicator is exactly the two original strict gates,
including their boundary values. -/
theorem primeOwnCubeGateRegion_indicator {k r : ℕ}
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (lambda : ℝ)
    (f : (Fin (k + 1) → ℝ) → ℝ) :
    (primeAffineGateRegion (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c)).indicator f =
      (fun t => if t ∈ primeAffineGateRegion L c then
        (if primeTupleOwnCubeForm t < lambda then f t else 0) else 0) := by
  funext t
  by_cases hR : t ∈ primeAffineGateRegion L c <;>
    by_cases hg : primeTupleOwnCubeForm t < lambda <;>
    simp [Set.indicator, mem_primeOwnCubeGateRegion, hR, hg]

end

end ImbalancedChen
