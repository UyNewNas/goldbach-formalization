import ImbalancedChen.PrimeOwnCubeAffineGates
import ImbalancedChen.ActualPrimePolyhedralTestFunctions

/-!
# Actual own-cube residual integrals on strict affine regions

The sum consists of actual lower residual densities, gated by their own
literal integer cube tests. The normalized residual error is already
proved uniformly; the finite affine prime-sum theorem supplies the genuine
Lebesgue integral. Both gates survive in the difference between two levels.
Identifying the caller's affine region with a particular arithmetic parent
frontier is a separate finite task, not an assumption of density convergence.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory
open scoped Classical BigOperators

/-- The true limiting integral for one strict own-cube level on the
additional fixed affine region. -/
def primeOwnCubeAffineIntegral {k r : ℕ} (a b lambda : ℝ)
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) : ℝ :=
  ∫ t in logPrimeBox (fun _ : Fin (k + 1) => a) (fun _ => b) ∩
      primeAffineGateRegion (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c),
    primeTupleMinusProfile lambda t * ∏ i, 1 / t i

/-- Arbitrary fixed nondegenerate affine constraints may be imposed in
addition to the literal own-cube gate. No integral-limit or uniform-error
premise is supplied by the caller. -/
theorem tendsto_actualPrimeBoxOwnCubeMinusSum_affineGates
    (k : ℕ) {r : ℕ} (a b lambda : ℝ) (ha : 0 < a) (hab : a < b)
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hL : ∀ j, L j ≠ 0) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualPrimeBoxOwnCubeMinusSum k N (cap N) a b lambda
      (primeAffineGateRegion L c))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (primeOwnCubeAffineIntegral a b lambda L c)) := by
  have herror := tendsto_actualPrimeBoxOwnCubeMinus_error k a b lambda ha hab
    (primeAffineGateRegion L c) cap hcap
  have hfixed := (tendsto_actualPrimeBoxTestSum_cube_affineGates ha hab
    (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c)
    (primeOwnCubeGateForms_ne_zero L hL)
    (primeTupleMinusProfile lambda) (continuousOn_primeTupleMinusProfile ha lambda)).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  rw [primeOwnCubeGateRegion_indicator] at hfixed
  have hh := herror.add hfixed
  simpa only [sub_add_cancel, zero_add, primeOwnCubeAffineIntegral] using hh

/-- The difference retains two separately admitted integrals. In
particular, no old gate is used to discard candidates restored by the new
level. A comparison of levels is not needed for this exact limit. -/
theorem tendsto_actualPrimeBoxOwnCubeMinus_difference_affineGates
    (k : ℕ) {r : ℕ} (a b lambdaOld lambdaNew : ℝ) (ha : 0 < a) (hab : a < b)
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hL : ∀ j, L j ≠ 0) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualPrimeBoxOwnCubeMinusSum k N (cap N) a b lambdaNew (primeAffineGateRegion L c) -
        actualPrimeBoxOwnCubeMinusSum k N (cap N) a b lambdaOld (primeAffineGateRegion L c))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (primeOwnCubeAffineIntegral a b lambdaNew L c -
        primeOwnCubeAffineIntegral a b lambdaOld L c)) := by
  exact (tendsto_actualPrimeBoxOwnCubeMinusSum_affineGates k a b lambdaNew ha hab
    L c hL cap hcap).sub (tendsto_actualPrimeBoxOwnCubeMinusSum_affineGates k a b lambdaOld
      ha hab L c hL cap hcap)

end

end ImbalancedChen
