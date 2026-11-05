import ImbalancedChen.P3FourierDPointwise
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

This file proves a TRUE finite-dimensional Fourier integration-by-parts
identity for iterated Frechet derivatives evaluated on arbitrary ordered
directions. It consumes the pinned Mathlib theorem
Real.fourier_iteratedFDeriv, NOT an assumed Fourier derivative identity.

The preceding CoordinateFourierIBP remains OPEN for the older ordered
coordinateDeriv/mixed functions: one must identify those ordinary
coordinate derivatives with the directional Frechet derivatives, prove
the physical signed-square monomial identity, and transfer the Haar
integrals between EuclideanSpace and Point d. All are manuscript-internal.
-/

namespace ImbalancedChen.P3FourierFrechetIBP
noncomputable section

open MeasureTheory Real Complex
open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open P3FourierDPointwise P3U5ChartMixedL1Budget

/-- The ACTUAL Frechet derivative applied to an ordered list of directions.
No formal jet or free derivative estimate appears in the definition. -/
def directionalDerivative {d n : ℕ}
    (f : FourierSpace d → ℂ) (v : Fin n → FourierSpace d) :
    FourierSpace d → ℂ :=
  fun x => iteratedFDeriv ℝ n f x v

/-- Genuine Fourier integration-by-parts for every finite ordered sequence
of directions. The only analytic conditions are ordinary finite smoothness
and integrability of the actual Frechet derivatives up to this order.
Neither the Fourier identity nor a desired PP estimate is a premise. -/
theorem fourier_directional_derivative {d n : ℕ}
    (f : FourierSpace d → ℂ)
    (hf : ContDiff ℝ (n : ℕ∞) f)
    (hi : ∀ k : ℕ, k ≤ n → Integrable (iteratedFDeriv ℝ k f))
    (v : Fin n → FourierSpace d) (eta : FourierSpace d) :
    𝓕 (directionalDerivative f v) eta =
      (-(2 * π * I)) ^ n •
        (∏ j : Fin n, (-innerSL ℝ) eta (v j)) •
          𝓕 f eta := by
  have hn : (n : ℕ∞) ≤ (n : ℕ∞) := le_rfl
  have hfourier :
      𝓕 (iteratedFDeriv ℝ n f) =
        (fun w => VectorFourier.fourierPowSMulRight
          (-innerSL ℝ) (𝓕 f) w n) :=
    Real.fourier_iteratedFDeriv (N := (n : ℕ∞)) hf
      (fun k hk => hi k (by exact_mod_cast hk)) hn
  calc
    𝓕 (directionalDerivative f v) eta =
        (𝓕 (iteratedFDeriv ℝ n f) eta) v := by
      simpa only [directionalDerivative] using
        (Real.fourier_continuousMultilinearMap_apply
          (v := eta) (m := v) (hi n le_rfl)).symm
    _ = (VectorFourier.fourierPowSMulRight
          (-innerSL ℝ) (𝓕 f) eta n) v := by
      rw [congrFun hfourier eta]
    _ = (-(2 * π * I)) ^ n •
          (∏ j : Fin n, (-innerSL ℝ) eta (v j)) •
            𝓕 f eta := by
      simp only [VectorFourier.fourierPowSMulRight_apply]

/-- The genuine standard coordinate vector in the same EuclideanSpace
used by the pinned Mathlib Fourier transform. -/
def basisDirection {d : ℕ} (i : Fin d) : FourierSpace d :=
  EuclideanSpace.single i (1 : ℝ)

/-- The real inner product against a standard basis direction is exactly
the corresponding coordinate frequency. -/
theorem inner_basisDirection {d : ℕ} (eta : FourierSpace d)
    (i : Fin d) :
    (innerSL ℝ) eta (basisDirection i) = eta i := by
  simpa [basisDirection, innerSL_apply_apply] using
    (EuclideanSpace.inner_single_right i (1 : ℝ) eta)

/-- The SAME order as the older literal mixed (doubled S) definition.
Repeated directions are retained, rather than collapsed into a finset. -/
def subsetDirections {d : ℕ} (S : Finset (Fin d)) :
    Fin (doubled S).length → FourierSpace d :=
  fun j => basisDirection ((doubled S)[j])

def subsetFrechetDerivative {d : ℕ} (f : FourierSpace d → ℂ)
    (S : Finset (Fin d)) : FourierSpace d → ℂ :=
  directionalDerivative f (subsetDirections S)

/-- Specialize the genuine Fourier-IBP identity to exactly the 2S ordered
coordinate directions of the manuscript. This has no hcoord premise.
It has NOT yet identified this Frechet derivative with the old mixed
coordinateDeriv, so it is not falsely labelled CoordinateFourierIBP. -/
theorem subset_frechet_fourier {d : ℕ} (f : FourierSpace d → ℂ)
    (S : Finset (Fin d))
    (hf : ContDiff ℝ ((doubled S).length : ℕ∞) f)
    (hi : ∀ k : ℕ, k ≤ (doubled S).length →
      Integrable (iteratedFDeriv ℝ k f))
    (eta : FourierSpace d) :
    𝓕 (subsetFrechetDerivative f S) eta =
      (-(2 * π * I)) ^ (doubled S).length •
        (∏ j : Fin (doubled S).length,
          (-innerSL ℝ) eta (subsetDirections S j)) •
            𝓕 f eta := by
  exact fourier_directional_derivative f hf hi (subsetDirections S) eta

/-- The Frechet specialization differentiates exactly twice per chosen
coordinate; this is still a source-only finite list identity. -/
theorem subset_frechet_order {d : ℕ} (S : Finset (Fin d)) :
    (doubled S).length = 2 * S.card := by
  simp [doubled, twice_length]

end
end ImbalancedChen.P3FourierFrechetIBP
