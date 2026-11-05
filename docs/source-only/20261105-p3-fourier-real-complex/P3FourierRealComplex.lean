import ImbalancedChen.P3FourierPointCoordinateBridge
import ImbalancedChen.P3FourierFrechetIBP
import ImbalancedChen.P3FourierDPointwise
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

/-!
P3.6 MANUSCRIPT-INTERNAL / SOURCE_ONLY / UNCOMPILED.
This is real-linear complexification of the ACTUAL original Point d mixed
derivative. It is not holomorphic differentiation, and it does not introduce
a Fourier-IBP hypothesis or arithmetic discrepancy bound.
-/

namespace ImbalancedChen.P3FourierRealComplex
noncomputable section
open MeasureTheory
open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open P3FourierDPointwise P3FourierFrechetIBP
open P3FourierPointCoordinateBridge P3U5ChartMixedL1Budget

def complexChartLift {d : ℕ} (w : P3AffineTransitionJets.Point d → ℝ) :
    FourierSpace d → ℂ :=
  Complex.ofRealCLM ∘ chartLift w

theorem complexChartLift_contDiff {d n : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (hw : ContDiff ℝ (n : ℕ∞) (chartLift w)) :
    ContDiff ℝ (n : ℕ∞) (complexChartLift w) :=
  Complex.ofRealCLM.contDiff.comp hw

/-- Pinned mathlib: ContinuousLinearMap.iteratedFDeriv_comp_left.
All Fréchet derivatives here are with respect to the REAL scalar field. -/
theorem complexChartLift_iterated {d n : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (hw : ContDiff ℝ (n : ℕ∞) (chartLift w))
    (x : FourierSpace d) :
    iteratedFDeriv ℝ n (complexChartLift w) x =
      Complex.ofRealCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (chartLift w) x) := by
  change iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ chartLift w) x = _
  exact Complex.ofRealCLM.iteratedFDeriv_comp_left hw.contDiffAt le_rfl

theorem complexChartLift_iterated_apply {d n : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (hw : ContDiff ℝ (n : ℕ∞) (chartLift w))
    (x : FourierSpace d) (v : Fin n → FourierSpace d) :
    (iteratedFDeriv ℝ n (complexChartLift w) x) v =
      (((iteratedFDeriv ℝ n (chartLift w) x) v : ℝ) : ℂ) := by
  rw [complexChartLift_iterated w hw x]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_apply,
    Complex.ofRealCLM_apply]

/-- Same original doubled S, same Euclidean chart, same value and multiplicity.
This *discharges the real-to-complex derivative identification*, assuming
only actual finite-order smoothness of the given physical weight. -/
theorem actualMixedFamily_eq_complexFrechet {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (S : Finset (Fin d))
    (hw : ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (x : FourierSpace d) :
    actualMixedFamily w S x =
      subsetFrechetDerivative (complexChartLift w) S x := by
  calc
    actualMixedFamily w S x =
        (((iteratedFDeriv ℝ (doubled S).length (chartLift w) x)
          (subsetDirections S) : ℝ) : ℂ) :=
        actualMixedFamily_eq_realFrechet w S hw x
    _ = (iteratedFDeriv ℝ (doubled S).length
          (complexChartLift w) x) (subsetDirections S) :=
        (complexChartLift_iterated_apply w hw x
          (subsetDirections S)).symm
    _ = subsetFrechetDerivative (complexChartLift w) S x := rfl

theorem actualMixedFamily_eq_complexFrechet_fun {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (S : Finset (Fin d))
    (hw : ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w)) :
    actualMixedFamily w S =
      subsetFrechetDerivative (complexChartLift w) S := by
  funext x
  exact actualMixedFamily_eq_complexFrechet w S hw x

/-- Same Haar measure on FourierSpace on both sides. Does NOT assert that
the original Point d product measure is already identified. -/
theorem actualD_eq_complexFrechet_D {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (hw : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w)) :
    derivativeD d (actualMixedFamily w) =
      derivativeD d
        (fun S => subsetFrechetDerivative (complexChartLift w) S) := by
  unfold derivativeD
  apply Finset.sum_congr rfl
  intro S hS
  rw [actualMixedFamily_eq_complexFrechet_fun w S (hw S)]

/-- Actual original mixed derivative Fourier transform via the TRUE pinned
Fourier theorem, with explicit ordinary ContDiff and integrability. -/
theorem actualMixed_fourier_frechet {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (S : Finset (Fin d))
    (hw : ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hi : ∀ k : ℕ, k ≤ (doubled S).length →
      Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (eta : FourierSpace d) :
    𝓕 (actualMixedFamily w S) eta =
      (-(2 * Real.pi * Complex.I)) ^ (doubled S).length •
        (∏ j : Fin (doubled S).length,
          (-innerSL ℝ) eta (subsetDirections S j)) •
            𝓕 (complexChartLift w) eta := by
  rw [actualMixedFamily_eq_complexFrechet_fun w S hw]
  exact subset_frechet_fourier (complexChartLift w) S
    (complexChartLift_contDiff w hw) hi eta

end
end ImbalancedChen.P3FourierRealComplex
