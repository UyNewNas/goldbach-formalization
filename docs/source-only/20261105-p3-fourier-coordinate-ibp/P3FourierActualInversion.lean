import ImbalancedChen.P3FourierActualBoxTail
import ImbalancedChen.P3FourierCutoffIdentity
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
P3.6, pinned manuscript 9731290 §4 (F). SOURCE_ONLY, UNCOMPILED,
KERNEL_UNVERIFIED.

Inverts the ACTUAL zero-order member of the original ordered doubled
mixed family, with Mathlib frequency eta and physical box |2*pi*eta|≤H.
The H-box error is paid by the preceding actual multidimensional Fourier
norm tail; it is NOT a newly hypothesized Fourier truncation estimate.

The final lemma passes the real geometric W evaluated on the original
Point d chart through the SAME rho, labelled source, complete product,
congruence test and exact coprime mean of the existing signedSource.
It stops at fullModulusMass: no claim that the latter is arithmetically
small, including at exact full product T. The original W_T family
regularity and all-source admission are still open manuscript duties.
-/

namespace ImbalancedChen.P3FourierActualInversion
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open P3AffineTransitionJets P3FourierDPointwise
open P3FourierPointCoordinateBridge P3FourierRealComplex
open P3FourierProductFubini P3FourierAutomaticMeasurability
open P3FourierActualBoxTail P3FourierRestrictedBox
open P3FullSignedModulusTail P3FourierCutoffIdentity

/-- All original doubled-mixed derivatives are treated with their genuine
real-linear Frechet regularity, including the empty derivative. -/
theorem actual_zero_integrable {d : ℕ} (w : Point d → ℝ)
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w))) :
    Integrable (actualMixedFamily w ∅) := by
  rw [actual_mixed_empty_eq_chart]
  simpa using hintegrable ∅ 0 (by simp)

/-- The original smoothness family itself implies continuity of the
undifferentiated Fourier input; no target-inversion hypothesis is added. -/
theorem actual_zero_continuous {d : ℕ} (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w)) :
    Continuous (actualMixedFamily w ∅) := by
  have h0 : ContDiff ℝ (0 : ℕ∞) (chartLift w) := by
    simpa [doubled] using hsmooth ∅
  rw [actual_mixed_empty_eq_chart]
  exact (complexChartLift_contDiff w h0).continuous

/-- Fourier integrability from ACTUAL L1 Fourier-norm control, using the
pinned integrable_norm_iff and Fourier continuity. No independent hF. -/
theorem actual_fourier_integrable {d : ℕ} (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w))) :
    Integrable (𝓕 (actualMixedFamily w ∅)) := by
  have hf : Integrable (actualMixedFamily w ∅) :=
    actual_zero_integrable w hintegrable
  have hmeas : AEStronglyMeasurable (𝓕 (actualMixedFamily w ∅)) :=
    (fourier_continuous_of_integrable (actualMixedFamily w ∅) hf).aestronglyMeasurable
  exact (integrable_norm_iff hmeas).mp
    (actual_fourier_norm_integrable w hsmooth hintegrable)

/-- This is the ACTUAL truncated inverse, with the original physical box,
not a new approximation operator with an assumed error. -/
def actualTruncatedInverse {d : ℕ} (w : Point d → ℝ)
    (H : ℝ) (x : FourierSpace d) : ℂ :=
  truncatedInverse (actualMixedFamily w ∅) (fourierBox d H) x

/-- Pointwise Fourier inversion with the real physical 2*pi cutoff.
The only analytic premises are original finite-order ContDiff and
actual iterated Frechet integrability. -/
theorem actual_truncated_inverse_error {d : ℕ}
    (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (H : ℝ) (hH : 0 < H) (x : FourierSpace d) :
    ‖actualMixedFamily w ∅ x - actualTruncatedInverse w H x‖ ≤
      (d : ℝ) * derivativeD d (actualMixedFamily w) / H := by
  have hf := actual_zero_integrable w hintegrable
  have hF := actual_fourier_integrable w hsmooth hintegrable
  have hc := (actual_zero_continuous w hsmooth).continuousAt
  calc
    ‖actualMixedFamily w ∅ x - actualTruncatedInverse w H x‖ ≤
        ∫ eta in (fourierBox d H)ᶜ,
          ‖𝓕 (actualMixedFamily w ∅) eta‖ :=
      fourier_cutoff_error (actualMixedFamily w ∅)
        hf hF x hc (fourierBox d H) (fourierBox_measurable d H)
    _ ≤ (d : ℝ) * derivativeD d (actualMixedFamily w) / H :=
      actual_fourier_box_tail_bound w hsmooth hintegrable H hH

/-- Recover the literal original real physical chart weight, including
the empty original HB differentiation list (NOT an empty Gamma word). -/
theorem actual_zero_real {d : ℕ} (w : Point d → ℝ)
    (x : FourierSpace d) :
    (actualMixedFamily w ∅ x).re = w (chartEquiv d x) := by
  rw [actual_mixed_empty_eq_chart]
  simp [complexChartLift, chartLift, Complex.ofRealCLM_apply]

/-- Pointwise real error in the ORIGINAL geometric weight. -/
theorem actual_real_truncated_inverse_error {d : ℕ}
    (w : Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (H : ℝ) (hH : 0 < H) (x : FourierSpace d) :
    |w (chartEquiv d x) - (actualTruncatedInverse w H x).re| ≤
      (d : ℝ) * derivativeD d (actualMixedFamily w) / H := by
  have hr : |(actualMixedFamily w ∅ x).re -
      (actualTruncatedInverse w H x).re| ≤
      ‖actualMixedFamily w ∅ x - actualTruncatedInverse w H x‖ := by
    simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm
        (actualMixedFamily w ∅ x - actualTruncatedInverse w H x)
  rw [actual_zero_real w x] at hr
  exact hr.trans
    (actual_truncated_inverse_error w hsmooth hintegrable H hH x)

/-- Exact SAME-rho finite signed-source Fourier cutoff payment.
The mass on the right is the actual full signed physical modulus
majorant, including exact-product contributions; its arithmetic
bound is NOT supplied here. No factor H^d or fibre-relative Theta
assumption appears. -/
theorem actual_same_rho_signed_cutoff {ι : Type*} {d g : ℕ}
    (Q : Finset ℕ) (source : Finset ι)
    (rho : ℕ → ℝ) (coefficient : ι → ℝ)
    (T : ℕ) (originalProducts : ι → Fin g → ℕ)
    (w : Point d → ℝ) (point : ι → FourierSpace d)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (H : ℝ) (hH : 0 < H) :
    |signedSource Q source rho coefficient
        (fun t => w (chartEquiv d (point t))) T originalProducts -
      signedSource Q source rho coefficient
        (fun t => (actualTruncatedInverse w H (point t)).re)
        T originalProducts| ≤
      ((d : ℝ) * derivativeD d (actualMixedFamily w) / H) *
        fullModulusMass Q source rho coefficient T originalProducts := by
  have heps : 0 ≤ (d : ℝ) * derivativeD d (actualMixedFamily w) / H :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (actual_derivativeD_nonneg w)) hH.le
  apply signedSource_approximation Q source rho coefficient
    (fun t => w (chartEquiv d (point t)))
    (fun t => (actualTruncatedInverse w H (point t)).re)
    T originalProducts
    ((d : ℝ) * derivativeD d (actualMixedFamily w) / H) heps
  intro t ht
  exact actual_real_truncated_inverse_error
    w hsmooth hintegrable H hH (point t)

end
end ImbalancedChen.P3FourierActualInversion
