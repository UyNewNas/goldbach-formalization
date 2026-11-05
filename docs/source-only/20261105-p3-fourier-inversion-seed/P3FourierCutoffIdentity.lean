import ImbalancedChen.P3FullSignedModulusTail
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

A genuine Fourier-inversion/cutoff identity over any finite-dimensional
real inner-product space, at the PREVIOUSLY PINNED Mathlib Fourier convention.
No postulated Fourier approximation lemma is used: inversion is supplied by
Mathlib from integrability of f and its actual Fourier transform.

The same-rho terminal transports the REAL PART of this actual cutoff into
the pre-existing complete signed congruence-minus-exact-coprime-mean sum.
A numerical bound on the Fourier tail is a separate geometric task.
No arithmetic distribution or shifted-divisor moment is assumed here.
-/

namespace ImbalancedChen.P3FourierCutoffIdentity
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace Classical BigOperators
open P3FullSignedModulusTail

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The truncation is the actual INVERSE Fourier integral on an arbitrary
measurable frequency set, not a finite-sum approximation or a new norm. -/
def truncatedInverse (f : V → ℂ) (s : Set V) (x : V) : ℂ :=
  ∫ ξ in s, (𝐞 ⟪ξ, x⟫) • (𝓕 f ξ)

/-- Inverting the full transform and subtracting the retained frequency
integral leaves EXACTLY the complementary integral, with no 2π error. -/
theorem full_minus_truncation_eq (f : V → ℂ)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (x : V) (hx : ContinuousAt f x) (s : Set V)
    (hs : MeasurableSet s) :
    f x - truncatedInverse f s x =
      ∫ ξ in sᶜ, (𝐞 ⟪ξ, x⟫) • (𝓕 f ξ) := by
  have hphase : Integrable (fun ξ : V => (𝐞 ⟪ξ, x⟫) • (𝓕 f ξ)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (f := (𝓕 f : V → ℂ)) (μ := volume) (-x)).2 hF
    simpa only [inner_neg_right, neg_neg] using h
  have hsplit := integral_add_compl hs hphase
  have hInv : 𝓕⁻ (𝓕 f) x = f x :=
    hf.fourierInv_fourier_eq hF hx
  change f x - (∫ ξ in s, (𝐞 ⟪ξ, x⟫) • (𝓕 f ξ)) = _
  rw [← hInv, Real.fourierInv_eq]
  rw [← hsplit]
  abel

/-- Exact L1-tail upper bound, valid in EVERY finite real dimension.
There is no premise of the desired Fourier decay, only the standard
integrability hypotheses needed for mathematical inversion. -/
theorem fourier_cutoff_error (f : V → ℂ)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (x : V) (hx : ContinuousAt f x)
    (s : Set V) (hs : MeasurableSet s) :
    ‖f x - truncatedInverse f s x‖ ≤
      ∫ ξ in sᶜ, ‖𝓕 f ξ‖ := by
  rw [full_minus_truncation_eq f hf hF x hx s hs]
  calc
    ‖∫ ξ in sᶜ, (𝐞 ⟪ξ, x⟫) • (𝓕 f ξ)‖
        ≤ ∫ ξ in sᶜ, ‖(𝐞 ⟪ξ, x⟫) • (𝓕 f ξ)‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ ξ in sᶜ, ‖𝓕 f ξ‖ := by simp_rw [Circle.norm_smul]

/-- The original signed modulus sum can consume the *actual* truncated
inverse: no modulus is used to select a geometric weight, and the same
rho multiplies count and mean. The remaining htail premise is geometric
L1 mass OUTSIDE the chosen frequency set, not a PP-discrepancy premise. -/
theorem same_rho_signed_fourier_cutoff {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι)
    (rho : ℕ → ℝ) (coefficient : ι → ℝ)
    (T : ℕ) (originalProducts : ι → Fin g → ℕ)
    (f : V → ℂ) (point : ι → V)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (hcont : ∀ t ∈ source, ContinuousAt f (point t))
    (s : Set V) (hs : MeasurableSet s)
    (eps : ℝ) (heps : 0 ≤ eps)
    (htail : ∀ t ∈ source, (∫ ξ in sᶜ, ‖𝓕 f ξ‖) ≤ eps) :
    |signedSource Q source rho coefficient
       (fun t => (f (point t)).re) T originalProducts -
     signedSource Q source rho coefficient
       (fun t => (truncatedInverse f s (point t)).re) T originalProducts| ≤
      eps * fullModulusMass Q source rho coefficient T originalProducts := by
  apply signedSource_approximation Q source rho coefficient
    (fun t => (f (point t)).re)
    (fun t => (truncatedInverse f s (point t)).re)
    T originalProducts eps heps
  intro t ht
  have hre :
      |(f (point t)).re - (truncatedInverse f s (point t)).re| ≤
        ‖f (point t) - truncatedInverse f s (point t)‖ := by
    simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm (f (point t) - truncatedInverse f s (point t))
  exact hre.trans
    ((fourier_cutoff_error f hf hF (point t) (hcont t ht) s hs).trans
      (htail t ht))

end
end ImbalancedChen.P3FourierCutoffIdentity
