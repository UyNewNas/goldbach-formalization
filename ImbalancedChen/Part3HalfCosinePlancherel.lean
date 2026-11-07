import ImbalancedChen.Part3FourierL1L2Plancherel
import ImbalancedChen.Part3KFullLineFourierBridge
import ImbalancedChen.Part3ActualKProfileLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
The two sibling source-only modules are required under their declared
staging names before compilation. All equality and Lp premises below are
discharged for the actual imaginaryOrderK. This is Euclidean cosine
Plancherel, not an automorphic or Kontorovich-Lebedev Plancherel theorem.
-/

noncomputable section

namespace ImbalancedChen.Part3.HalfCosinePlancherelSourceOnly

open Set MeasureTheory SchwartzMap FourierTransform
open scoped FourierTransform SchwartzMap
open FourierL1L2PlancherelSourceOnly KFullLineFourierBridgeSourceOnly
open P3ActualKProfileLpSourceOnly ImaginaryOrderKBesselSourceOnly

/-- The half-line cosine transform with the actual K-order convention. -/
def halfCosineTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (Real.cos (2 * t * u) : ℂ) * f u

theorem halfCosineTransform_eq_half_fourier {f : ℝ → ℂ}
    (h₁ : Integrable f) (heven : ∀ u, f (-u) = f u) (t : ℝ) :
    halfCosineTransform f t = (1 / 2 : ℂ) * 𝓕 f (t / Real.pi) := by
  exact cosine_integral_eq_half_fourier f h₁ heven t

/-- Full-axis spectral mass of the half-line transform. The coefficient
π/2 comes from the 2tu convention and the even spatial extension. -/
theorem halfCosineTransform_plancherel {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) (heven : ∀ u, f (-u) = f u) :
    (∫ t : ℝ, ‖halfCosineTransform f t‖ ^ 2) =
      (Real.pi / 2) * ∫ u in Ioi (0 : ℝ), ‖f u‖ ^ 2 := by
  have habs (u : ℝ) : f |u| = f u := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu), heven]
  have hmass : (∫ u : ℝ, ‖f u‖ ^ 2) =
      2 * ∫ u in Ioi (0 : ℝ), ‖f u‖ ^ 2 := by
    calc
      _ = ∫ u : ℝ, ‖f |u|‖ ^ 2 := by simp_rw [habs]
      _ = _ := integral_comp_abs (f := fun u : ℝ => ‖f u‖ ^ 2)
  calc
    _ = ∫ t : ℝ, ‖(1 / 2 : ℂ) * 𝓕 f (t / Real.pi)‖ ^ 2 := by
      simp_rw [halfCosineTransform_eq_half_fourier h₁ heven]
    _ = (Real.pi / 4) * ∫ u : ℝ, ‖f u‖ ^ 2 :=
      integral_norm_sq_half_rescaled_fourier h₁ h₂
    _ = _ := by rw [hmass]; ring

theorem halfCosineTransform_sq_integrable {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) (heven : ∀ u, f (-u) = f u) :
    Integrable (fun t : ℝ => ‖halfCosineTransform f t‖ ^ 2) := by
  simpa only [halfCosineTransform_eq_half_fourier h₁ heven] using
    integrable_norm_sq_half_rescaled_fourier h₁ h₂

/-- The two independently written sibling profiles are definitionally
the same actual exponential-cosh function. -/
theorem kEvenProfile_eq_evenLaplaceProfile (q : ℝ) :
    kEvenProfile q = evenLaplaceProfile q := by
  rfl

theorem kEvenProfile_memLp_two {q : ℝ} (hq : 0 < q) :
    MemLp (kEvenProfile q) 2 := by
  simpa only [kEvenProfile_eq_evenLaplaceProfile] using
    evenLaplaceProfile_memLp_two hq

/-- Actual K_{2it}(q) is square-integrable in the full real order axis. -/
theorem imaginaryOrderK_sq_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (fun t : ℝ => |imaginaryOrderK t q| ^ 2) := by
  have h := integrable_norm_sq_half_rescaled_fourier
    (kEvenProfile_integrable hq) (kEvenProfile_memLp_two hq)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  rw [← imaginaryOrderK_eq_half_fourier t q hq]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The requested exact full-axis cosine Plancherel identity for the
already defined integral realization of K_{2it}(q), with q > 0. -/
theorem imaginaryOrderK_plancherel {q : ℝ} (hq : 0 < q) :
    (∫ t : ℝ, |imaginaryOrderK t q| ^ 2) =
      (Real.pi / 2) * imaginaryOrderK 0 (2 * q) := by
  calc
    _ = ∫ t : ℝ, ‖(1 / 2 : ℂ) *
        𝓕 (kEvenProfile q) (t / Real.pi)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [← imaginaryOrderK_eq_half_fourier t q hq]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ = (Real.pi / 4) * ∫ u : ℝ, ‖kEvenProfile q u‖ ^ 2 :=
      integral_norm_sq_half_rescaled_fourier
        (kEvenProfile_integrable hq) (kEvenProfile_memLp_two hq)
    _ = (Real.pi / 4) * (2 * imaginaryOrderK 0 (2 * q)) := by
      rw [kEvenProfile_eq_evenLaplaceProfile,
        evenLaplaceProfile_norm_sq_integral hq]
    _ = _ := by ring

end ImbalancedChen.Part3.HalfCosinePlancherelSourceOnly
