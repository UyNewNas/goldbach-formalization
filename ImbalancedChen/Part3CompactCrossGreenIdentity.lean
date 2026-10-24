import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Source-only, uncompiled. Off-diagonal Green identity on the real line.
All integrability and vanishing boundary conditions follow from actual compact
support. This does not assert a self-adjoint extension or an automorphic spectrum. -/
namespace ImbalancedChen.Part3.CompactCrossGreenIdentity20261024zz

noncomputable section
open MeasureTheory

theorem integral_star_mul_secondDeriv (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, star (f x) * deriv (deriv g) x) =
      -(∫ x : ℝ, star (deriv f x) * deriv g x) := by
  have hfs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  have hgs : ContDiff ℝ ((1 : ℕ∞ω) + 1) g := by simpa using hg
  have hfd : Differentiable ℝ f := (contDiff_succ_iff_deriv.mp hfs).1
  have hdf : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp hfs).2.2
  have hdg : ContDiff ℝ 1 (deriv g) :=
    (contDiff_succ_iff_deriv.mp hgs).2.2
  have hgd : Differentiable ℝ (deriv g) := hdg.differentiable_one
  have hi₁ : Integrable (fun x : ℝ => star (f x) * deriv (deriv g) x) :=
    (hf.continuous.star.mul hdg.continuous_deriv_one).integrable_of_hasCompactSupport
      (hgc.deriv.deriv.mul_left)
  have hi₂ : Integrable (fun x : ℝ => star (deriv f x) * deriv g x) :=
    (hdf.continuous.star.mul hdg.continuous).integrable_of_hasCompactSupport
      (hgc.deriv.mul_left)
  have hi₀ : Integrable (fun x : ℝ => star (f x) * deriv g x) :=
    (hf.continuous.star.mul hdg.continuous).integrable_of_hasCompactSupport
      (hgc.deriv.mul_left)
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => star (f x)) (v := deriv g)
    (u' := fun x : ℝ => star (deriv f x))
    (v' := deriv (deriv g))
    (fun x _ => (hfd x).hasDerivAt.star)
    (fun x _ => (hgd x).hasDerivAt) hi₁ hi₂ hi₀

theorem negative_laplacian_pairing_eq_gradient_pairing (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, star (f x) * (-deriv (deriv g) x)) =
      ∫ x : ℝ, star (deriv f x) * deriv g x := by
  simp_rw [mul_neg]
  rw [integral_neg, integral_star_mul_secondDeriv f g hf hg hfc hgc, neg_neg]

/-- Off-diagonal integration by parts with the derivative on the first factor.
This gives the second half of the Green symmetry without invoking an operator
extension or an assumed integration-by-parts contract. -/
theorem integral_secondDeriv_star_mul (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, star (deriv (deriv f) x) * g x) =
      -(∫ x : ℝ, star (deriv f x) * deriv g x) := by
  have hfs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  have hgs : ContDiff ℝ ((1 : ℕ∞ω) + 1) g := by simpa using hg
  have hdf : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp hfs).2.2
  have hdg : ContDiff ℝ 1 (deriv g) :=
    (contDiff_succ_iff_deriv.mp hgs).2.2
  have hfd : Differentiable ℝ (deriv f) := hdf.differentiable_one
  have hgd : Differentiable ℝ g := (contDiff_succ_iff_deriv.mp hgs).1
  have hi₁ : Integrable (fun x : ℝ => g x * star (deriv (deriv f) x)) :=
    (hg.continuous.mul hdf.continuous_deriv_one.star).integrable_of_hasCompactSupport
      (hgc.mul_right)
  have hi₂ : Integrable (fun x : ℝ => deriv g x * star (deriv f x)) :=
    (hdg.continuous.mul hdf.continuous.star).integrable_of_hasCompactSupport
      (hgc.deriv.mul_right)
  have hi₀ : Integrable (fun x : ℝ => g x * star (deriv f x)) :=
    (hg.continuous.mul hdf.continuous.star).integrable_of_hasCompactSupport
      (hgc.mul_right)
  have h := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := fun x : ℝ => star (deriv f x))
    (u' := deriv g) (v' := fun x : ℝ => star (deriv (deriv f) x))
    (fun x _ => (hgd x).hasDerivAt)
    (fun x _ => (hfd x).hasDerivAt.star) hi₁ hi₂ hi₀
  simpa only [mul_comm] using h

theorem compact_green_symmetry (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, star (f x) * deriv (deriv g) x) =
      ∫ x : ℝ, star (deriv (deriv f) x) * g x := by
  rw [integral_star_mul_secondDeriv f g hf hg hfc hgc,
    integral_secondDeriv_star_mul f g hf hg hfc hgc]

end
end ImbalancedChen.Part3.CompactCrossGreenIdentity20261024zz

