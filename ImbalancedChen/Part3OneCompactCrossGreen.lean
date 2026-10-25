import ImbalancedChen.Part3CompactCrossGreenIdentity

/-!
# Green integration by parts with exactly one compact test factor

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The first function is compactly supported; the second C2 function may be
noncompact. All product integrability is PROVED from the compact first
factor and its actual derivatives, and pinned real-line integration by
parts gives the cross Green identity. This removes the false need for a
compact Poincare test function when a compact seed is the other factor.
It does not identify a whole-plane graph with an automorphic operator.
-/

namespace ImbalancedChen.Part3.OneCompactCrossGreen20261025a

noncomputable section
open MeasureTheory

private theorem deriv_contDiff_one (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (deriv f) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  exact (contDiff_succ_iff_deriv.mp hs).2.2

private theorem compact_star (f : ℝ → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => star (f x)) :=
  hf.comp_left (g := star) (by simp)

/-- There is no compact-support hypothesis on g. Boundary and integrable
product obligations are supplied by f and its compact derivatives. -/
theorem integral_star_mul_secondDeriv_one_compact (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) :
    (∫ x : ℝ, star (f x) * deriv (deriv g) x) =
      -(∫ x : ℝ, star (deriv f x) * deriv g x) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf := deriv_contDiff_one f hf
  have hdg := deriv_contDiff_one g hg
  have hgd : Differentiable ℝ (deriv g) := hdg.differentiable_one
  have hi₁ : Integrable (fun x : ℝ => star (f x) * deriv (deriv g) x) :=
    (hf.continuous.star.mul hdg.continuous_deriv_one).integrable_of_hasCompactSupport
      (compact_star f hfc).mul_right
  have hi₂ : Integrable (fun x : ℝ => star (deriv f x) * deriv g x) :=
    (hdf.continuous.star.mul hdg.continuous).integrable_of_hasCompactSupport
      (compact_star (deriv f) hfc.deriv).mul_right
  have hi₀ : Integrable (fun x : ℝ => star (f x) * deriv g x) :=
    (hf.continuous.star.mul hdg.continuous).integrable_of_hasCompactSupport
      (compact_star f hfc).mul_right
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => star (f x)) (v := deriv g)
    (u' := fun x : ℝ => star (deriv f x)) (v' := deriv (deriv g))
    (fun x _ => (hfd x).hasDerivAt.star)
    (fun x _ => (hgd x).hasDerivAt) hi₁ hi₂ hi₀

/-- Derivatives on the compact first argument give the same first-order
form against the unrestricted C2 second argument. -/
theorem integral_secondDeriv_star_mul_one_compact (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) :
    (∫ x : ℝ, star (deriv (deriv f) x) * g x) =
      -(∫ x : ℝ, star (deriv f x) * deriv g x) := by
  have hdf := deriv_contDiff_one f hf
  have hdg := deriv_contDiff_one g hg
  have hfd : Differentiable ℝ (deriv f) := hdf.differentiable_one
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hi₁ : Integrable (fun x : ℝ => g x * star (deriv (deriv f) x)) :=
    (hg.continuous.mul hdf.continuous_deriv_one.star).integrable_of_hasCompactSupport
      (compact_star (deriv (deriv f)) hfc.deriv.deriv).mul_left
  have hi₂ : Integrable (fun x : ℝ => deriv g x * star (deriv f x)) :=
    (hdg.continuous.mul hdf.continuous.star).integrable_of_hasCompactSupport
      (compact_star (deriv f) hfc.deriv).mul_left
  have hi₀ : Integrable (fun x : ℝ => g x * star (deriv f x)) :=
    (hg.continuous.mul hdf.continuous.star).integrable_of_hasCompactSupport
      (compact_star (deriv f) hfc.deriv).mul_left
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := fun x : ℝ => star (deriv f x))
    (u' := deriv g) (v' := fun x : ℝ => star (deriv (deriv f) x))
    (fun x _ => (hgd x).hasDerivAt)
    (fun x _ => (hfd x).hasDerivAt.star) hi₁ hi₂ hi₀
  simpa only [mul_comm] using h

/-- Genuine one-compact Green symmetry. This is a differential identity
for actual integrable products, with no supplied Green conclusion. -/
theorem one_compact_green_symmetry (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) :
    (∫ x : ℝ, star (f x) * (-deriv (deriv g) x)) =
      ∫ x : ℝ, star (-deriv (deriv f) x) * g x := by
  simp only [mul_neg, star_neg, neg_mul]
  rw [integral_neg, integral_neg,
    integral_star_mul_secondDeriv_one_compact f g hf hg hfc,
    integral_secondDeriv_star_mul_one_compact f g hf hg hfc]

/-- The actual Dirichlet pairing after integrating one real coordinate. -/
theorem one_compact_negative_secondDeriv_eq_gradient (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) :
    (∫ x : ℝ, star (f x) * (-deriv (deriv g) x)) =
      ∫ x : ℝ, star (deriv f x) * deriv g x := by
  simp only [mul_neg]
  rw [integral_neg, integral_star_mul_secondDeriv_one_compact f g hf hg hfc, neg_neg]

end
end ImbalancedChen.Part3.OneCompactCrossGreen20261025a
