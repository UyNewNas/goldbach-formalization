import ImbalancedChen.Part3ContinuedFourierSpatialSmooth
import ImbalancedChen.Part3FiniteLevelEisensteinOldforms
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
New source only, 2026-10-26. UNCOMPILED / ZERO FORMAL CREDIT.

Positive real dilations commute with the literal hyperbolic Maass operator.
The result is proved through both actual second derivatives. A genuine
two-variable smoothness hypothesis is used for addition of these derivatives.
The resulting finite-list theorem applies to the completed level-one object
at arbitrary positive integral dilations; the central parameter is included.
No held primitive-coordinate derivative module is used.
-/

namespace ImbalancedChen.Part3.FiniteCompletedOldformSpatial20261026a

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo
open ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
open ImbalancedChen.Part3.ContinuedFourierSpatialSmooth
open ImbalancedChen.Part3.CompletedEisensteinSpatialMaass
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a

abbrev SpatialSmooth (F : ℝ × ℝ → ℂ) : Prop := ContDiffOn ℝ ∞ F upperChart

def dilatedChart (a : ℝ) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  F (a * p.1, a * p.2)

theorem second_deriv_dilate (f : ℝ → ℂ) (a x : ℝ) :
    deriv (deriv (fun t : ℝ => f (a * t))) x =
      (a : ℂ) ^ 2 * deriv (deriv f) (a * x) := by
  have hfirst : deriv (fun t : ℝ => f (a * t)) =
      fun t : ℝ => (a : ℂ) * deriv f (a * t) := by
    funext t
    simpa only [Complex.real_smul] using deriv_comp_mul_left a f t
  rw [hfirst, deriv_const_mul_field, deriv_comp_mul_left]
  simp only [Complex.real_smul, pow_two]
  ring

theorem maassLaplacian_dilate (F : ℝ × ℝ → ℂ) (a x y : ℝ) :
    maassLaplacian (dilatedChart a F) x y = maassLaplacian F (a * x) (a * y) := by
  unfold maassLaplacian dilatedChart
  rw [second_deriv_dilate (fun t : ℝ => F (t, a * y)) a x,
    second_deriv_dilate (fun t : ℝ => F (a * x, t)) a y]
  push_cast
  ring

theorem dilatedChart_smooth {F : ℝ × ℝ → ℂ} (hF : SpatialSmooth F)
    {a : ℝ} (ha : 0 < a) : SpatialSmooth (dilatedChart a F) := by
  have hm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (a * p.1, a * p.2)) := by fun_prop
  exact hF.comp hm.contDiffOn (fun p hp => mul_pos ha hp)

private theorem sectionX_smoothAt {F : ℝ × ℝ → ℂ} (hF : SpatialSmooth F)
    (x y : ℝ) (hy : 0 < y) : ContDiffAt ℝ ∞ (fun t : ℝ => F (t, y)) x := by
  have hpt : ContDiffAt ℝ ∞ F (x, y) :=
    hF.contDiffAt (upperChart_isOpen.mem_nhds hy)
  exact hpt.comp x (by fun_prop)

private theorem sectionY_smoothAt {F : ℝ × ℝ → ℂ} (hF : SpatialSmooth F)
    (x y : ℝ) (hy : 0 < y) : ContDiffAt ℝ ∞ (fun t : ℝ => F (x, t)) y := by
  have hpt : ContDiffAt ℝ ∞ F (x, y) :=
    hF.contDiffAt (upperChart_isOpen.mem_nhds hy)
  exact hpt.comp y (by fun_prop)

private theorem second_deriv_add_local {f g : ℝ → ℂ} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (he : (fun t => deriv (fun r => f r + g r) t) =ᶠ[𝓝 x]
      (fun t => deriv f t + deriv g t)) :
    deriv (deriv (fun t => f t + g t)) x = deriv (deriv f) x + deriv (deriv g) x := by
  rw [he.deriv_eq]
  apply deriv_add
  · exact (hf.derivWithin (m := (1 : ℕ∞ω)) (by simp)).differentiableAt one_ne_zero
  · exact (hg.derivWithin (m := (1 : ℕ∞ω)) (by simp)).differentiableAt one_ne_zero

theorem maassLaplacian_add {F G : ℝ × ℝ → ℂ} (hF : SpatialSmooth F)
    (hG : SpatialSmooth G) (x y : ℝ) (hy : 0 < y) :
    maassLaplacian (fun p => F p + G p) x y =
      maassLaplacian F x y + maassLaplacian G x y := by
  have hx : deriv (deriv (fun t : ℝ => F (t, y) + G (t, y))) x =
      deriv (deriv (fun t : ℝ => F (t, y))) x +
        deriv (deriv (fun t : ℝ => G (t, y))) x := by
    apply second_deriv_add_local (sectionX_smoothAt hF x y hy)
      (sectionX_smoothAt hG x y hy)
    exact Filter.Eventually.of_forall (fun t => deriv_add
      ((sectionX_smoothAt hF t y hy).differentiableAt (by simp))
      ((sectionX_smoothAt hG t y hy).differentiableAt (by simp)))
  have hy' : deriv (deriv (fun t : ℝ => F (x, t) + G (x, t))) y =
      deriv (deriv (fun t : ℝ => F (x, t))) y +
        deriv (deriv (fun t : ℝ => G (x, t))) y := by
    apply second_deriv_add_local (sectionY_smoothAt hF x y hy)
      (sectionY_smoothAt hG x y hy)
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact deriv_add ((sectionY_smoothAt hF x t ht).differentiableAt (by simp))
      ((sectionY_smoothAt hG x t ht).differentiableAt (by simp))
  unfold maassLaplacian
  rw [hx, hy']
  ring

theorem maassLaplacian_const_mul (c : ℂ) (F : ℝ × ℝ → ℂ) (x y : ℝ) :
    maassLaplacian (fun p => c * F p) x y = c * maassLaplacian F x y := by
  unfold maassLaplacian
  simp only [deriv_const_mul_field']
  ring

/-- The actual finite completed oldform list on the positive real chart. -/
def completedTermsChart (T : List (ℕ+ × ℂ)) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (T.map (fun t => t.2 * completedEisensteinFourier s
    ((t.1 : ℝ) * p.2) ((t.1 : ℝ) * p.1))).sum

theorem completedTermsChart_nil (s : ℂ) : completedTermsChart [] s = 0 := rfl

theorem completedTermsChart_cons (t : ℕ+ × ℂ) (T : List (ℕ+ × ℂ)) (s : ℂ) :
    completedTermsChart (t :: T) s = fun p =>
      t.2 * completedEisensteinFourier s ((t.1 : ℝ) * p.2) ((t.1 : ℝ) * p.1) +
        completedTermsChart T s p := by
  funext p
  rfl

theorem completedTermsChart_smooth (T : List (ℕ+ × ℂ)) (s : ℂ) :
    SpatialSmooth (completedTermsChart T s) := by
  induction T with
  | nil => exact contDiffOn_const
  | cons t T ih =>
      rw [completedTermsChart_cons]
      exact ((dilatedChart_smooth (completedEisensteinFourier_contDiffOn_infty s)
        (by exact_mod_cast t.1.pos)).const_mul t.2).add ih

theorem completedTermsChart_maass (T : List (ℕ+ × ℂ))
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (x y : ℝ) (hy : 0 < y) :
    maassLaplacian (completedTermsChart T s) x y =
      s * (1 - s) * completedTermsChart T s (x, y) := by
  induction T with
  | nil => simp [completedTermsChart, maassLaplacian]
  | cons t T ih =>
      have ht : 0 < (t.1 : ℝ) := by exact_mod_cast t.1.pos
      rw [completedTermsChart_cons, maassLaplacian_add
        ((dilatedChart_smooth (completedEisensteinFourier_contDiffOn_infty s) ht).const_mul t.2)
        (completedTermsChart_smooth T s) x y hy,
        maassLaplacian_const_mul]
      change t.2 * maassLaplacian
        (dilatedChart (t.1 : ℝ) (fun p => completedEisensteinFourier s p.2 p.1)) x y +
          maassLaplacian (completedTermsChart T s) x y = _
      rw [maassLaplacian_dilate,
        completedEisensteinFourier_maass_eigen s hs0 hs1
          ((t.1 : ℝ) * y) ((t.1 : ℝ) * x) (mul_pos ht hy), ih]
      ring

/-- Native evaluation agrees with the genuine two-variable chart, so the
finite-list theorem is about the actual continued physical object. -/
theorem completedTermsChart_eq_native (T : List (ℕ+ × ℂ)) (s : ℂ)
    (z : UpperHalfPlane) :
    completedTermsChart T s (z.re, z.im) =
      (T.map (fun t => t.2 * completedActualEisenstein s (pnatDilate t.1 z))).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp [completedActualEisenstein, pnatDilate, dilate, completedTermsChart]

end

end ImbalancedChen.Part3.FiniteCompletedOldformSpatial20261026a
