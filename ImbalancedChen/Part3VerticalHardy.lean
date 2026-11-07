import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED, 2026-10-24.

Vertical Hardy estimate for a complex-valued smooth compactly supported
function on the positive half-line.  Its proof expands the nonnegative
square `‖h' - h/(2y)‖²`, with the cross term supplied by an actual
integration by parts.  No quotient-surface or automorphic spectral
statement is made here.
-/

namespace ImbalancedChen.Part3.VerticalHardy20261024zz

noncomputable section

open MeasureTheory Filter

private def weight (n : ℕ) (h : ℝ → ℂ) (y : ℝ) : ℂ :=
  ((y⁻¹ : ℝ) ^ n) • h y

private theorem weight_continuous (n : ℕ) (h : ℝ → ℂ)
    (hh : Continuous h) (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    Continuous (weight n h) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hz : (0 : ℝ) ∉ tsupport h := by
      intro hz
      exact (lt_irrefl (0 : ℝ)) (hpos hz)
    have he : h =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hz
    have hw : weight n h =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) :=
      he.mono (fun z hz => by simp [weight, hz])
    exact continuousAt_const.congr_of_eventuallyEq hw
  · exact ((continuousAt_id.inv₀ hy).pow n).smul hh.continuousAt

private theorem weight_compact (n : ℕ) (h : ℝ → ℂ)
    (hh : HasCompactSupport h) : HasCompactSupport (weight n h) := by
  exact hh.smul_left

private theorem weight_integrable (n : ℕ) (h : ℝ → ℂ)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    Integrable (weight n h) :=
  (weight_continuous n h hh hpos).integrable_of_hasCompactSupport
    (weight_compact n h hhc)

private theorem weight_one_hasDerivAt (h : ℝ → ℂ)
    (hh : Differentiable ℝ h) (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ))
    (y : ℝ) :
    HasDerivAt (weight 1 h)
      (weight 1 (deriv h) y - weight 2 h y) y := by
  by_cases hy : y = 0
  · subst y
    have hz : (0 : ℝ) ∉ tsupport h := by
      intro hz
      exact (lt_irrefl (0 : ℝ)) (hpos hz)
    have hw : (0 : ℝ) ∉ tsupport (weight 1 h) := by
      intro hw
      exact hz ((tsupport_smul_subset_right
        (fun z : ℝ => (z⁻¹ : ℝ) ^ 1) h) hw)
    have hd : deriv h 0 = 0 := deriv_of_notMem_tsupport hz
    simpa [weight, hd] using
      (HasDerivAt.of_notMem_tsupport hw)
  · have hi : HasDerivAt (fun z : ℝ => z⁻¹) (-(y ^ 2)⁻¹) y :=
      hasDerivAt_inv hy
    convert hi.smul (hh y).hasDerivAt using 1 <;>
      simp only [weight, pow_one, pow_two, smul_eq_mul] <;>
      field_simp <;> ring

/-- The actual integration-by-parts identity.  The two terms on the
left are conjugates after integration.  The right side is the weighted
mass.  All three integrands are integrable because `h` and `h'` have
compact support strictly inside `y > 0`. -/
theorem vertical_cross_identity (h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    (∫ y : ℝ, star (h y) * weight 1 (deriv h) y) +
      (∫ y : ℝ, star (deriv h y) * weight 1 h y) =
      ∫ y : ℝ, star (h y) * weight 2 h y := by
  have hdh : Continuous (deriv h) := hh.continuous_deriv_one
  have hdpos : tsupport (deriv h) ⊆ Set.Ioi (0 : ℝ) :=
    Set.Subset.trans tsupport_deriv_subset hpos
  have hiA : Integrable (fun y : ℝ =>
      star (h y) * weight 1 (deriv h) y) :=
    (hh.continuous.star.mul (weight_continuous 1 (deriv h) hdh hdpos)).integrable_of_hasCompactSupport
      ((weight_compact 1 (deriv h) hhc.deriv).mul_left)
  have hiM : Integrable (fun y : ℝ =>
      star (h y) * weight 2 h y) :=
    (hh.continuous.star.mul (weight_continuous 2 h hh.continuous hpos)).integrable_of_hasCompactSupport
      ((weight_compact 2 h hhc).mul_left)
  have hi₁ : Integrable (fun y : ℝ =>
      star (h y) * (weight 1 (deriv h) y - weight 2 h y)) := by
    convert hiA.sub hiM using 1
    ext y
    ring
  have hi₂ : Integrable (fun y : ℝ =>
      star (deriv h y) * weight 1 h y) :=
    (hdh.star.mul (weight_continuous 1 h hh.continuous hpos)).integrable_of_hasCompactSupport
      ((weight_compact 1 h hhc).mul_left)
  have hi₀ : Integrable (fun y : ℝ =>
      star (h y) * weight 1 h y) :=
    (hh.continuous.star.mul (weight_continuous 1 h hh.continuous hpos)).integrable_of_hasCompactSupport
      ((weight_compact 1 h hhc).mul_left)
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun y : ℝ => star (h y))
    (v := weight 1 h)
    (u' := fun y : ℝ => star (deriv h y))
    (v' := fun y : ℝ => weight 1 (deriv h) y - weight 2 h y)
    (fun y _ => (hh.differentiable_one y).hasDerivAt.star)
    (fun y _ => weight_one_hasDerivAt h hh.differentiable_one hpos y)
    hi₁ hi₂ hi₀
  rw [show (∫ y : ℝ,
      star (h y) * (weight 1 (deriv h) y - weight 2 h y)) =
      (∫ y : ℝ, star (h y) * weight 1 (deriv h) y) -
      (∫ y : ℝ, star (h y) * weight 2 h y) by
        convert integral_sub hiA hiM using 1
        ext y
        ring] at hibp
  linear_combination hibp

/-- Real form of the cross identity. -/
theorem vertical_cross_real (h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    2 * (∫ y : ℝ, (star (h y) * weight 1 (deriv h) y).re) =
      ∫ y : ℝ, ‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2 := by
  have hdh : Continuous (deriv h) := hh.continuous_deriv_one
  have hdpos : tsupport (deriv h) ⊆ Set.Ioi (0 : ℝ) :=
    Set.Subset.trans tsupport_deriv_subset hpos
  have hiA : Integrable (fun y : ℝ =>
      star (h y) * weight 1 (deriv h) y) :=
    (hh.continuous.star.mul (weight_continuous 1 (deriv h) hdh hdpos)).integrable_of_hasCompactSupport
      ((weight_compact 1 (deriv h) hhc.deriv).mul_left)
  have hiB : Integrable (fun y : ℝ =>
      star (deriv h y) * weight 1 h y) :=
    (hdh.star.mul (weight_continuous 1 h hh.continuous hpos)).integrable_of_hasCompactSupport
      ((weight_compact 1 h hhc).mul_left)
  have hiM : Integrable (fun y : ℝ =>
      star (h y) * weight 2 h y) :=
    (hh.continuous.star.mul (weight_continuous 2 h hh.continuous hpos)).integrable_of_hasCompactSupport
      ((weight_compact 2 h hhc).mul_left)
  have hc := vertical_cross_identity h hh hhc hpos
  have hconj (y : ℝ) :
      (star (deriv h y) * weight 1 h y).re =
      (star (h y) * weight 1 (deriv h) y).re := by
    simp [weight, Complex.mul_re, Complex.star_def, Complex.smul_re,
      Complex.smul_im]
    ring
  have hmass (y : ℝ) :
      (star (h y) * weight 2 h y).re =
      ‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [weight, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
      Complex.smul_re, Complex.smul_im]
    ring
  have hre := congrArg Complex.re hc
  rw [Complex.add_re, ← integral_re hiA,
    ← integral_re hiB, ← integral_re hiM] at hre
  simp_rw [hconj, hmass] at hre
  linear_combination hre

/-- Exact square identity behind the sharp constant `1/4`. -/
theorem vertical_hardy_square_identity (h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    (∫ y : ℝ, ‖deriv h y - ((2 * y)⁻¹ : ℝ) • h y‖ ^ 2) =
      (∫ y : ℝ, ‖deriv h y‖ ^ 2) -
        (1 / 4 : ℝ) *
          (∫ y : ℝ, ‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2) := by
  have hdpos : tsupport (deriv h) ⊆ Set.Ioi (0 : ℝ) :=
    Set.Subset.trans tsupport_deriv_subset hpos
  have hdcont : Continuous (deriv h) := hh.continuous_deriv_one
  have hiD : Integrable (fun y : ℝ => ‖deriv h y‖ ^ 2) := by
    convert (hdcont.norm.mul hdcont.norm).integrable_of_hasCompactSupport
      (hhc.deriv.norm.mul_right) using 1
    ext y
    simp [pow_two]
  have hiM : Integrable (fun y : ℝ =>
      ‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2) := by
    have hw := weight_continuous 1 h hh.continuous hpos
    convert (hw.norm.mul hw.norm).integrable_of_hasCompactSupport
      ((weight_compact 1 h hhc).norm.mul_right) using 1
    ext y
    simp [weight, norm_smul, Real.norm_eq_abs, sq_abs]
    ring
  have hiC : Integrable (fun y : ℝ =>
      (star (h y) * weight 1 (deriv h) y).re) := by
    exact ((hh.continuous.star.mul
      (weight_continuous 1 (deriv h) hdcont hdpos)).integrable_of_hasCompactSupport
      ((weight_compact 1 (deriv h) hhc.deriv).mul_left)).re
  have hpoint (y : ℝ) :
      ‖deriv h y - ((2 * y)⁻¹ : ℝ) • h y‖ ^ 2 =
        ‖deriv h y‖ ^ 2 -
          (star (h y) * weight 1 (deriv h) y).re +
          (1 / 4 : ℝ) * (‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2) := by
    have hhalf : (2 * y)⁻¹ = (1 / 2 : ℝ) * y⁻¹ := by
      simp [mul_inv_rev, div_eq_mul_inv] <;> ring
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq]
    simp [hhalf, weight, Complex.normSq_apply, Complex.mul_re, Complex.star_def,
      Complex.smul_re, Complex.smul_im, inv_mul_eq_div]
    ring
  simp_rw [hpoint]
  rw [integral_add (hiD.sub hiC) hiM.const_mul,
    integral_sub hiD hiC, integral_const_mul]
  have hc := vertical_cross_real h hh hhc hpos
  linear_combination (-1 / 2 : ℝ) * hc

/-- Sharp vertical Hardy estimate on the positive half-line.  Since
`h` is zero on `(-∞,0]`, whole-line integrals here equal positive
half-line integrals. -/
theorem vertical_hardy (h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    (1 / 4 : ℝ) *
        (∫ y : ℝ, ‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2) ≤
      ∫ y : ℝ, ‖deriv h y‖ ^ 2 := by
  have hsq := vertical_hardy_square_identity h hh hhc hpos
  have hnonneg : 0 ≤
      ∫ y : ℝ, ‖deriv h y - ((2 * y)⁻¹ : ℝ) • h y‖ ^ 2 :=
    integral_nonneg (fun y => sq_nonneg _)
  linarith

/-- The compact tensor form has the `1/4` lower bound against the
separated chart mass.  The canonical tensor form module identifies the
right side with its hyperbolic Laplacian energy. -/
theorem tensor_separated_hardy_floor (g h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    (1 / 4 : ℝ) *
        (∫ x : ℝ, ‖g x‖ ^ 2) *
        (∫ y : ℝ, ‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2) ≤
      (∫ x : ℝ, ‖deriv g x‖ ^ 2) *
        (∫ y : ℝ, ‖h y‖ ^ 2) +
      (∫ x : ℝ, ‖g x‖ ^ 2) *
        (∫ y : ℝ, ‖deriv h y‖ ^ 2) := by
  have hg0 : 0 ≤ (∫ x : ℝ, ‖g x‖ ^ 2) :=
    integral_nonneg (fun x => sq_nonneg _)
  have hx0 : 0 ≤ (∫ x : ℝ, ‖deriv g x‖ ^ 2) :=
    integral_nonneg (fun x => sq_nonneg _)
  have hy0 : 0 ≤ (∫ y : ℝ, ‖h y‖ ^ 2) :=
    integral_nonneg (fun y => sq_nonneg _)
  have hv := mul_le_mul_of_nonneg_left (vertical_hardy h hh hhc hpos) hg0
  nlinarith [mul_nonneg hx0 hy0]

private def hardyResidual (h : ℝ → ℂ) (y : ℝ) : ℂ :=
  deriv h y - (1 / 2 : ℝ) • weight 1 h y

private theorem hardyResidual_eq (h : ℝ → ℂ) (y : ℝ) :
    hardyResidual h y = deriv h y - ((2 * y)⁻¹ : ℝ) • h y := by
  have hy : (2 * y)⁻¹ = (1 / 2 : ℝ) * y⁻¹ := by
    simp [mul_inv_rev, div_eq_mul_inv] <;> ring
  simp [hardyResidual, weight, hy, smul_smul]

/-- If the Hardy square vanishes at every point, the test function is
zero.  The auxiliary function `h(y)^2/y` has zero derivative on the
connected positive half-line and is zero outside the compact support. -/
private theorem residual_identically_zero_implies_zero (h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ))
    (hr : ∀ y : ℝ, hardyResidual h y = 0) : h = 0 := by
  let q : ℝ → ℂ := fun y => (y⁻¹ : ℝ) • (h y * h y)
  have hqderiv (y : ℝ) (hy : y ∈ Set.Ioi (0 : ℝ)) : deriv q y = 0 := by
    have hyn : y ≠ 0 := ne_of_gt hy
    have hprod : HasDerivAt (fun z : ℝ => h z * h z)
        (deriv h y * h y + h y * deriv h y) y :=
      ((hh.differentiable_one y).hasDerivAt).mul
        ((hh.differentiable_one y).hasDerivAt)
    have hqhas := (hasDerivAt_inv hyn).smul hprod
    have hres : deriv h y = ((2 * y)⁻¹ : ℝ) • h y := by
      simpa only [hardyResidual_eq, sub_eq_zero] using hr y
    have hzero :
        (y⁻¹ : ℝ) • (deriv h y * h y + h y * deriv h y) +
          (-(y ^ 2)⁻¹ : ℝ) • (h y * h y) = 0 := by
      rw [hres]
      simp only [Complex.real_smul, smul_eq_mul]
      push_cast
      field_simp [hyn]
      ring
    exact hqhas.deriv.trans hzero
  have hqdiff : DifferentiableOn ℝ q (Set.Ioi (0 : ℝ)) := by
    intro y hy
    have hyn : y ≠ 0 := ne_of_gt hy
    exact ((hasDerivAt_inv hyn).smul
      (((hh.differentiable_one y).hasDerivAt).mul
        ((hh.differentiable_one y).hasDerivAt))).differentiableAt.differentiableWithinAt
  obtain ⟨b, hb⟩ : BddAbove (tsupport h) := hhc.isBounded.bddAbove
  let y₀ : ℝ := max b 0 + 1
  have hy₀ : y₀ ∈ Set.Ioi (0 : ℝ) := by
    change 0 < max b 0 + 1
    linarith [le_max_right b 0]
  have hy₀out : y₀ ∉ tsupport h := by
    intro hm
    have hle := hb hm
    change max b 0 + 1 ≤ b at hle
    linarith [le_max_left b 0]
  have hy₀zero : h y₀ = 0 := image_eq_zero_of_notMem_tsupport hy₀out
  apply funext
  intro y
  by_cases hy : y ∈ Set.Ioi (0 : ℝ)
  · have hqzero : q y = 0 := by
      calc
        q y = q y₀ :=
          isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
            hqdiff hqderiv hy hy₀
        _ = 0 := by simp [q, hy₀zero]
    have hsq : h y * h y = 0 := by
      have hcast : ((y⁻¹ : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (inv_ne_zero (ne_of_gt hy))
      apply (mul_eq_zero.mp ?_).resolve_left hcast
      simpa [q, Complex.real_smul] using hqzero
    exact (mul_eq_zero.mp hsq).elim id id
  · have hout : y ∉ tsupport h := by
      intro hm
      exact hy (hpos hm)
    exact image_eq_zero_of_notMem_tsupport hout

/-- Every nonzero compact test function has a *strict* Hardy
inequality.  The constant `1/4` remains sharp over the class: this
statement supplies no uniform positive improvement. -/
theorem vertical_hardy_strict (h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h)
    (hpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) (hne : h ≠ 0) :
    (1 / 4 : ℝ) *
        (∫ y : ℝ, ‖h y‖ ^ 2 * (y⁻¹ : ℝ) ^ 2) <
      ∫ y : ℝ, ‖deriv h y‖ ^ 2 := by
  have hex : ∃ y : ℝ, hardyResidual h y ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    exact hne (residual_identically_zero_implies_zero h hh hhc hpos hnot)
  obtain ⟨y₀, hy₀⟩ := hex
  have hrcont : Continuous (hardyResidual h) := by
    exact hh.continuous_deriv_one.sub
      (continuous_const.smul (weight_continuous 1 h hh.continuous hpos))
  have hrcomp : HasCompactSupport (hardyResidual h) := by
    exact hhc.deriv.sub ((weight_compact 1 h hhc).smul_left)
  have hpositive : 0 < ∫ y : ℝ, ‖hardyResidual h y‖ ^ 2 := by
    apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := y₀)
    · exact hrcont.norm.pow 2
    · convert (hrcomp.norm.mul_right) using 1 <;> ext y <;> simp [pow_two]
    · intro y
      exact sq_nonneg _
    · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hy₀)
  have hsq := vertical_hardy_square_identity h hh hhc hpos
  simp_rw [← hardyResidual_eq] at hsq
  linarith

end

end ImbalancedChen.Part3.VerticalHardy20261024zz
