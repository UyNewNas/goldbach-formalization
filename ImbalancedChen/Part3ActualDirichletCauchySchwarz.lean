import ImbalancedChen.Part3ActualMobiusDirichletCovariance
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Pointwise Cauchy--Schwarz and Hermitian algebra for the ACTUAL chart
Dirichlet pairing of the existing literal sliceDx/sliceDy derivatives.
The exact complex two-component Lagrange identity proves the bound;
hyperbolic height weighting is then treated as its actual real square.

Only the scalar energy PAIR is used. No scalar quotient gradient vector
is introduced, and no conformality/energy target is a supplied premise.
The final generic L1 consequence requires genuine diagonal integrability
and mixed measurability, but never assumes mixed integrability itself.
-/

namespace ImbalancedChen.Part3.ActualDirichletCauchySchwarz20261025a

noncomputable section
open Set MeasureTheory
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a
open ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a

/-- The exact two-component complex Lagrange identity. -/
theorem complex_pair_lagrange (a b c d : ℂ) :
    Complex.normSq (star a * c + star b * d) + Complex.normSq (a * d - b * c) =
      (Complex.normSq a + Complex.normSq b) *
        (Complex.normSq c + Complex.normSq d) := by
  simp only [Complex.star_def, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem complex_pair_cauchySchwarz (a b c d : ℂ) :
    Complex.normSq (star a * c + star b * d) ≤
      (Complex.normSq a + Complex.normSq b) *
        (Complex.normSq c + Complex.normSq d) := by
  have h := complex_pair_lagrange a b c d
  have hpos := Complex.normSq_nonneg (a * d - b * c)
  linarith

def chartEnergySq (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  Complex.normSq (sliceDx F p) + Complex.normSq (sliceDy F p)

theorem chartEnergySq_nonneg (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    0 ≤ chartEnergySq F p :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem chartDirichlet_normSq_le (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    Complex.normSq (chartDirichlet F G p) ≤ chartEnergySq F p * chartEnergySq G p :=
  complex_pair_cauchySchwarz _ _ _ _

/-- Exact diagonal real part, with no lost imaginary contribution. -/
theorem chartDirichlet_self_re_eq_energySq (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    (chartDirichlet F F p).re = chartEnergySq F p := by
  rw [chartDirichlet_self_eq]
  rfl

theorem chartDirichlet_star (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    star (chartDirichlet F G p) = chartDirichlet G F p := by
  simp only [chartDirichlet, star_add, star_mul, star_star]
  ring

theorem hyperbolicChartDirichlet_self_re_eq (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    (hyperbolicChartDirichlet F F p).re = p.2^2 * chartEnergySq F p := by
  rw [hyperbolicChartDirichlet, chartDirichlet_self_eq]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

/-- Cauchy--Schwarz for the actual scalar hyperbolic energy pair. -/
theorem hyperbolicChartDirichlet_normSq_le (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    Complex.normSq (hyperbolicChartDirichlet F G p) ≤
      (hyperbolicChartDirichlet F F p).re * (hyperbolicChartDirichlet G G p).re := by
  calc
    _ = (p.2^2)^2 * Complex.normSq (chartDirichlet F G p) := by
      rw [hyperbolicChartDirichlet, Complex.normSq_mul, ← Complex.ofReal_pow,
        Complex.normSq_ofReal]
      ring
    _ ≤ (p.2^2)^2 * (chartEnergySq F p * chartEnergySq G p) :=
      mul_le_mul_of_nonneg_left (chartDirichlet_normSq_le F G p) (sq_nonneg _)
    _ = _ := by
      rw [hyperbolicChartDirichlet_self_re_eq, hyperbolicChartDirichlet_self_re_eq]
      ring

theorem hyperbolicChartDirichlet_star (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    star (hyperbolicChartDirichlet F G p) = hyperbolicChartDirichlet G F p := by
  unfold hyperbolicChartDirichlet
  rw [star_mul, chartDirichlet_star]
  have hreal : star ((p.2 : ℂ)^2) = (p.2 : ℂ)^2 := by simp
  rw [hreal]
  ring

theorem chartDirichlet_two_mul_norm_le (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    2 * ‖chartDirichlet F G p‖ ≤ chartEnergySq F p + chartEnergySq G p := by
  have htriangle : ‖chartDirichlet F G p‖ ≤
      ‖sliceDx F p‖ * ‖sliceDx G p‖ + ‖sliceDy F p‖ * ‖sliceDy G p‖ := by
    simpa only [chartDirichlet, norm_mul, norm_star] using
      norm_add_le (star (sliceDx F p) * sliceDx G p)
        (star (sliceDy F p) * sliceDy G p)
  simp only [chartEnergySq, Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖sliceDx F p‖ - ‖sliceDx G p‖),
    sq_nonneg (‖sliceDy F p‖ - ‖sliceDy G p‖)]

theorem hyperbolicChartDirichlet_two_mul_norm_le (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    2 * ‖hyperbolicChartDirichlet F G p‖ ≤
      (hyperbolicChartDirichlet F F p).re + (hyperbolicChartDirichlet G G p).re := by
  have hheight : ‖(p.2 : ℂ)^2‖ = p.2^2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ = p.2^2 * (2 * ‖chartDirichlet F G p‖) := by
      rw [hyperbolicChartDirichlet, norm_mul, hheight]
      ring
    _ ≤ p.2^2 * (chartEnergySq F p + chartEnergySq G p) :=
      mul_le_mul_of_nonneg_left (chartDirichlet_two_mul_norm_le F G p) (sq_nonneg _)
    _ = _ := by
      rw [hyperbolicChartDirichlet_self_re_eq, hyperbolicChartDirichlet_self_re_eq]
      ring

private theorem sliceDx_add (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    sliceDx (F + G) p = sliceDx F p + sliceDx G p := by
  have hline : HasDerivAt (fun x : ℝ => (x, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact deriv_add (hF.hasFDerivAt.comp_hasDerivAt p.1 hline).differentiableAt
    (hG.hasFDerivAt.comp_hasDerivAt p.1 hline).differentiableAt

private theorem sliceDy_add (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    sliceDy (F + G) p = sliceDy F p + sliceDy G p := by
  have hline : HasDerivAt (fun y : ℝ => (p.1, y)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact deriv_add (hF.hasFDerivAt.comp_hasDerivAt p.2 hline).differentiableAt
    (hG.hasFDerivAt.comp_hasDerivAt p.2 hline).differentiableAt

theorem chartDirichlet_add_left (F G H : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    chartDirichlet (F + G) H p = chartDirichlet F H p + chartDirichlet G H p := by
  simp only [chartDirichlet, sliceDx_add F G p hF hG, sliceDy_add F G p hF hG, star_add]
  ring

theorem chartDirichlet_add_right (F G H : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hG : DifferentiableAt ℝ G p) (hH : DifferentiableAt ℝ H p) :
    chartDirichlet F (G + H) p = chartDirichlet F G p + chartDirichlet F H p := by
  simp only [chartDirichlet, sliceDx_add G H p hG hH, sliceDy_add G H p hG hH]
  ring

theorem chartDirichlet_smul_left (c : ℂ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    chartDirichlet (c • F) G p = star c * chartDirichlet F G p := by
  simp only [chartDirichlet, sliceDx, sliceDy, Pi.smul_apply, smul_eq_mul,
    deriv_const_mul_field, star_mul]
  ring

theorem chartDirichlet_smul_right (c : ℂ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    chartDirichlet F (c • G) p = c * chartDirichlet F G p := by
  simp only [chartDirichlet, sliceDx, sliceDy, Pi.smul_apply, smul_eq_mul,
    deriv_const_mul_field]
  ring

theorem hyperbolicChartDirichlet_add_left (F G H : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    hyperbolicChartDirichlet (F + G) H p =
      hyperbolicChartDirichlet F H p + hyperbolicChartDirichlet G H p := by
  simp only [hyperbolicChartDirichlet, chartDirichlet_add_left F G H p hF hG]
  ring

theorem hyperbolicChartDirichlet_add_right (F G H : ℝ × ℝ → ℂ) (p : ℝ × ℝ)
    (hG : DifferentiableAt ℝ G p) (hH : DifferentiableAt ℝ H p) :
    hyperbolicChartDirichlet F (G + H) p =
      hyperbolicChartDirichlet F G p + hyperbolicChartDirichlet F H p := by
  simp only [hyperbolicChartDirichlet, chartDirichlet_add_right F G H p hG hH]
  ring

theorem hyperbolicChartDirichlet_smul_left (c : ℂ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    hyperbolicChartDirichlet (c • F) G p = star c * hyperbolicChartDirichlet F G p := by
  simp only [hyperbolicChartDirichlet, chartDirichlet_smul_left]
  ring

theorem hyperbolicChartDirichlet_smul_right (c : ℂ) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    hyperbolicChartDirichlet F (c • G) p = c * hyperbolicChartDirichlet F G p := by
  simp only [hyperbolicChartDirichlet, chartDirichlet_smul_right]
  ring

/-- A real diagonal-energy L1 budget gives the complex mixed-energy L1
budget on ANY actual measurable realization, with mixed measurability
explicit and no assertion that a gradient vector descends as a scalar. -/
theorem integrable_mixed_of_diagonal {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (P : α → ℝ × ℝ) (F G : ℝ × ℝ → ℂ)
    (hmeas : AEStronglyMeasurable (fun x => hyperbolicChartDirichlet F G (P x)) μ)
    (hF : Integrable (fun x => (hyperbolicChartDirichlet F F (P x)).re) μ)
    (hG : Integrable (fun x => (hyperbolicChartDirichlet G G (P x)).re) μ) :
    Integrable (fun x => hyperbolicChartDirichlet F G (P x)) μ := by
  apply (hF.add hG).mono' hmeas
  exact Filter.Eventually.of_forall fun x => by
    have h := hyperbolicChartDirichlet_two_mul_norm_le F G (P x)
    have hn := norm_nonneg (hyperbolicChartDirichlet F G (P x))
    linarith

end
end ImbalancedChen.Part3.ActualDirichletCauchySchwarz20261025a
