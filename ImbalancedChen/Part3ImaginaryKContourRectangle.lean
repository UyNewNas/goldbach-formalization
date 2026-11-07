import ImbalancedChen.Part3ComplexOrderKPositiveLaplace
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Actual imaginary-K finite rectangle and vanishing vertical edges

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The entire function is exp(-q*cosh(z)+i*tau*z), with no contour identity
assumed. Pinned Cauchy-Goursat proves the finite rectangle identity. The
vertical edges are bounded uniformly along their full height by an actual
cosh exponential, which tends to zero on both sides. The next step may
therefore pass to whole-line integrals without retaining boundary terms.
No spectral estimate, measure, or Plancherel theorem is assumed.
-/

namespace ImbalancedChen.Part3.ImaginaryKContourRectangle20261025a

noncomputable section
open Complex Set Filter MeasureTheory Topology

def contourKernel (q tau : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(q : ℂ) * Complex.cosh z + ((tau : ℂ) * I) * z)

def horizontal (q tau height x : ℝ) : ℂ :=
  contourKernel q tau ((x : ℂ) + (height : ℂ) * I)

def verticalEdge (q tau x height : ℝ) : ℂ :=
  ∫ y : ℝ in 0..height, horizontal q tau y x

theorem contourKernel_differentiable (q tau : ℝ) : Differentiable ℂ (contourKernel q tau) := by
  unfold contourKernel
  fun_prop

/-- The full finite rectangle, including both oriented vertical edges. -/
theorem finite_rectangle_identity (q tau R height : ℝ) :
    (∫ x : ℝ in (-R)..R, horizontal q tau 0 x) -
      (∫ x : ℝ in (-R)..R, horizontal q tau height x) +
      I * verticalEdge q tau R height - I * verticalEdge q tau (-R) height = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (contourKernel q tau) ((-R : ℝ) : ℂ) ((R : ℂ) + (height : ℂ) * I)
    (contourKernel_differentiable q tau).differentiableOn
  simpa only [horizontal, verticalEdge, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, zero_add,
    add_zero, sub_zero, smul_eq_mul] using h

/-- Exact modulus on a horizontal line; the order exponential is retained. -/
theorem norm_horizontal (q tau height x : ℝ) :
    ‖horizontal q tau height x‖ =
      Real.exp (-q * Real.cosh x * Real.cos height - tau * height) := by
  have hcosh : (Complex.cosh ((x : ℂ) + (height : ℂ) * I)).re =
      Real.cosh x * Real.cos height := by
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [horizontal, contourKernel, Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, hcosh]
  ring

/-- Uniform bound over the entire vertical segment, including negative
heights. Its tau-dependent factor is fixed while the sides go to infinity. -/
theorem norm_horizontal_le_vertical_majorant {q : ℝ} (hq : 0 < q)
    (tau x height y : ℝ) (hheight : |height| < Real.pi / 2)
    (hy : |y| ≤ |height|) :
    ‖horizontal q tau y x‖ ≤
      Real.exp (-q * Real.cosh x * Real.cos |height| + |tau| * |height|) := by
  have hpi : |height| ≤ Real.pi := by linarith [Real.pi_pos]
  have hcos : Real.cos |height| ≤ Real.cos y := by
    rw [← Real.cos_abs y]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) hpi hy
  have hprod := mul_le_mul_of_nonneg_left hcos (mul_pos hq (Real.cosh_pos x)).le
  have htau : -tau * y ≤ |tau| * |height| := by
    calc
      -tau * y = -(tau * y) := by ring
      _ ≤ |tau * y| := neg_le_abs _
      _ = |tau| * |y| := abs_mul _ _
      _ ≤ |tau| * |height| := mul_le_mul_of_nonneg_left hy (abs_nonneg tau)
  rw [norm_horizontal]
  apply Real.exp_le_exp.mpr
  nlinarith only [hprod, htau]

theorem norm_verticalEdge_le {q : ℝ} (hq : 0 < q) (tau x height : ℝ)
    (hheight : |height| < Real.pi / 2) :
    ‖verticalEdge q tau x height‖ ≤
      Real.exp (-q * Real.cosh x * Real.cos |height| + |tau| * |height|) * |height| := by
  unfold verticalEdge
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := height) (f := fun y => horizontal q tau y x) (fun y hy => by
      have hy' : min 0 height < y ∧ y ≤ max 0 height := hy
      have hlow : -|height| ≤ min 0 height :=
        le_min (neg_nonpos.mpr (abs_nonneg height)) (neg_abs_le height)
      have hupp : max 0 height ≤ |height| := max_le (abs_nonneg height) (le_abs_self height)
      exact norm_horizontal_le_vertical_majorant hq tau x height y hheight
        (abs_le.mpr ⟨hlow.trans hy'.1.le, hy'.2.trans hupp⟩))

private theorem tendsto_cosh_atTop : Tendsto Real.cosh atTop atTop := by
  have hhalf : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * Real.exp x) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono _ hhalf
  intro x
  rw [Real.cosh_eq]
  have hpos := Real.exp_pos (-x)
  linarith only [hpos]

/-- The genuine superexponential-in-x vertical majorant tends to zero. -/
theorem tendsto_vertical_majorant_zero {q : ℝ} (hq : 0 < q) (tau height : ℝ)
    (hheight : |height| < Real.pi / 2) :
    Tendsto (fun x : ℝ =>
      Real.exp (-q * Real.cosh x * Real.cos |height| + |tau| * |height|) * |height|)
      atTop (𝓝 0) := by
  have hc : 0 < Real.cos |height| := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [abs_nonneg height, Real.pi_pos], hheight⟩
  have hn : Tendsto (fun x : ℝ => (-(q * Real.cos |height|)) * Real.cosh x)
      atTop atBot := tendsto_cosh_atTop.const_mul_atTop_of_neg (neg_neg_of_pos (mul_pos hq hc))
  have he := (Real.tendsto_exp_atBot.comp hn).const_mul (Real.exp (|tau| * |height|))
  have hbase : Tendsto (fun x : ℝ =>
      Real.exp (-q * Real.cosh x * Real.cos |height| + |tau| * |height|)) atTop (𝓝 0) := by
    have he' : Tendsto (fun x : ℝ => Real.exp (|tau| * |height|) *
      Real.exp ((-(q * Real.cos |height|)) * Real.cosh x)) atTop (𝓝 0) := by
      simpa only [mul_zero] using he
    apply he'.congr
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [zero_mul] using hbase.mul_const |height|

theorem tendsto_right_verticalEdge_zero {q : ℝ} (hq : 0 < q) (tau height : ℝ)
    (hheight : |height| < Real.pi / 2) :
    Tendsto (fun R : ℝ => verticalEdge q tau R height) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (tendsto_vertical_majorant_zero hq tau height hheight)
  intro R
  exact norm_verticalEdge_le hq tau R height hheight

theorem tendsto_left_verticalEdge_zero {q : ℝ} (hq : 0 < q) (tau height : ℝ)
    (hheight : |height| < Real.pi / 2) :
    Tendsto (fun R : ℝ => verticalEdge q tau (-R) height) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (tendsto_vertical_majorant_zero hq tau height hheight)
  intro R
  simpa only [Real.cosh_neg] using norm_verticalEdge_le hq tau (-R) height hheight

end
end ImbalancedChen.Part3.ImaginaryKContourRectangle20261025a
