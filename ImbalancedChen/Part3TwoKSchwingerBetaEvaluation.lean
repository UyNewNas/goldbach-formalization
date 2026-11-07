import ImbalancedChen.Part3TwoKSchwingerAbsolute
import ImbalancedChen.Part3ComplexBetaHalfLineGamma
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The genuine reduced two-K double integral is evaluated by u=t*y,
an absolutely convergent Gamma fiber, and the actual complex halfline Beta
theorem. No double-integral or product-formula premise is introduced.
-/

namespace ImbalancedChen.Part3.TwoKSchwingerBetaEvaluation20261025a
noncomputable section
open Set MeasureTheory Filter Complex
open TwoKSchwingerAbsolute20261025a
open ImbalancedChen.Part3ComplexBetaHalfLineGamma

def normalizedGammaFiber (d : ℂ) (r t : ℝ) : ℂ :=
  (r : ℂ) ^ d * Complex.exp ((Real.log t : ℂ) * (d - 1)) *
    (Real.exp (-(r * t)) : ℂ)

theorem normalizedGammaFiber_norm (d : ℂ) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ‖normalizedGammaFiber d r t‖ =
      r ^ d.re * (t ^ (d.re - 1) * Real.exp (-(r * t))) := by
  rw [normalizedGammaFiber, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.sub_re, Complex.one_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos ht]
  ring

theorem normalizedGammaFiber_integrable {d : ℂ} (hd : 0 < d.re) {r : ℝ}
    (hr : 0 < r) : IntegrableOn (normalizedGammaFiber d r) (Ioi 0) := by
  have hb : IntegrableOn
      (fun t : ℝ => t ^ (d.re - 1) * Real.exp (-(r * t))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := d.re - 1)
        (b := r) (by linarith) le_rfl hr
  have hm : Measurable (normalizedGammaFiber d r) := by
    unfold normalizedGammaFiber
    fun_prop
  apply (hb.const_mul (r ^ d.re)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (normalizedGammaFiber_norm d hr ht).le

theorem normalizedGammaFiber_integral_norm {d : ℂ} (hd : 0 < d.re) {r : ℝ}
    (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), ‖normalizedGammaFiber d r t‖) = Real.Gamma d.re := by
  have he : (∫ t in Ioi (0 : ℝ), ‖normalizedGammaFiber d r t‖) =
      ∫ t in Ioi (0 : ℝ), r ^ d.re *
        (t ^ (d.re - 1) * Real.exp (-(r * t))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact normalizedGammaFiber_norm d hr ht
  rw [he, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hd hr]
  have hp : r ^ d.re * (1 / r) ^ d.re = 1 := by
    rw [← Real.mul_rpow hr.le (one_div_pos.mpr hr).le]
    simp [hr.ne']
  rw [← mul_assoc, hp, one_mul]

theorem normalizedGammaFiber_integral {d : ℂ} (hd : 0 < d.re) {r : ℝ}
    (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), normalizedGammaFiber d r t) = Complex.Gamma d := by
  have he : (∫ t in Ioi (0 : ℝ), normalizedGammaFiber d r t) =
      (r : ℂ) ^ d * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ (d - 1) * Complex.exp (-((r : ℂ) * (t : ℂ))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [normalizedGammaFiber,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
      ← Complex.ofReal_log ht.le, Complex.ofReal_exp]
    push_cast
    ring
  rw [he, Complex.integral_cpow_mul_exp_neg_mul_Ioi hd hr]
  have hp : (r : ℂ) ^ d * ((1 / r : ℝ) : ℂ) ^ d = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg hr.le (one_div_pos.mpr hr).le]
    simp [hr.ne']
  push_cast at hp ⊢
  rw [← mul_assoc, hp, one_mul]

def scaledBetaFiber (a b d : ℂ) (y t : ℝ) : ℂ :=
  halflineKernel b a y * normalizedGammaFiber d (1 + y) t

theorem scaledBetaFiber_joint_integrable {a b d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hd : 0 < d.re) :
    Integrable (fun p : ℝ × ℝ => scaledBetaFiber a b d p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hm : Measurable (fun p : ℝ × ℝ => scaledBetaFiber a b d p.1 p.2) := by
    unfold scaledBetaFiber halflineKernel normalizedGammaFiber
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (normalizedGammaFiber_integrable hd (by linarith : 0 < 1 + y)).const_mul _
  · have hbase := (integrableOn_halflineKernel hb ha).norm.mul_const (Real.Gamma d.re)
    apply hbase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    simp only [scaledBetaFiber, norm_mul, integral_const_mul]
    rw [normalizedGammaFiber_integral_norm hd (by linarith : 0 < 1 + y)]

def gammaBetaKernel (a b d : ℂ) (t u : ℝ) : ℂ :=
  (Real.exp (-t - u) : ℂ) * (t : ℂ) ^ (a - 1) * (u : ℂ) ^ (b - 1) /
    ((t + u : ℝ) : ℂ) ^ (a + b - d)

/-- The actual one-dimensional Jacobian u=t*y, with no change-of-variable
identity hidden in a hypothesis. -/
theorem gammaBetaKernel_scaled (a b d : ℂ) {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    (t : ℂ) * gammaBetaKernel a b d t (t * y) = scaledBetaFiber a b d y t := by
  have hr : 0 < 1 + y := by linarith
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hrC : ((1 + y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hpT : (t : ℂ) ^ (a - 1) * (t : ℂ) ^ (b - 1) * (t : ℂ) =
      (t : ℂ) ^ (a + b - d) * (t : ℂ) ^ (d - 1) := by
    calc
      _ = (t : ℂ) ^ (a - 1) * (t : ℂ) ^ (b - 1) * (t : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_add _ _ htC, ← Complex.cpow_add _ _ htC,
          ← Complex.cpow_add _ _ htC]
        congr 1
        ring
  have hpR : ((1 + y : ℝ) : ℂ) ^ (a + b) =
      ((1 + y : ℝ) : ℂ) ^ (a + b - d) * ((1 + y : ℝ) : ℂ) ^ d := by
    rw [← Complex.cpow_add _ _ hrC]
    congr 1
    ring
  have htnz : (t : ℂ) ^ (a + b - d) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl htC)
  have hrnz : ((1 + y : ℝ) : ℂ) ^ d ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hrC)
  have hrcnz : ((1 + y : ℝ) : ℂ) ^ (a + b - d) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hrC)
  have hpowD : Complex.exp ((Real.log t : ℂ) * (d - 1)) = (t : ℂ) ^ (d - 1) := by
    rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le]
  have hexp : -t - t * y = -((1 + y) * t) := by ring
  unfold gammaBetaKernel scaledBetaFiber halflineKernel normalizedGammaFiber
  rw [show t + t * y = t * (1 + y) by ring, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ht.le hy.le,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ht.le hr.le,
    hpowD, hexp, hpR]
  calc
    _ = (Real.exp (-((1 + y) * t)) : ℂ) *
        ((t : ℂ) ^ (a - 1) * (t : ℂ) ^ (b - 1) * (t : ℂ)) *
        (y : ℂ) ^ (b - 1) /
        ((t : ℂ) ^ (a + b - d) * ((1 + y : ℝ) : ℂ) ^ (a + b - d)) := by ring
    _ = (Real.exp (-((1 + y) * t)) : ℂ) *
        ((t : ℂ) ^ (a + b - d) * (t : ℂ) ^ (d - 1)) *
        (y : ℂ) ^ (b - 1) /
        ((t : ℂ) ^ (a + b - d) * ((1 + y : ℝ) : ℂ) ^ (a + b - d)) := by rw [hpT]
    _ = _ := by field_simp [htnz, hrnz, hrcnz] <;> ring

/-- A Gamma-Beta double integral evaluated from its actual Jacobian and
an absolutely integrable transformed fiber. -/
theorem gammaBetaKernel_iterated_integral {a b d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hd : 0 < d.re) :
    (∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), gammaBetaKernel a b d t u) =
      Complex.Gamma d * (Complex.Gamma b * Complex.Gamma a / Complex.Gamma (b + a)) := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), scaledBetaFiber a b d y t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hscale := integral_comp_mul_left_Ioi' (gammaBetaKernel a b d t) 0 ht
      rw [mul_zero, Complex.real_smul] at hscale
      rw [← hscale, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact gammaBetaKernel_scaled a b d ht hy
    _ = ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), scaledBetaFiber a b d y t :=
      (integral_integral_swap (scaledBetaFiber_joint_integrable ha hb hd)).symm
    _ = ∫ y in Ioi (0 : ℝ), halflineKernel b a y * Complex.Gamma d := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      simp only [scaledBetaFiber, integral_const_mul]
      rw [normalizedGammaFiber_integral hd (by linarith : 0 < 1 + y)]
    _ = _ := by rw [integral_mul_const, integral_halflineKernel_eq_gamma hb ha]; ring

def gammaA (tau sigma s : ℝ) : ℂ := (tau : ℂ) * I + mellinParameter tau sigma s
def gammaB (tau sigma s : ℝ) : ℂ := (sigma : ℂ) * I + mellinParameter tau sigma s
def gammaD (tau sigma s : ℝ) : ℂ :=
  gammaA tau sigma s + gammaB tau sigma s - mellinParameter tau sigma s

theorem gamma_parameters_re (tau sigma s : ℝ) :
    (gammaA tau sigma s).re = s / 2 ∧ (gammaB tau sigma s).re = s / 2 ∧
      (gammaD tau sigma s).re = s / 2 := by
  simp [gammaA, gammaB, gammaD, mellinParameter_re]

theorem schwingerBetaKernel_integral (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      schwingerBetaKernel tau sigma s p.1 p.2) =
      Complex.Gamma (gammaD tau sigma s) *
        (Complex.Gamma (gammaB tau sigma s) * Complex.Gamma (gammaA tau sigma s) /
          Complex.Gamma (s : ℂ)) := by
  have he : schwingerBetaKernel tau sigma s =
      gammaBetaKernel (gammaA tau sigma s) (gammaB tau sigma s) (gammaD tau sigma s) := by
    funext t u
    have hexponent : gammaA tau sigma s + gammaB tau sigma s - gammaD tau sigma s =
        mellinParameter tau sigma s := by unfold gammaD; ring
    simp only [schwingerBetaKernel, gammaBetaKernel, hexponent, gammaA, gammaB]
  have hsum : gammaB tau sigma s + gammaA tau sigma s = (s : ℂ) := by
    unfold gammaA gammaB mellinParameter
    ring
  rw [integral_prod _ (schwingerBetaKernel_integrable tau sigma hs), he]
  have hp := gamma_parameters_re tau sigma s
  rw [gammaBetaKernel_iterated_integral (by rw [hp.1]; exact half_pos hs)
    (by rw [hp.2.1]; exact half_pos hs) (by rw [hp.2.2]; exact half_pos hs), hsum]

theorem actualSchwingerProduct_integral_four_gamma (tau sigma : ℝ) {s : ℝ}
    (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), actualSchwingerProduct tau sigma s x) =
      Complex.Gamma (mellinParameter tau sigma s) * Complex.Gamma (gammaD tau sigma s) *
        Complex.Gamma (gammaB tau sigma s) * Complex.Gamma (gammaA tau sigma s) /
          Complex.Gamma (s : ℂ) := by
  rw [actualSchwingerProduct_integral_eq_beta_reduction tau sigma hs,
    schwingerBetaKernel_integral tau sigma hs]
  ring

end
end ImbalancedChen.Part3.TwoKSchwingerBetaEvaluation20261025a
