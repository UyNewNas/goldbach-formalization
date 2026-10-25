import ImbalancedChen.Part3TwoKSchwingerBetaEvaluation
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Full complex two-K Schwinger convergence strip. The allocation of the
positive Mellin exponent between the two Schwinger variables is adapted
to the real parts of both orders. No product integrability is assumed.
-/

namespace ImbalancedChen.Part3.ComplexTwoKSchwingerAbsolute20261025a
noncomputable section
open Set MeasureTheory Filter Complex
open ComplexOrderKPositiveLaplace20261025a ComplexOrderKBridgeSourceOnly
open TwoKSchwingerAbsolute20261025a (positiveMeasure reciprocalSum reciprocalSum_pos)

def positiveWeight (alpha beta t u : ℝ) : ℝ :=
  Real.exp (Real.log t * (alpha - 1) + Real.log u * (beta - 1) - t - u)
def positiveFiber (alpha beta c t u x : ℝ) : ℝ :=
  Real.exp (Real.log x * (c - 1)) * Real.exp (-(reciprocalSum t u * x)) *
    positiveWeight alpha beta t u
def gammaEnvelope (a t : ℝ) : ℝ := Real.exp (-t) * t ^ (a - 1)

theorem positive_pairs_ae :
    ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure, 0 < p.1 ∧ 0 < p.2 := by
  apply (ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact ⟨ht, hu⟩

theorem reciprocalSum_inv_bounds {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    0 < 1 / reciprocalSum t u ∧ 1 / reciprocalSum t u ≤ t ∧
      1 / reciprocalSum t u ≤ u := by
  have he : 1 / reciprocalSum t u = t * u / (t + u) := by
    unfold reciprocalSum
    field_simp [ht.ne', hu.ne', (add_pos ht hu).ne'] <;> ring
  refine ⟨one_div_pos.mpr (reciprocalSum_pos ht hu), ?_, ?_⟩
  · rw [he]
    apply (div_le_iff₀ (add_pos ht hu)).mpr
    nlinarith [sq_nonneg t]
  · rw [he]
    apply (div_le_iff₀ (add_pos ht hu)).mpr
    nlinarith [sq_nonneg u]

/-- Allocate different positive powers to the two orders. This is what
permits negative real parts of either order throughout the full strip. -/
theorem positiveWeight_mul_rpow_le {alpha beta c l k t u : ℝ}
    (hl : 0 ≤ l) (hk : 0 ≤ k) (hlk : l + k = c) (ht : 0 < t) (hu : 0 < u) :
    positiveWeight alpha beta t u * (1 / reciprocalSum t u) ^ c ≤
      gammaEnvelope (alpha + l) t * gammaEnvelope (beta + k) u := by
  have hb := reciprocalSum_inv_bounds ht hu
  have hp : (1 / reciprocalSum t u) ^ c ≤ t ^ l * u ^ k := by
    rw [← hlk, Real.rpow_add hb.1]
    exact mul_le_mul (Real.rpow_le_rpow hb.1.le hb.2.1 hl)
      (Real.rpow_le_rpow hb.1.le hb.2.2 hk)
      (Real.rpow_nonneg hb.1.le _) (Real.rpow_nonneg ht.le _)
  calc
    _ ≤ positiveWeight alpha beta t u * (t ^ l * u ^ k) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    _ = _ := by
      unfold positiveWeight gammaEnvelope
      rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hu,
        Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hu]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem positiveFiber_integrable {alpha beta c t u : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hu : 0 < u) : IntegrableOn (positiveFiber alpha beta c t u) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ (c - 1) * Real.exp (-(reciprocalSum t u * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := c - 1)
        (b := reciprocalSum t u) (by linarith) le_rfl (reciprocalSum_pos ht hu)
  apply (hbase.mul_const (positiveWeight alpha beta t u)).congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [positiveFiber, Real.rpow_def_of_pos hx]

theorem positiveFiber_integral {alpha beta c t u : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hu : 0 < u) :
    (∫ x in Ioi (0 : ℝ), positiveFiber alpha beta c t u x) =
      positiveWeight alpha beta t u * (1 / reciprocalSum t u) ^ c * Real.Gamma c := by
  have he : (∫ x in Ioi (0 : ℝ), positiveFiber alpha beta c t u x) =
      ∫ x in Ioi (0 : ℝ), (x ^ (c - 1) *
        Real.exp (-(reciprocalSum t u * x))) * positiveWeight alpha beta t u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [positiveFiber, Real.rpow_def_of_pos hx]
  rw [he, integral_mul_const,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hc (reciprocalSum_pos ht hu)]
  ring

theorem positiveFiber_joint_integrable {alpha beta c l k : ℝ}
    (hc : 0 < c) (hl : 0 ≤ l) (hk : 0 ≤ k) (hlk : l + k = c)
    (hal : 0 < alpha + l) (hbk : 0 < beta + k) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => positiveFiber alpha beta c p.1.1 p.1.2 p.2)
      ((positiveMeasure.prod positiveMeasure).prod positiveMeasure) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      positiveFiber alpha beta c p.1.1 p.1.2 p.2) := by
    unfold positiveFiber positiveWeight reciprocalSum
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [positive_pairs_ae] with p hp
    exact positiveFiber_integrable hc hp.1 hp.2
  · have hg1 : Integrable (gammaEnvelope (alpha + l)) positiveMeasure :=
      Real.GammaIntegral_convergent hal
    have hg2 : Integrable (gammaEnvelope (beta + k)) positiveMeasure :=
      Real.GammaIntegral_convergent hbk
    have henv := (hg1.mul_prod hg2).mul_const (Real.Gamma c)
    apply henv.mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [positive_pairs_ae] with p hp
    have hb := reciprocalSum_pos hp.1 hp.2
    have he : (∫ x in Ioi (0 : ℝ), ‖positiveFiber alpha beta c p.1 p.2 x‖) =
        positiveWeight alpha beta p.1 p.2 * (1 / reciprocalSum p.1 p.2) ^ c * Real.Gamma c := by
      rw [← positiveFiber_integral hc hp.1 hp.2]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        unfold positiveFiber positiveWeight
        positivity
    rw [he, Real.norm_eq_abs, abs_of_nonneg (by unfold positiveWeight; positivity)]
    exact mul_le_mul_of_nonneg_right (positiveWeight_mul_rpow_le hl hk hlk hp.1 hp.2)
      (Real.Gamma_pos_of_pos hc).le

def mellinParameter (nu mu s : ℂ) : ℂ := (s - nu - mu) / 2
def stripMargin (nu mu s : ℂ) : ℝ := (s.re - |nu.re| - |mu.re|) / 4
def leftAllocation (nu mu s : ℂ) : ℝ := (|nu.re| - nu.re) / 2 + stripMargin nu mu s
def rightAllocation (nu mu s : ℂ) : ℝ := (|mu.re| - mu.re) / 2 + stripMargin nu mu s

theorem mellinParameter_re (nu mu s : ℂ) :
    (mellinParameter nu mu s).re = (s.re - nu.re - mu.re) / 2 := by
  simp [mellinParameter, div_eq_mul_inv]

theorem strip_allocations {nu mu s : ℂ} (hs : |nu.re| + |mu.re| < s.re) :
    0 < (mellinParameter nu mu s).re ∧
    0 ≤ leftAllocation nu mu s ∧ 0 ≤ rightAllocation nu mu s ∧
    leftAllocation nu mu s + rightAllocation nu mu s = (mellinParameter nu mu s).re ∧
    0 < nu.re + leftAllocation nu mu s ∧ 0 < mu.re + rightAllocation nu mu s := by
  have hmargin : 0 < stripMargin nu mu s := by unfold stripMargin; linarith
  unfold leftAllocation rightAllocation
  simp only [mellinParameter_re]
  have hn := le_abs_self nu.re
  have hm := le_abs_self mu.re
  have hnn := neg_le_abs nu.re
  have hmn := neg_le_abs mu.re
  refine ⟨by linarith, by linarith, by linarith, ?_, by linarith, by linarith⟩
  unfold stripMargin
  ring

def schwingerCoefficient (nu mu : ℂ) (t u : ℝ) : ℂ :=
  Complex.exp ((Real.log t : ℂ) * (nu - 1) + (Real.log u : ℂ) * (mu - 1) +
    ((-t - u : ℝ) : ℂ))
def schwingerFiber (nu mu s : ℂ) (t u x : ℝ) : ℂ :=
  Complex.exp ((Real.log x : ℂ) * (mellinParameter nu mu s - 1)) *
    (Real.exp (-(reciprocalSum t u * x)) : ℂ) * schwingerCoefficient nu mu t u
def reducedSchwingerDensity (nu mu s : ℂ) (t u : ℝ) : ℂ :=
  schwingerCoefficient nu mu t u *
    ((1 / reciprocalSum t u : ℝ) : ℂ) ^ mellinParameter nu mu s

theorem norm_schwingerCoefficient (nu mu : ℂ) (t u : ℝ) :
    ‖schwingerCoefficient nu mu t u‖ = positiveWeight nu.re mu.re t u := by
  simp [schwingerCoefficient, positiveWeight, Complex.norm_exp]

theorem norm_schwingerFiber (nu mu s : ℂ) (t u x : ℝ) :
    ‖schwingerFiber nu mu s t u x‖ =
      positiveFiber nu.re mu.re (mellinParameter nu mu s).re t u x := by
  rw [schwingerFiber, norm_mul, norm_mul, norm_schwingerCoefficient]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, Complex.one_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), positiveFiber]

/-- Genuine full-strip Schwinger triple absolute integrability. -/
theorem schwingerFiber_joint_integrable {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => schwingerFiber nu mu s p.1.1 p.1.2 p.2)
      ((positiveMeasure.prod positiveMeasure).prod positiveMeasure) := by
  obtain ⟨hc, hl, hk, hlk, hal, hbk⟩ := strip_allocations hs
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      schwingerFiber nu mu s p.1.1 p.1.2 p.2) := by
    unfold schwingerFiber schwingerCoefficient reciprocalSum
    fun_prop
  exact (positiveFiber_joint_integrable hc hl hk hlk hal hbk).mono'
    hm.aestronglyMeasurable (ae_of_all _ fun p => (norm_schwingerFiber nu mu s _ _ _).le)

theorem schwingerFiber_integral_x {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    (∫ x in Ioi (0 : ℝ), schwingerFiber nu mu s t u x) =
      Complex.Gamma (mellinParameter nu mu s) * reducedSchwingerDensity nu mu s t u := by
  have he : (∫ x in Ioi (0 : ℝ), schwingerFiber nu mu s t u x) =
      ∫ x in Ioi (0 : ℝ), ((x : ℂ) ^ (mellinParameter nu mu s - 1) *
        Complex.exp (-((reciprocalSum t u : ℂ) * (x : ℂ)))) * schwingerCoefficient nu mu t u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [schwingerFiber, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le, Complex.ofReal_exp]
    push_cast
    rfl
  rw [he, integral_mul_const, Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (strip_allocations hs).1 (reciprocalSum_pos ht hu)]
  unfold reducedSchwingerDensity
  push_cast
  ring

theorem reducedSchwingerDensity_integrable {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) :
    Integrable (fun p : ℝ × ℝ => reducedSchwingerDensity nu mu s p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hgamma := Complex.Gamma_ne_zero_of_re_pos (strip_allocations hs).1
  have h := (schwingerFiber_joint_integrable hs).integral_prod_left.const_mul
    (Complex.Gamma (mellinParameter nu mu s))⁻¹
  apply h.congr
  filter_upwards [positive_pairs_ae] with p hp
  rw [schwingerFiber_integral_x hs hp.1 hp.2]
  simp only [← mul_assoc, inv_mul_cancel₀ hgamma, one_mul]

end
end ImbalancedChen.Part3.ComplexTwoKSchwingerAbsolute20261025a
