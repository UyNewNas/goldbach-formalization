import ImbalancedChen.Part3ComplexTwoKSchwingerAbsolute
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The full-strip absolutely convergent Schwinger fiber is identified with
the actual complex-order K product and evaluated by the proved generic
Gamma-Beta integral. No product-integrability or Mellin-formula premise.
-/

namespace ImbalancedChen.Part3.ComplexTwoKSchwingerProduct20261025a
noncomputable section
open Set MeasureTheory Filter Complex
open ComplexOrderKPositiveLaplace20261025a ComplexOrderKBridgeSourceOnly
open TwoKSchwingerAbsolute20261025a (positiveMeasure reciprocalSum)
open TwoKSchwingerBetaEvaluation20261025a (gammaBetaKernel gammaBetaKernel_iterated_integral)
open ComplexTwoKSchwingerAbsolute20261025a

theorem schwingerCoefficient_eq_actual (nu mu : ℂ) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    schwingerCoefficient nu mu t u =
      (t : ℂ) ^ (nu - 1) * (u : ℂ) ^ (mu - 1) * (Real.exp (-t - u) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
    ← Complex.ofReal_log ht.le, ← Complex.ofReal_log hu.le]
  unfold schwingerCoefficient
  rw [Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp]

theorem schwingerFiber_eq_actual (nu mu s : ℂ) {q t u : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hu : 0 < u) :
    schwingerFiber nu mu s t u (q ^ 2 / 4) =
      ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter nu mu s - 1) *
        dampedGammaDensity nu q t * dampedGammaDensity mu q u := by
  have hx : 0 < q ^ 2 / 4 := by positivity
  have hexp : -(reciprocalSum t u * (q ^ 2 / 4)) + (-t - u) =
      -t - q ^ 2 / (4 * t) + (-u - q ^ 2 / (4 * u)) := by
    unfold reciprocalSum
    field_simp [ht.ne', hu.ne'] <;> ring
  have he : (Real.exp (-(reciprocalSum t u * (q ^ 2 / 4))) : ℂ) *
      (Real.exp (-t - u) : ℂ) =
      (Real.exp (-t) : ℂ) * (Real.exp (-(q ^ 2 / (4 * t))) : ℂ) *
        ((Real.exp (-u) : ℂ) * (Real.exp (-(q ^ 2 / (4 * u))) : ℂ)) := by
    norm_cast
    simp only [← Real.exp_add]
    congr 1
    exact hexp
  have hpow : Complex.exp ((Real.log (q ^ 2 / 4) : ℂ) * (mellinParameter nu mu s - 1)) =
      ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter nu mu s - 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le]
  rw [schwingerFiber, hpow, schwingerCoefficient_eq_actual nu mu ht hu]
  unfold dampedGammaDensity
  calc
    _ = ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter nu mu s - 1) *
        (t : ℂ) ^ (nu - 1) * (u : ℂ) ^ (mu - 1) *
        ((Real.exp (-(reciprocalSum t u * (q ^ 2 / 4))) : ℂ) *
          (Real.exp (-t - u) : ℂ)) := by ring
    _ = _ := by rw [he]; ring

theorem schwingerFiber_pair_integral_at_q (nu mu s : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      schwingerFiber nu mu s p.1 p.2 (q ^ 2 / 4)) =
      ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter nu mu s - 1) *
        (2 * ((q / 2 : ℝ) : ℂ) ^ nu * complexOrderK nu q) *
        (2 * ((q / 2 : ℝ) : ℂ) ^ mu * complexOrderK mu q) := by
  calc
    _ = ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter nu mu s - 1) *
          (dampedGammaDensity nu q p.1 * dampedGammaDensity mu q p.2) := by
      apply integral_congr_ae
      filter_upwards [positive_pairs_ae] with p hp
      rw [schwingerFiber_eq_actual nu mu s hq hp.1 hp.2]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_prod_mul,
        dampedGammaDensity_integral nu hq, dampedGammaDensity_integral mu hq]
      ring

def actualSchwingerProduct (nu mu s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (mellinParameter nu mu s - 1) *
    (2 * (Real.sqrt x : ℂ) ^ nu * complexOrderK nu (2 * Real.sqrt x)) *
    (2 * (Real.sqrt x : ℂ) ^ mu * complexOrderK mu (2 * Real.sqrt x))

theorem schwingerFiber_pair_integral (nu mu s : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      schwingerFiber nu mu s p.1 p.2 x) = actualSchwingerProduct nu mu s x := by
  have hq : 0 < 2 * Real.sqrt x := mul_pos (by norm_num) (Real.sqrt_pos.mpr hx)
  have hxq : (2 * Real.sqrt x) ^ 2 / 4 = x := by nlinarith [Real.sq_sqrt hx.le]
  have hhalf : (2 * Real.sqrt x) / 2 = Real.sqrt x := by ring
  simpa only [hxq, hhalf, actualSchwingerProduct] using
    schwingerFiber_pair_integral_at_q nu mu s hq

theorem actualSchwingerProduct_integrable {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) :
    IntegrableOn (actualSchwingerProduct nu mu s) (Ioi 0) := by
  have h := (schwingerFiber_joint_integrable hs).integral_prod_right
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact schwingerFiber_pair_integral nu mu s hx

theorem actualSchwingerProduct_integral_reduction {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), actualSchwingerProduct nu mu s x) =
      Complex.Gamma (mellinParameter nu mu s) *
        ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
          reducedSchwingerDensity nu mu s p.1 p.2 := by
  calc
    _ = ∫ x in Ioi (0 : ℝ), ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        schwingerFiber nu mu s p.1 p.2 x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (schwingerFiber_pair_integral nu mu s hx).symm
    _ = ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ∫ x in Ioi (0 : ℝ), schwingerFiber nu mu s p.1 p.2 x :=
      (integral_integral_swap (schwingerFiber_joint_integrable hs)).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [positive_pairs_ae] with p hp
      exact schwingerFiber_integral_x hs hp.1 hp.2

def gammaA (nu mu s : ℂ) : ℂ := nu + mellinParameter nu mu s
def gammaB (nu mu s : ℂ) : ℂ := mu + mellinParameter nu mu s
def gammaD (nu mu s : ℂ) : ℂ := nu + mu + mellinParameter nu mu s

theorem gamma_parameters_positive {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) :
    0 < (gammaA nu mu s).re ∧ 0 < (gammaB nu mu s).re ∧ 0 < (gammaD nu mu s).re := by
  have hn := le_abs_self nu.re
  have hm := le_abs_self mu.re
  have hnn := neg_le_abs nu.re
  have hmn := neg_le_abs mu.re
  simp only [gammaA, gammaB, gammaD, Complex.add_re, mellinParameter_re]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem reducedSchwingerDensity_eq_betaKernel (nu mu s : ℂ) {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) :
    reducedSchwingerDensity nu mu s t u =
      gammaBetaKernel (gammaA nu mu s) (gammaB nu mu s) (gammaD nu mu s) t u := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have he : 1 / reciprocalSum t u = t * u / (t + u) := by
    unfold reciprocalSum
    field_simp [ht.ne', hu.ne', (add_pos ht hu).ne'] <;> ring
  have htP : (t : ℂ) ^ (nu - 1) * (t : ℂ) ^ mellinParameter nu mu s =
      (t : ℂ) ^ (gammaA nu mu s - 1) := by
    rw [← Complex.cpow_add _ _ htC]
    congr 1
    unfold gammaA
    ring
  have huP : (u : ℂ) ^ (mu - 1) * (u : ℂ) ^ mellinParameter nu mu s =
      (u : ℂ) ^ (gammaB nu mu s - 1) := by
    rw [← Complex.cpow_add _ _ huC]
    congr 1
    unfold gammaB
    ring
  have hC : gammaA nu mu s + gammaB nu mu s - gammaD nu mu s = mellinParameter nu mu s := by
    unfold gammaA gammaB gammaD
    ring
  unfold reducedSchwingerDensity gammaBetaKernel
  rw [schwingerCoefficient_eq_actual nu mu ht hu, he, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (mul_pos ht hu).le (add_pos ht hu).le,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ht.le hu.le, hC]
  calc
    _ = (Real.exp (-t - u) : ℂ) *
        ((t : ℂ) ^ (nu - 1) * (t : ℂ) ^ mellinParameter nu mu s) *
        ((u : ℂ) ^ (mu - 1) * (u : ℂ) ^ mellinParameter nu mu s) /
        ((t + u : ℝ) : ℂ) ^ mellinParameter nu mu s := by ring
    _ = _ := by rw [htP, huP]

theorem reducedSchwingerDensity_integral {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) :
    (∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      reducedSchwingerDensity nu mu s p.1 p.2) =
      Complex.Gamma (gammaD nu mu s) *
        (Complex.Gamma (gammaB nu mu s) * Complex.Gamma (gammaA nu mu s) / Complex.Gamma s) := by
  have hB : Integrable (fun p : ℝ × ℝ =>
      gammaBetaKernel (gammaA nu mu s) (gammaB nu mu s) (gammaD nu mu s) p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
    apply (reducedSchwingerDensity_integrable hs).congr
    filter_upwards [positive_pairs_ae] with p hp
    exact reducedSchwingerDensity_eq_betaKernel nu mu s hp.1 hp.2
  have he : (∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      reducedSchwingerDensity nu mu s p.1 p.2) =
      ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        gammaBetaKernel (gammaA nu mu s) (gammaB nu mu s) (gammaD nu mu s) p.1 p.2 := by
    apply integral_congr_ae
    filter_upwards [positive_pairs_ae] with p hp
    exact reducedSchwingerDensity_eq_betaKernel nu mu s hp.1 hp.2
  have hp := gamma_parameters_positive hs
  have hsum : gammaB nu mu s + gammaA nu mu s = s := by
    unfold gammaA gammaB mellinParameter
    ring
  rw [he, integral_prod _ hB, gammaBetaKernel_iterated_integral hp.1 hp.2.1 hp.2.2, hsum]

theorem actualSchwingerProduct_integral_four_gamma {nu mu s : ℂ}
    (hs : |nu.re| + |mu.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), actualSchwingerProduct nu mu s x) =
      Complex.Gamma (mellinParameter nu mu s) * Complex.Gamma (gammaD nu mu s) *
        Complex.Gamma (gammaB nu mu s) * Complex.Gamma (gammaA nu mu s) / Complex.Gamma s := by
  rw [actualSchwingerProduct_integral_reduction hs, reducedSchwingerDensity_integral hs]
  ring

end
end ImbalancedChen.Part3.ComplexTwoKSchwingerProduct20261025a
