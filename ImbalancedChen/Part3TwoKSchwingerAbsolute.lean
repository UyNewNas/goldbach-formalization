import ImbalancedChen.Part3ComplexOrderKPositiveLaplace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Absolute convergence of the actual two-K Schwinger fiber

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
For imaginary orders i*tau,i*sigma and real s>0 the Schwinger variable
x=q^2/4 has exponent zeta=(s-i*tau-i*sigma)/2. The full three-variable
fiber is absolutely integrable. Its x integration is evaluated by the
pinned complex Gamma-Laplace theorem, leaving an explicit double integral.
The exact dictionary to the actual dampedGammaDensity is proved below.
The remaining Beta evaluation and the q-Mellin change of variables are
not claimed here; nor is any KL orthogonality or spectral formula.
-/

namespace ImbalancedChen.Part3.TwoKSchwingerAbsolute20261025a

noncomputable section
open Set MeasureTheory Filter Complex
open ComplexOrderKPositiveLaplace20261025a

abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

def reciprocalSum (t u : ℝ) : ℝ := t⁻¹ + u⁻¹
def positiveWeight (t u : ℝ) : ℝ := Real.exp (-t - u) / (t * u)

def positiveFiber (c t u x : ℝ) : ℝ :=
  Real.exp (Real.log x * (c - 1)) * Real.exp (-(reciprocalSum t u * x)) *
    positiveWeight t u

def gammaEnvelope (c t : ℝ) : ℝ := Real.exp (-t) * t ^ (c / 2 - 1)

theorem reciprocalSum_pos {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    0 < reciprocalSum t u := add_pos (inv_pos.mpr ht) (inv_pos.mpr hu)

private theorem positive_pairs_ae :
    ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure, 0 < p.1 ∧ 0 < p.2 := by
  apply (ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact ⟨ht, hu⟩

theorem reciprocalSum_inv_le_sqrt {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    1 / reciprocalSum t u ≤ Real.sqrt (t * u) := by
  have he : 1 / reciprocalSum t u = t * u / (t + u) := by
    unfold reciprocalSum
    field_simp [ht.ne', hu.ne', (add_pos ht hu).ne'] <;> ring
  rw [he]
  have hw : 0 ≤ Real.sqrt (t * u) := Real.sqrt_nonneg _
  have hw2 : Real.sqrt (t * u) ^ 2 = t * u := Real.sq_sqrt (mul_pos ht hu).le
  have hsum : 2 * Real.sqrt (t * u) ≤ t + u := by
    nlinarith [sq_nonneg (t - u)]
  apply (div_le_iff₀ (add_pos ht hu)).mpr
  nlinarith [mul_nonneg hw (sub_nonneg.mpr hsum)]

theorem positiveWeight_mul_rpow_le {c t u : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hu : 0 < u) :
    positiveWeight t u * (1 / reciprocalSum t u) ^ c ≤
      gammaEnvelope c t * gammaEnvelope c u := by
  have hbase : 0 ≤ 1 / reciprocalSum t u := by
    exact (one_div_pos.mpr (reciprocalSum_pos ht hu)).le
  have hp := Real.rpow_le_rpow hbase (reciprocalSum_inv_le_sqrt ht hu) hc.le
  have hpow : (Real.sqrt (t * u)) ^ c = t ^ (c / 2) * u ^ (c / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_pos ht hu).le]
    have he : (1 / 2 : ℝ) * c = c / 2 := by ring
    rw [he, Real.mul_rpow ht.le hu.le]
  rw [hpow] at hp
  have hwt : 0 ≤ positiveWeight t u := by unfold positiveWeight; positivity
  have htP : t ^ (c / 2 - 1) = t ^ (c / 2) / t := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  have huP : u ^ (c / 2 - 1) = u ^ (c / 2) / u := by
    rw [Real.rpow_sub hu, Real.rpow_one]
  calc
    _ ≤ positiveWeight t u * (t ^ (c / 2) * u ^ (c / 2)) :=
      mul_le_mul_of_nonneg_left hp hwt
    _ = _ := by
      unfold positiveWeight gammaEnvelope
      rw [htP, huP, show -t - u = -t + -u by ring, Real.exp_add]
      ring

theorem positiveFiber_integrable {c t u : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hu : 0 < u) : IntegrableOn (positiveFiber c t u) (Ioi 0) := by
  have hb := reciprocalSum_pos ht hu
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ (c - 1) * Real.exp (-(reciprocalSum t u * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := c - 1)
        (b := reciprocalSum t u) (by linarith) le_rfl hb
  apply (hbase.mul_const (positiveWeight t u)).congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [positiveFiber, Real.rpow_def_of_pos hx]

theorem positiveFiber_integral {c t u : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hu : 0 < u) :
    (∫ x in Ioi (0 : ℝ), positiveFiber c t u x) =
      positiveWeight t u * (1 / reciprocalSum t u) ^ c * Real.Gamma c := by
  have he : (∫ x in Ioi (0 : ℝ), positiveFiber c t u x) =
      ∫ x in Ioi (0 : ℝ), (x ^ (c - 1) *
        Real.exp (-(reciprocalSum t u * x))) * positiveWeight t u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [positiveFiber, Real.rpow_def_of_pos hx]
  rw [he, integral_mul_const,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hc (reciprocalSum_pos ht hu)]
  ring

/-- A genuine triple absolute-convergence certificate; c may be arbitrarily
small and positive, so there is no hidden positive Mellin cutoff. -/
theorem positiveFiber_joint_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => positiveFiber c p.1.1 p.1.2 p.2)
      ((positiveMeasure.prod positiveMeasure).prod positiveMeasure) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ => positiveFiber c p.1.1 p.1.2 p.2) := by
    unfold positiveFiber positiveWeight reciprocalSum
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [positive_pairs_ae] with p hp
    exact positiveFiber_integrable hc hp.1 hp.2
  · have hg : Integrable (gammaEnvelope c) positiveMeasure :=
      Real.GammaIntegral_convergent (half_pos hc)
    have henv := (hg.mul_prod hg).mul_const (Real.Gamma c)
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ∫ x in Ioi (0 : ℝ), ‖positiveFiber c p.1 p.2 x‖)
        (positiveMeasure.prod positiveMeasure) :=
      hm.aestronglyMeasurable.norm.integral_prod_right'
    apply henv.mono' hmeas
    filter_upwards [positive_pairs_ae] with p hp
    have ht : 0 < p.1 := hp.1
    have hu : 0 < p.2 := hp.2
    have hb : 0 < reciprocalSum p.1 p.2 := reciprocalSum_pos ht hu
    have he : (∫ x in Ioi (0 : ℝ), ‖positiveFiber c p.1 p.2 x‖) =
        positiveWeight p.1 p.2 * (1 / reciprocalSum p.1 p.2) ^ c * Real.Gamma c := by
      rw [← positiveFiber_integral hc hp.1 hp.2]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        unfold positiveFiber positiveWeight
        positivity
    rw [he, Real.norm_eq_abs, abs_of_nonneg (by
      unfold positiveWeight
      positivity)]
    exact mul_le_mul_of_nonneg_right (positiveWeight_mul_rpow_le hc hp.1 hp.2)
      (Real.Gamma_pos_of_pos hc).le

def mellinParameter (tau sigma s : ℝ) : ℂ :=
  ((s : ℂ) - (tau : ℂ) * I - (sigma : ℂ) * I) / 2

theorem mellinParameter_re (tau sigma s : ℝ) :
    (mellinParameter tau sigma s).re = s / 2 := by
  simp [mellinParameter, div_eq_mul_inv]

def schwingerCoefficient (tau sigma t u : ℝ) : ℂ :=
  Complex.exp ((Real.log t : ℂ) * ((tau : ℂ) * I - 1)) *
    Complex.exp ((Real.log u : ℂ) * ((sigma : ℂ) * I - 1)) *
    (Real.exp (-t - u) : ℂ)

def schwingerFiber (tau sigma s t u x : ℝ) : ℂ :=
  Complex.exp ((Real.log x : ℂ) * (mellinParameter tau sigma s - 1)) *
    (Real.exp (-(reciprocalSum t u * x)) : ℂ) * schwingerCoefficient tau sigma t u

def reducedSchwingerDensity (tau sigma s t u : ℝ) : ℂ :=
  schwingerCoefficient tau sigma t u *
    ((1 / reciprocalSum t u : ℝ) : ℂ) ^ mellinParameter tau sigma s

theorem norm_schwingerCoefficient (tau sigma : ℝ) {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) :
    ‖schwingerCoefficient tau sigma t u‖ = positiveWeight t u := by
  simp only [schwingerCoefficient, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, zero_mul, mul_zero, sub_zero, zero_sub, mul_neg_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Real.exp_neg, Real.exp_log ht, Real.exp_neg, Real.exp_log hu]
  unfold positiveWeight
  ring

theorem norm_schwingerFiber (tau sigma s x : ℝ) {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) :
    ‖schwingerFiber tau sigma s t u x‖ = positiveFiber (s / 2) t u x := by
  rw [schwingerFiber, norm_mul, norm_mul, norm_schwingerCoefficient tau sigma ht hu]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, Complex.one_re,
    mellinParameter_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), positiveFiber]

/-- Absolute convergence of the actual imaginary-order Schwinger fiber.
No product identity is an input. -/
theorem schwingerFiber_joint_integrable (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => schwingerFiber tau sigma s p.1.1 p.1.2 p.2)
      ((positiveMeasure.prod positiveMeasure).prod positiveMeasure) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      schwingerFiber tau sigma s p.1.1 p.1.2 p.2) := by
    unfold schwingerFiber schwingerCoefficient reciprocalSum
    fun_prop
  apply (positiveFiber_joint_integrable (half_pos hs)).mono' hm.aestronglyMeasurable
  have hp : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂
      ((positiveMeasure.prod positiveMeasure).prod positiveMeasure),
      0 < p.1.1 ∧ 0 < p.1.2 := by
    apply (ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [positive_pairs_ae] with p hp
    exact ae_of_all _ fun _ => hp
  filter_upwards [hp] with p hp
  exact (norm_schwingerFiber tau sigma s p.2 hp.1 hp.2).le

theorem schwingerFiber_integral_x (tau sigma : ℝ) {s t u : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hu : 0 < u) :
    (∫ x in Ioi (0 : ℝ), schwingerFiber tau sigma s t u x) =
      Complex.Gamma (mellinParameter tau sigma s) * reducedSchwingerDensity tau sigma s t u := by
  have he : (∫ x in Ioi (0 : ℝ), schwingerFiber tau sigma s t u x) =
      ∫ x in Ioi (0 : ℝ), ((x : ℂ) ^ (mellinParameter tau sigma s - 1) *
        Complex.exp (-((reciprocalSum t u : ℂ) * (x : ℂ)))) *
          schwingerCoefficient tau sigma t u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [schwingerFiber, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le, Complex.ofReal_exp]
    push_cast
    rfl
  rw [he, integral_mul_const, Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (by rw [mellinParameter_re]; exact half_pos hs) (reciprocalSum_pos ht hu)]
  unfold reducedSchwingerDensity
  push_cast
  ring

theorem reducedSchwingerDensity_integrable (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => reducedSchwingerDensity tau sigma s p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hgamma : Complex.Gamma (mellinParameter tau sigma s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [mellinParameter_re]; exact half_pos hs)
  have h := ((schwingerFiber_joint_integrable tau sigma hs).integral_prod_left).const_mul
    (Complex.Gamma (mellinParameter tau sigma s))⁻¹
  apply h.congr
  filter_upwards [positive_pairs_ae] with p hp
  rw [schwingerFiber_integral_x tau sigma hs hp.1 hp.2]
  simp only [← mul_assoc, inv_mul_cancel₀ hgamma, one_mul]

/-- Exact Fubini reduction to an explicit double Schwinger integral. The
remaining Beta evaluation is deliberately not asserted as an assumption. -/
theorem schwinger_integral_reduction (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      schwingerFiber tau sigma s p.1 p.2 x) =
    Complex.Gamma (mellinParameter tau sigma s) *
      ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        reducedSchwingerDensity tau sigma s p.1 p.2 := by
  rw [← integral_integral_swap (schwingerFiber_joint_integrable tau sigma hs),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [positive_pairs_ae] with p hp
  exact schwingerFiber_integral_x tau sigma hs hp.1 hp.2

/-- Literal dictionary: these are the two actual damped Gamma densities
at x=q^2/4, not unrelated auxiliary kernels. -/
theorem schwingerFiber_eq_actual (tau sigma s : ℝ) {q t u : ℝ}
    (hq : 0 < q) (ht : 0 < t) (hu : 0 < u) :
    schwingerFiber tau sigma s t u (q ^ 2 / 4) =
      ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter tau sigma s - 1) *
        dampedGammaDensity ((tau : ℂ) * I) q t *
        dampedGammaDensity ((sigma : ℂ) * I) q u := by
  have hx : 0 < q ^ 2 / 4 := by positivity
  have hexp : -(reciprocalSum t u * (q ^ 2 / 4)) + (-t - u) =
      -t - q ^ 2 / (4 * t) + (-u - q ^ 2 / (4 * u)) := by
    unfold reciprocalSum
    field_simp [ht.ne', hu.ne'] <;> ring
  simp only [schwingerFiber, schwingerCoefficient, dampedGammaDensity,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log ht.le, ← Complex.ofReal_log hu.le]
  have he : (Real.exp (-(reciprocalSum t u * (q ^ 2 / 4))) : ℂ) *
      (Real.exp (-t - u) : ℂ) =
      (Real.exp (-t) : ℂ) * (Real.exp (-(q ^ 2 / (4 * t))) : ℂ) *
        ((Real.exp (-u) : ℂ) * (Real.exp (-(q ^ 2 / (4 * u))) : ℂ)) := by
    norm_cast
    simp only [← Real.exp_add]
    congr 1
    exact hexp
  calc
    _ = Complex.exp ((Real.log (q ^ 2 / 4) : ℂ) * (mellinParameter tau sigma s - 1)) *
        Complex.exp ((Real.log t : ℂ) * ((tau : ℂ) * I - 1)) *
        Complex.exp ((Real.log u : ℂ) * ((sigma : ℂ) * I - 1)) *
        ((Real.exp (-(reciprocalSum t u * (q ^ 2 / 4))) : ℂ) *
          (Real.exp (-t - u) : ℂ)) := by ring
    _ = _ := by rw [he]; ring

/-- Integrating the two Schwinger variables produces precisely the product
of the two actual K integrals, with all positive-base power factors kept. -/
theorem schwingerFiber_pair_integral_at_q (tau sigma s : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      schwingerFiber tau sigma s p.1 p.2 (q ^ 2 / 4)) =
      ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter tau sigma s - 1) *
        (2 * ((q / 2 : ℝ) : ℂ) ^ ((tau : ℂ) * I) *
          ComplexOrderKBridgeSourceOnly.complexOrderK ((tau : ℂ) * I) q) *
        (2 * ((q / 2 : ℝ) : ℂ) ^ ((sigma : ℂ) * I) *
          ComplexOrderKBridgeSourceOnly.complexOrderK ((sigma : ℂ) * I) q) := by
  calc
    _ = ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ((q ^ 2 / 4 : ℝ) : ℂ) ^ (mellinParameter tau sigma s - 1) *
          (dampedGammaDensity ((tau : ℂ) * I) q p.1 *
            dampedGammaDensity ((sigma : ℂ) * I) q p.2) := by
      apply integral_congr_ae
      filter_upwards [positive_pairs_ae] with p hp
      rw [schwingerFiber_eq_actual tau sigma s hq hp.1 hp.2]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_prod_mul,
        dampedGammaDensity_integral ((tau : ℂ) * I) hq,
        dampedGammaDensity_integral ((sigma : ℂ) * I) hq]
      ring

/-- Actual product integrand in the squared Mellin coordinate x=q^2/4.
This definition deliberately preserves the Schwinger normalization. -/
def actualSchwingerProduct (tau sigma s x : ℝ) : ℂ :=
  (x : ℂ) ^ (mellinParameter tau sigma s - 1) *
    (2 * (Real.sqrt x : ℂ) ^ ((tau : ℂ) * I) *
      ComplexOrderKBridgeSourceOnly.complexOrderK ((tau : ℂ) * I) (2 * Real.sqrt x)) *
    (2 * (Real.sqrt x : ℂ) ^ ((sigma : ℂ) * I) *
      ComplexOrderKBridgeSourceOnly.complexOrderK ((sigma : ℂ) * I) (2 * Real.sqrt x))

theorem schwingerFiber_pair_integral (tau sigma s : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      schwingerFiber tau sigma s p.1 p.2 x) = actualSchwingerProduct tau sigma s x := by
  have hq : 0 < 2 * Real.sqrt x := mul_pos (by norm_num) (Real.sqrt_pos.mpr hx)
  have hxq : (2 * Real.sqrt x) ^ 2 / 4 = x := by
    nlinarith [Real.sq_sqrt hx.le]
  have hhalf : (2 * Real.sqrt x) / 2 = Real.sqrt x := by ring
  simpa only [hxq, hhalf, actualSchwingerProduct] using
    schwingerFiber_pair_integral_at_q tau sigma s hq

/-- Absolute convergence is for the actual two-K product, not just for an
auxiliary three-variable kernel. -/
theorem actualSchwingerProduct_integrable (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (actualSchwingerProduct tau sigma s) (Ioi 0) := by
  have h := (schwingerFiber_joint_integrable tau sigma hs).integral_prod_right
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact schwingerFiber_pair_integral tau sigma s hx

/-- An unconditional reduced integral for the literal two-K product. The
remaining double density is absolutely integrable by the theorem above. -/
theorem actualSchwingerProduct_integral_reduction (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), actualSchwingerProduct tau sigma s x) =
      Complex.Gamma (mellinParameter tau sigma s) *
        ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
          reducedSchwingerDensity tau sigma s p.1 p.2 := by
  rw [← schwinger_integral_reduction tau sigma hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schwingerFiber_pair_integral tau sigma s hx).symm

def schwingerBetaKernel (tau sigma s t u : ℝ) : ℂ :=
  (Real.exp (-t - u) : ℂ) *
    (t : ℂ) ^ ((tau : ℂ) * I + mellinParameter tau sigma s - 1) *
    (u : ℂ) ^ ((sigma : ℂ) * I + mellinParameter tau sigma s - 1) /
    ((t + u : ℝ) : ℂ) ^ mellinParameter tau sigma s

/-- The reduced Schwinger density is precisely the Gamma-Beta double
density. All cpow divisions use strictly positive real bases. -/
theorem reducedSchwingerDensity_eq_betaKernel (tau sigma s : ℝ) {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) :
    reducedSchwingerDensity tau sigma s t u = schwingerBetaKernel tau sigma s t u := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have he : 1 / reciprocalSum t u = t * u / (t + u) := by
    unfold reciprocalSum
    field_simp [ht.ne', hu.ne', (add_pos ht hu).ne'] <;> ring
  have htP : (t : ℂ) ^ ((tau : ℂ) * I - 1) *
      (t : ℂ) ^ mellinParameter tau sigma s =
      (t : ℂ) ^ ((tau : ℂ) * I + mellinParameter tau sigma s - 1) := by
    rw [← Complex.cpow_add _ _ htC]
    congr 1
    ring
  have huP : (u : ℂ) ^ ((sigma : ℂ) * I - 1) *
      (u : ℂ) ^ mellinParameter tau sigma s =
      (u : ℂ) ^ ((sigma : ℂ) * I + mellinParameter tau sigma s - 1) := by
    rw [← Complex.cpow_add _ _ huC]
    congr 1
    ring
  have hcoef : schwingerCoefficient tau sigma t u =
      (t : ℂ) ^ ((tau : ℂ) * I - 1) *
        (u : ℂ) ^ ((sigma : ℂ) * I - 1) * (Real.exp (-t - u) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero htC, Complex.cpow_def_of_ne_zero huC,
      ← Complex.ofReal_log ht.le, ← Complex.ofReal_log hu.le]
    rfl
  unfold reducedSchwingerDensity schwingerBetaKernel
  rw [hcoef, he, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (mul_pos ht hu).le (add_pos ht hu).le,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ht.le hu.le]
  calc
    _ = (Real.exp (-t - u) : ℂ) *
        ((t : ℂ) ^ ((tau : ℂ) * I - 1) * (t : ℂ) ^ mellinParameter tau sigma s) *
        ((u : ℂ) ^ ((sigma : ℂ) * I - 1) * (u : ℂ) ^ mellinParameter tau sigma s) /
        ((t + u : ℝ) : ℂ) ^ mellinParameter tau sigma s := by ring
    _ = _ := by rw [htP, huP]

theorem schwingerBetaKernel_integrable (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => schwingerBetaKernel tau sigma s p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  apply (reducedSchwingerDensity_integrable tau sigma hs).congr
  filter_upwards [positive_pairs_ae] with p hp
  exact reducedSchwingerDensity_eq_betaKernel tau sigma s hp.1 hp.2

/-- The bounded milestone: a genuine absolutely convergent reduced Beta
integral for the actual product, before evaluating that Beta integral. -/
theorem actualSchwingerProduct_integral_eq_beta_reduction (tau sigma : ℝ)
    {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), actualSchwingerProduct tau sigma s x) =
      Complex.Gamma (mellinParameter tau sigma s) *
        ∫ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
          schwingerBetaKernel tau sigma s p.1 p.2 := by
  rw [actualSchwingerProduct_integral_reduction tau sigma hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [positive_pairs_ae] with p hp
  exact reducedSchwingerDensity_eq_betaKernel tau sigma s hp.1 hp.2

end
end ImbalancedChen.Part3.TwoKSchwingerAbsolute20261025a
