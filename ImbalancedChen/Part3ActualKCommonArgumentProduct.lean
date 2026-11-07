import ImbalancedChen.Part3ComplexOrderKPositiveLaplace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual K product at a common positive real argument, for arbitrary complex
orders. Starting with the proved literal full-line tilted K integral, the
affine changes v = 2*s-u and u = s+t give the full-line product kernel.
Their joint absolute integrability is derived before either Fubini swap.
Reflection then gives the positive-half-line cosh kernel. This is the
positive-real-argument case of DLMF 10.32.17; no product formula is an input.

Primary reference checked 2026-10-26: https://dlmf.nist.gov/10.32.E17,
whose printed domain is |ph z| < pi/2 with arbitrary complex orders.
The different, unequal-argument Macdonald formula 10.32.18 has printed
domain |ph z| < pi, |ph zeta| < pi, |ph(z+zeta)| < pi/4. It is NOT proved
or assumed here. This module does not identify an automorphic Bessel
transform, orbital integral, Weber formula, or spectral normalization.
-/

namespace ImbalancedChen.Part3.ActualKCommonArgumentProduct20261026a

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a

/-- The exact one-dimensional affine fiber Jacobian. -/
theorem affineFiber_integral (f : ℝ × ℝ → ℂ) (a : ℝ → ℝ) (b x : ℝ) :
    (∫ y : ℝ, f (x, b * y + a x)) = |b⁻¹| • ∫ y : ℝ, f (x, y) := by
  rw [Measure.integral_comp_mul_left (fun y => f (x, y + a x)) b,
    integral_add_right_eq_self]

/-- Absolute integrability under an affine fiber change. The first
coordinate is fixed, so the input fiber is `prod_right_ae`. -/
theorem affineFiber_integrable (f : ℝ × ℝ → ℂ) (hfcont : Continuous f)
    (hf : Integrable f (volume.prod volume)) (a : ℝ → ℝ)
    (ha : Continuous a) {b : ℝ} (hb : b ≠ 0) :
    Integrable (fun p : ℝ × ℝ => f (p.1, b * p.2 + a p.1))
      (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ => f (p.1, b * p.2 + a p.1)) := by
    fun_prop
  apply (integrable_prod_iff hcont.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hf.prod_right_ae] with x hx
    exact (hx.comp_add_right (a x)).comp_mul_left' hb
  · apply (hf.integral_norm_prod_left.const_mul |b⁻¹|).congr
    exact Eventually.of_forall fun x => by
      have hscale := Measure.integral_comp_mul_left
        (fun y : ℝ => ‖f (x, y + a x)‖) b
      rw [integral_add_right_eq_self, smul_eq_mul] at hscale
      exact hscale.symm

def rawProduct (nu mu : ℂ) (q : ℝ) (u v : ℝ) : ℂ :=
  tiltedDensity nu q u * tiltedDensity mu q v

theorem rawProduct_continuous (nu mu : ℂ) (q : ℝ) :
    Continuous (fun p : ℝ × ℝ => rawProduct nu mu q p.1 p.2) := by
  unfold rawProduct tiltedDensity
  fun_prop

theorem rawProduct_integrable (nu mu : ℂ) {q : ℝ} (hq : 0 < q) :
    Integrable (fun p : ℝ × ℝ => rawProduct nu mu q p.1 p.2)
      (volume.prod volume) :=
  (tiltedDensity_integrable nu hq).mul_prod (tiltedDensity_integrable mu hq)

def halfShear (nu mu : ℂ) (q : ℝ) (u s : ℝ) : ℂ :=
  rawProduct nu mu q u (2 * s - u)

theorem halfShear_continuous (nu mu : ℂ) (q : ℝ) :
    Continuous (fun p : ℝ × ℝ => halfShear nu mu q p.1 p.2) := by
  unfold halfShear rawProduct tiltedDensity
  fun_prop

theorem halfShear_integrable (nu mu : ℂ) {q : ℝ} (hq : 0 < q) :
    Integrable (fun p : ℝ × ℝ => halfShear nu mu q p.1 p.2)
      (volume.prod volume) := by
  simpa only [halfShear, sub_eq_add_neg] using
    affineFiber_integrable (fun p => rawProduct nu mu q p.1 p.2)
      (rawProduct_continuous nu mu q) (rawProduct_integrable nu mu hq)
      (fun u : ℝ => -u) (by fun_prop) (by norm_num : (2 : ℝ) ≠ 0)

theorem halfShear_fiber (nu mu : ℂ) (q u : ℝ) :
    (∫ s : ℝ, halfShear nu mu q u s) =
      (1 / 2 : ℂ) * ∫ v : ℝ, rawProduct nu mu q u v := by
  have h := affineFiber_integral (fun p => rawProduct nu mu q p.1 p.2)
    (fun u : ℝ => -u) 2 u
  simpa [halfShear, sub_eq_add_neg, Complex.real_smul] using h

def centeredProduct (nu mu : ℂ) (q : ℝ) (s t : ℝ) : ℂ :=
  rawProduct nu mu q (s + t) (s - t)

theorem centeredProduct_integrable (nu mu : ℂ) {q : ℝ} (hq : 0 < q) :
    Integrable (fun p : ℝ × ℝ => centeredProduct nu mu q p.1 p.2)
      (volume.prod volume) := by
  have hswap := (halfShear_integrable nu mu hq).swap
  have hc : Continuous (fun p : ℝ × ℝ => halfShear nu mu q p.2 p.1) := by
    exact (halfShear_continuous nu mu q).comp continuous_swap
  have h := affineFiber_integrable (fun p => halfShear nu mu q p.2 p.1)
    hc hswap (fun s : ℝ => s) continuous_id (by norm_num : (1 : ℝ) ≠ 0)
  apply h.congr
  exact Eventually.of_forall fun p => by
    unfold halfShear centeredProduct
    congr 1 <;> ring

/-- The hyperbolic addition identity inside the actual, absolutely
integrable product. The orders are independent complex numbers. -/
theorem centeredProduct_factor (nu mu : ℂ) (q s t : ℝ) :
    centeredProduct nu mu q s t =
      Complex.exp ((nu - mu) * (t : ℂ)) *
        tiltedDensity (nu + mu) (2 * q * Real.cosh t) s := by
  unfold centeredProduct rawProduct tiltedDensity
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [Real.cosh_add, Real.cosh_sub]
  push_cast
  ring

def weightedKernel (nu mu : ℂ) (q t : ℝ) : ℂ :=
  Complex.exp ((nu - mu) * (t : ℂ)) *
    complexOrderK (nu + mu) (2 * q * Real.cosh t)

theorem centeredProduct_fiber (nu mu : ℂ) {q : ℝ} (hq : 0 < q) (t : ℝ) :
    (∫ s : ℝ, centeredProduct nu mu q s t) = 2 * weightedKernel nu mu q t := by
  have harg : 0 < 2 * q * Real.cosh t :=
    mul_pos (mul_pos (by norm_num) hq) (Real.cosh_pos t)
  simp_rw [centeredProduct_factor]
  rw [integral_const_mul, tiltedDensity_integral (nu + mu) harg]
  unfold weightedKernel
  ring

/-- Absolute convergence of the surviving full-line actual K kernel;
it follows from joint L1, rather than being an input hypothesis. -/
theorem weightedKernel_integrable (nu mu : ℂ) {q : ℝ} (hq : 0 < q) :
    Integrable (weightedKernel nu mu q) := by
  have h := (centeredProduct_integrable nu mu hq).integral_prod_right
  apply (h.const_mul (1 / 2 : ℂ)).congr
  exact Eventually.of_forall fun t => by
    rw [centeredProduct_fiber nu mu hq]
    ring

/-- Exact full-line product integral of the literal K source. -/
theorem actual_K_product_full_line (nu mu : ℂ) {q : ℝ} (hq : 0 < q) :
    complexOrderK nu q * complexOrderK mu q =
      ∫ t : ℝ, weightedKernel nu mu q t := by
  have hcenter := centeredProduct_integrable nu mu hq
  have hhalf := halfShear_integrable nu mu hq
  have htotal : (∫ s : ℝ, ∫ t : ℝ, centeredProduct nu mu q s t) =
      2 * (complexOrderK nu q * complexOrderK mu q) := by
    calc
      _ = ∫ s : ℝ, ∫ t : ℝ, halfShear nu mu q (t + s) s := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s => integral_congr_ae
          (Eventually.of_forall fun t => by
            unfold centeredProduct halfShear
            congr 1 <;> ring)
      _ = ∫ s : ℝ, ∫ u : ℝ, halfShear nu mu q u s := by
        apply integral_congr_ae
        exact Eventually.of_forall fun s =>
          integral_add_right_eq_self (fun u => halfShear nu mu q u s) s
      _ = ∫ u : ℝ, ∫ s : ℝ, halfShear nu mu q u s :=
        integral_integral_swap hhalf.swap
      _ = (1 / 2 : ℂ) * ∫ u : ℝ, ∫ v : ℝ, rawProduct nu mu q u v := by
        simp_rw [halfShear_fiber]
        rw [integral_const_mul]
      _ = _ := by
        unfold rawProduct
        simp_rw [integral_const_mul, integral_mul_const,
          tiltedDensity_integral nu hq, tiltedDensity_integral mu hq]
        ring
  have heval : (∫ s : ℝ, ∫ t : ℝ, centeredProduct nu mu q s t) =
      2 * ∫ t : ℝ, weightedKernel nu mu q t := by
    rw [integral_integral_swap hcenter]
    simp_rw [centeredProduct_fiber nu mu hq]
    rw [integral_const_mul]
  calc
    _ = (1 / 2 : ℂ) * (2 * (complexOrderK nu q * complexOrderK mu q)) := by ring
    _ = _ := by rw [← htotal, heval]; ring

def coshKernel (nu mu : ℂ) (q t : ℝ) : ℂ :=
  complexOrderK (nu + mu) (2 * q * Real.cosh t) *
    Complex.cosh ((nu - mu) * (t : ℂ))

theorem weightedKernel_pair (nu mu : ℂ) (q t : ℝ) :
    weightedKernel nu mu q (-t) + weightedKernel nu mu q t =
      2 * coshKernel nu mu q t := by
  unfold weightedKernel coshKernel
  rw [Real.cosh_neg, Complex.ofReal_neg, mul_neg, Complex.cosh]
  ring

/-- Absolute convergence of the actual half-line product transform. -/
theorem coshKernel_integrable (nu mu : ℂ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (coshKernel nu mu q) (Ioi 0) := by
  have h := weightedKernel_integrable nu mu hq
  have hp := (h.comp_neg.add h).const_mul (1 / 2 : ℂ)
  apply (hp.congr (Eventually.of_forall fun t => by
    rw [weightedKernel_pair]
    ring)).integrableOn

/-- DLMF 10.32.17 at a common positive real argument, derived from actual
K. No restriction is imposed on the two complex orders. -/
theorem actual_K_product_cosh (nu mu : ℂ) {q : ℝ} (hq : 0 < q) :
    complexOrderK nu q * complexOrderK mu q =
      2 * ∫ t in Ioi (0 : ℝ),
        complexOrderK (nu + mu) (2 * q * Real.cosh t) *
          Complex.cosh ((nu - mu) * (t : ℂ)) := by
  have h := weightedKernel_integrable nu mu hq
  rw [actual_K_product_full_line nu mu hq]
  calc
    _ = (∫ t in Iic (0 : ℝ), weightedKernel nu mu q t) +
        ∫ t in Ioi (0 : ℝ), weightedKernel nu mu q t :=
      (intervalIntegral.integral_Iic_add_Ioi h.integrableOn h.integrableOn).symm
    _ = (∫ t in Ioi (0 : ℝ), weightedKernel nu mu q (-t)) +
        ∫ t in Ioi (0 : ℝ), weightedKernel nu mu q t := by
      congr 1
      simpa only [neg_zero] using
        (integral_comp_neg_Ioi (0 : ℝ) (weightedKernel nu mu q)).symm
    _ = ∫ t in Ioi (0 : ℝ),
        (weightedKernel nu mu q (-t) + weightedKernel nu mu q t) :=
      (integral_add h.comp_neg.integrableOn h.integrableOn).symm
    _ = _ := by
      simp_rw [weightedKernel_pair]
      rw [integral_const_mul]
      rfl

end
end ImbalancedChen.Part3.ActualKCommonArgumentProduct20261026a
