import ImbalancedChen.Part3ActualKUnequalKZeroRatio
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual absolutely convergent K_0 ratio product is transported by
r=exp(v) from the positive axis to the whole real line. Its Jacobian
is exp(v), and its power becomes exp(-nu*v). The ratio distance becomes
sqrt(x^2+y^2+2*x*y*cosh(v)) by a proved real identity. Reflection then
gives the positive cosh-distance formula, for arbitrary complex nu and
independently positive x,y. No product or Weber formula is assumed.

This K_0 distance representation does not prove the different Macdonald
dt/t representation DLMF 10.32.18 or its complex-argument domain. Those
remain OPEN, as do orbital identification and automorphic normalization.
-/

namespace ImbalancedChen.Part3.ActualKUnequalHyperbolicDistance20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualKUnequalKZeroRatio20261026b

def hyperbolicDistance (x y v : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2 + 2 * x * y * Real.cosh v)

/-- The actual positive ratio-to-hyperbolic distance change. -/
theorem radialDistance_exp (x y v : ℝ) :
    radialDistance x y (Real.exp v) = hyperbolicDistance x y v := by
  rw [radialDistance_eq_sqrt x y (Real.exp_pos v)]
  unfold hyperbolicDistance
  congr 1
  rw [Real.cosh_eq, Real.exp_neg]
  ring

theorem hyperbolicDistance_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : ℝ) :
    0 < hyperbolicDistance x y v := by
  rw [← radialDistance_exp]
  exact radialDistance_pos hx hy (Real.exp_pos v)

theorem hyperbolicDistance_neg (x y v : ℝ) :
    hyperbolicDistance x y (-v) = hyperbolicDistance x y v := by
  simp only [hyperbolicDistance, Real.cosh_neg]

def weightedDistanceKernel (nu : ℂ) (x y v : ℝ) : ℂ :=
  Complex.exp (-nu * (v : ℂ)) * complexOrderK 0 (hyperbolicDistance x y v)

/-- The true exponential Jacobian changes r^(-nu-1) dr into
exp(-nu*v) dv. All complex powers have positive real bases. -/
theorem ratioKernel_exp_jacobian (nu : ℂ) (x y v : ℝ) :
    (Real.exp v : ℂ) * ratioKernel nu x y (Real.exp v) =
      weightedDistanceKernel nu x y v := by
  have heC : (Real.exp v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
  have hlog : Complex.log (Real.exp v : ℂ) = (v : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
  have hpower : (Real.exp v : ℂ) * (Real.exp v : ℂ) ^ (-nu - 1) =
      Complex.exp (-nu * (v : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero heC, hlog, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    ring
  unfold ratioKernel weightedDistanceKernel
  rw [radialDistance_exp]
  rw [← mul_assoc, hpower]

/-- Absolute convergence is transported from the actual positive K_0
ratio transform. It is not an independent hypothesis on the final kernel. -/
theorem weightedDistanceKernel_integrable (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Integrable (weightedDistanceKernel nu x y) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := (univ : Set ℝ)) measurableSet_univ
    (fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt)
    (fun v _ w _ hvw => Real.exp_injective hvw) (ratioKernel nu x y)
  rw [image_univ, Real.range_exp, integrableOn_univ] at hchange
  have h := hchange.mp (ratioKernel_integrable nu hx hy)
  simpa only [abs_of_pos (Real.exp_pos _), Complex.real_smul,
    ratioKernel_exp_jacobian] using h

/-- The exact substitution r=exp(v), including its image and Jacobian. -/
theorem ratioKernel_integral_eq_full_line (nu : ℂ) (x y : ℝ) :
    (∫ r in Ioi (0 : ℝ), ratioKernel nu x y r) =
      ∫ v : ℝ, weightedDistanceKernel nu x y v := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := (univ : Set ℝ)) measurableSet_univ
    (fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt)
    (fun v _ w _ hvw => Real.exp_injective hvw) (ratioKernel nu x y)
  simpa only [image_univ, Real.range_exp, integral_univ,
    abs_of_pos (Real.exp_pos _), Complex.real_smul,
    ratioKernel_exp_jacobian] using hchange

/-- The genuine full-line unequal-argument K product transform. -/
theorem actual_K_unequal_distance_full_line (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    complexOrderK nu x * complexOrderK nu y =
      (1 / 2 : ℂ) * ∫ v : ℝ, weightedDistanceKernel nu x y v := by
  have hratio : complexOrderK nu x * complexOrderK nu y =
      (1 / 2 : ℂ) * ∫ r in Ioi (0 : ℝ), ratioKernel nu x y r := by
    calc
      _ = (1 / 2 : ℂ) * ∫ r in Ioi (0 : ℝ), (r : ℂ) ^ (-nu - 1) *
          complexOrderK 0 (Real.sqrt (x ^ 2 + y ^ 2 + x * y * (r + r⁻¹))) :=
        actual_K_unequal_KZero_ratio nu hx hy
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        simp only [ratioKernel, radialDistance_eq_sqrt x y hr]
  rw [hratio, ratioKernel_integral_eq_full_line]

def coshDistanceKernel (nu : ℂ) (x y v : ℝ) : ℂ :=
  complexOrderK 0 (hyperbolicDistance x y v) * Complex.cosh (nu * (v : ℂ))

theorem weightedDistanceKernel_pair (nu : ℂ) (x y v : ℝ) :
    weightedDistanceKernel nu x y (-v) + weightedDistanceKernel nu x y v =
      2 * coshDistanceKernel nu x y v := by
  unfold weightedDistanceKernel coshDistanceKernel
  rw [hyperbolicDistance_neg, Complex.ofReal_neg]
  simp only [mul_neg, neg_mul, neg_neg]
  rw [Complex.cosh]
  ring

/-- Actual absolute convergence on the positive hyperbolic coordinate. -/
theorem coshDistanceKernel_integrable (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (coshDistanceKernel nu x y) (Ioi 0) := by
  have h := weightedDistanceKernel_integrable nu hx hy
  have hp := (h.comp_neg.add h).const_mul (1 / 2 : ℂ)
  apply (hp.congr (Eventually.of_forall fun v => by
    rw [weightedDistanceKernel_pair]
    ring)).integrableOn

theorem weightedDistance_integral_eq_two_cosh (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    (∫ v : ℝ, weightedDistanceKernel nu x y v) =
      2 * ∫ v in Ioi (0 : ℝ), coshDistanceKernel nu x y v := by
  have h := weightedDistanceKernel_integrable nu hx hy
  calc
    _ = (∫ v in Iic (0 : ℝ), weightedDistanceKernel nu x y v) +
        ∫ v in Ioi (0 : ℝ), weightedDistanceKernel nu x y v :=
      (intervalIntegral.integral_Iic_add_Ioi h.integrableOn h.integrableOn).symm
    _ = (∫ v in Ioi (0 : ℝ), weightedDistanceKernel nu x y (-v)) +
        ∫ v in Ioi (0 : ℝ), weightedDistanceKernel nu x y v := by
      congr 1
      simpa only [neg_zero] using
        (integral_comp_neg_Ioi (0 : ℝ) (weightedDistanceKernel nu x y)).symm
    _ = ∫ v in Ioi (0 : ℝ),
        (weightedDistanceKernel nu x y (-v) + weightedDistanceKernel nu x y v) :=
      (integral_add h.comp_neg.integrableOn h.integrableOn).symm
    _ = _ := by
      simp_rw [weightedDistanceKernel_pair]
      rw [integral_const_mul]

/-- The literal K_0 hyperbolic-distance product formula at two independent
positive arguments, with separately proved absolute convergence. -/
theorem actual_K_unequal_hyperbolic_distance (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    complexOrderK nu x * complexOrderK nu y =
      ∫ v in Ioi (0 : ℝ),
        complexOrderK 0 (Real.sqrt (x ^ 2 + y ^ 2 + 2 * x * y * Real.cosh v)) *
          Complex.cosh (nu * (v : ℂ)) := by
  rw [actual_K_unequal_distance_full_line nu hx hy,
    weightedDistance_integral_eq_two_cosh nu hx hy]
  change (1 / 2 : ℂ) * (2 * ∫ v in Ioi (0 : ℝ), coshDistanceKernel nu x y v) =
    ∫ v in Ioi (0 : ℝ), coshDistanceKernel nu x y v
  ring

end
end ImbalancedChen.Part3.ActualKUnequalHyperbolicDistance20261026b
