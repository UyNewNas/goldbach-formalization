import ImbalancedChen.Part3ActualKZeroScaledMellin
import ImbalancedChen.Part3ActualKUnequalDistancePowerL1
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual unequal-scaled-argument K product Mellin transform, for
a,b>0 and Re(s)>2*|Re(nu)|. The K_0 distance expansion is jointly L1:
the exact scaled K_0 Mellin norm fiber is a fixed finite L1 norm times
the already proved unequal-distance power/cosh L1 density. Only after
that proof is Fubini used. Its two fibers are the actual K product and
the actual scaled K_0 Gamma Mellin integral. No final Mellin formula,
product-integrability certificate, or hypergeometric identification is
an assumption. Complex-argument sector continuation remains OPEN.
-/

namespace ImbalancedChen.Part3.ActualKUnequalScaledMellin20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualKUnequalHyperbolicDistance20261026b
open ActualKZeroScaledMellin20261026b ActualKUnequalDistancePowerL120261026b

/-- The actual product expansion in the coordinate order (v,q). -/
def unequalMellinJoint (nu s : ℂ) (a b v q : ℝ) : ℂ :=
  scaledZeroMellin s (hyperbolicDistance a b v) q * Complex.cosh (nu * (v : ℂ))

def unequalProductMellin (nu s : ℂ) (a b q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 1) * complexOrderK nu (a * q) * complexOrderK nu (b * q)

theorem unequalMellinJoint_measurable (nu s : ℂ) (a b : ℝ) :
    Measurable (fun p : ℝ × ℝ => unequalMellinJoint nu s a b p.1 p.2) := by
  have hK : Measurable (complexOrderK 0) := actualK_measurable 0
  unfold unequalMellinJoint scaledZeroMellin hyperbolicDistance
  fun_prop

/-- The exact absolute q-fiber. The base K_0 Mellin L1 norm is finite
for Re(s)>0; its unequal-distance coefficient is supplied by the prior leaf. -/
theorem unequalMellinJoint_norm_fiber (nu s : ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    (∫ q in Ioi (0 : ℝ), ‖unequalMellinJoint nu s a b v q‖) =
      (∫ u in Ioi (0 : ℝ), ‖baseZeroMellin s u‖) * distancePowerNorm nu s.re a b v := by
  simp only [unequalMellinJoint, norm_mul]
  rw [integral_mul_const, scaledZeroMellin_norm_integral s (hyperbolicDistance_pos ha hb v)]
  unfold distancePowerNorm
  ring

/-- Genuine joint L1 on the full requested strip, before either Fubini
interchange. The scales a and b need not agree. -/
theorem unequalMellinJoint_integrable {nu s : ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * |nu.re| < s.re) :
    Integrable (fun p : ℝ × ℝ => unequalMellinJoint nu s a b p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hs0 : 0 < s.re := by linarith [abs_nonneg nu.re]
  apply (integrable_prod_iff (unequalMellinJoint_measurable nu s a b).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun v =>
      (scaledZeroMellin_integrable hs0 (hyperbolicDistance_pos ha hb v)).mul_const _
  · apply ((distancePowerNorm_integrable ha hb hs).const_mul
      (∫ u in Ioi (0 : ℝ), ‖baseZeroMellin s u‖)).congr
    exact Eventually.of_forall fun v => (unequalMellinJoint_norm_fiber nu s ha hb v).symm

/-- The actual scaled K_0 Mellin fiber supplies the Gamma coefficient. -/
theorem unequalMellinJoint_integral_q (nu : ℂ) {s : ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s.re) (v : ℝ) :
    (∫ q in Ioi (0 : ℝ), unequalMellinJoint nu s a b v q) =
      zeroMellinGamma s * distancePowerKernel nu s a b v := by
  unfold unequalMellinJoint
  rw [integral_mul_const, scaledZeroMellin_integral hs (hyperbolicDistance_pos ha hb v)]
  unfold distancePowerKernel
  ring

/-- The other fiber is the actual unequal K product at x=a*q,y=b*q,
using the proved real square-root distance scaling. -/
theorem unequalMellinJoint_integral_v (nu s : ℂ) {a b q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) :
    (∫ v in Ioi (0 : ℝ), unequalMellinJoint nu s a b v q) =
      unequalProductMellin nu s a b q := by
  have hproduct := actual_K_unequal_hyperbolic_distance nu (mul_pos ha hq) (mul_pos hb hq)
  unfold unequalMellinJoint scaledZeroMellin unequalProductMellin
  calc
    _ = (q : ℂ) ^ (s - 1) * ∫ v in Ioi (0 : ℝ),
        complexOrderK 0 (hyperbolicDistance (a * q) (b * q) v) *
          Complex.cosh (nu * (v : ℂ)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      rw [hyperbolicDistance_mul a b v hq]
      ring
    _ = _ := by
      change (q : ℂ) ^ (s - 1) *
        (∫ v in Ioi (0 : ℝ), complexOrderK 0
          (Real.sqrt ((a * q) ^ 2 + (b * q) ^ 2 +
            2 * (a * q) * (b * q) * Real.cosh v)) * Complex.cosh (nu * (v : ℂ))) = _
      rw [← hproduct]
      ring

/-- Absolute convergence of the actual unequal-scaled K product Mellin
integral on the full strip Re(s)>2*|Re(nu)|. -/
theorem unequalProductMellin_integrable {nu s : ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * |nu.re| < s.re) :
    Integrable (unequalProductMellin nu s a b) positiveMeasure := by
  have h := (unequalMellinJoint_integrable ha hb hs).integral_prod_right
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact unequalMellinJoint_integral_v nu s ha hb hq

/-- The true product Mellin reduction, proved by absolutely convergent
Fubini and evaluated actual K_0 fibers. -/
theorem actual_K_unequal_scaled_mellin_kernel {nu s : ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * |nu.re| < s.re) :
    (∫ q in Ioi (0 : ℝ), unequalProductMellin nu s a b q) =
      zeroMellinGamma s * ∫ v in Ioi (0 : ℝ), distancePowerKernel nu s a b v := by
  have hs0 : 0 < s.re := by linarith [abs_nonneg nu.re]
  have hjoint := unequalMellinJoint_integrable ha hb hs
  calc
    _ = ∫ q in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), unequalMellinJoint nu s a b v q := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact (unequalMellinJoint_integral_v nu s ha hb hq).symm
    _ = ∫ v in Ioi (0 : ℝ), ∫ q in Ioi (0 : ℝ), unequalMellinJoint nu s a b v q :=
      (integral_integral_swap hjoint).symm
    _ = _ := by
      simp_rw [unequalMellinJoint_integral_q nu ha hb hs0]
      rw [integral_const_mul]

/-- Displayed actual unequal-scaled product Mellin formula. The remaining
integral is literal, with its own proved absolute convergence. -/
theorem actual_K_unequal_scaled_mellin {nu s : ℂ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * |nu.re| < s.re) :
    (∫ q in Ioi (0 : ℝ), (q : ℂ) ^ (s - 1) *
      complexOrderK nu (a * q) * complexOrderK nu (b * q)) =
      ((2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2) *
        ∫ v in Ioi (0 : ℝ), Complex.cosh (nu * (v : ℂ)) *
          ((a ^ 2 + b ^ 2 + 2 * a * b * Real.cosh v : ℝ) : ℂ) ^ (-s / 2) := by
  change (∫ q in Ioi (0 : ℝ), unequalProductMellin nu s a b q) =
    zeroMellinGamma s * ∫ v in Ioi (0 : ℝ), Complex.cosh (nu * (v : ℂ)) *
      (squaredDistance a b v : ℂ) ^ (-s / 2)
  rw [actual_K_unequal_scaled_mellin_kernel ha hb hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  unfold distancePowerKernel
  rw [hyperbolicDistance_cpow s ha hb v]

end
end ImbalancedChen.Part3.ActualKUnequalScaledMellin20261026b
