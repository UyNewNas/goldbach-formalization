import ImbalancedChen.Part3ActualKUnequalHyperbolicDistance
import ImbalancedChen.Part3ActualKZeroSchwingerFiber
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

DLMF 10.32.18 at independently positive real arguments and arbitrary
complex order, derived from the actual K_0 distance product. Its inner
K_0 is expanded by the proved positive Schwinger density. The exact
integral of the norm along that density is twice the norm of the prior
cosh-distance kernel, so the two-variable expansion is jointly L1.
Fubini is then justified, and the other fiber is the literal defining
integral of K_nu(x*y/t). No product/Weber formula or final-integrability
hypothesis is used.

Primary formula and domain checked at https://dlmf.nist.gov/10.32.E18:
the printed complex domain is |ph z|<pi, |ph zeta|<pi, and
|ph(z+zeta)|<pi/4. This module proves ONLY the positive-real slice.
Extension to the printed complex domain remains OPEN. Orbital kernel
identification and automorphic normalization also remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualKMacdonaldPositive20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualKUnequalHyperbolicDistance20261026b
open ActualKZeroSchwingerFiber20261026b

/-- The actual two-variable expansion of the previously proved K_0
cosh-distance product kernel. The coordinate order is (v,t). -/
def macdonaldJoint (nu : ℂ) (x y v t : ℝ) : ℂ :=
  (zeroSchwingerDensity (hyperbolicDistance x y v) t : ℂ) *
    Complex.cosh (nu * (v : ℂ))

theorem macdonaldJoint_measurable (nu : ℂ) (x y : ℝ) :
    Measurable (fun p : ℝ × ℝ => macdonaldJoint nu x y p.1 p.2) := by
  unfold macdonaldJoint zeroSchwingerDensity hyperbolicDistance
  fun_prop

/-- Exact absolute integral along the Schwinger fiber. The positivity of
that real density supplies an equality, so no external majorant is needed. -/
theorem macdonaldJoint_norm_fiber (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (v : ℝ) :
    (∫ t in Ioi (0 : ℝ), ‖macdonaldJoint nu x y v t‖) =
      2 * ‖coshDistanceKernel nu x y v‖ := by
  simp only [macdonaldJoint, norm_mul]
  rw [integral_mul_const,
    zeroSchwingerDensity_norm_integral (hyperbolicDistance_pos hx hy v)]
  unfold coshDistanceKernel
  rw [norm_mul]
  ring

/-- Joint absolute convergence before the Fubini interchange. Both
arguments vary independently, and the complex order is unrestricted. -/
theorem macdonaldJoint_integrable (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun p : ℝ × ℝ => macdonaldJoint nu x y p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  apply (integrable_prod_iff (macdonaldJoint_measurable nu x y).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun v =>
      (zeroSchwingerDensity_complex_integrable (hyperbolicDistance_pos hx hy v)).mul_const _
  · apply ((coshDistanceKernel_integrable nu hx hy).norm.const_mul 2).congr
    exact Eventually.of_forall fun v => (macdonaldJoint_norm_fiber nu hx hy v).symm

/-- Evaluation along t reproduces the actual distance kernel. -/
theorem macdonaldJoint_integral_t (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (v : ℝ) :
    (∫ t in Ioi (0 : ℝ), macdonaldJoint nu x y v t) =
      2 * coshDistanceKernel nu x y v := by
  unfold macdonaldJoint
  rw [integral_mul_const,
    zeroSchwingerDensity_complex_integral (hyperbolicDistance_pos hx hy v)]
  unfold coshDistanceKernel
  ring

theorem hyperbolicDistance_sq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : ℝ) :
    hyperbolicDistance x y v ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y * Real.cosh v := by
  unfold hyperbolicDistance
  apply Real.sq_sqrt
  have hcosh := Real.cosh_pos v
  positivity

def macdonaldWeight (x y t : ℝ) : ℝ :=
  t⁻¹ * Real.exp (-t / 2 - (x ^ 2 + y ^ 2) / (2 * t))

def macdonaldKernel (nu : ℂ) (x y t : ℝ) : ℂ :=
  (macdonaldWeight x y t : ℂ) * complexOrderK nu (x * y / t)

/-- The exact damping split exposes the actual K_nu(x*y/t) fiber. -/
theorem macdonaldJoint_factor (nu : ℂ) {x y t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) (v : ℝ) :
    macdonaldJoint nu x y v t = (macdonaldWeight x y t : ℂ) *
      complexOrderIntegrand nu (x * y / t) v := by
  have hexponent : -t / 2 - (x ^ 2 + y ^ 2 + 2 * x * y * Real.cosh v) / (2 * t) =
      (-t / 2 - (x ^ 2 + y ^ 2) / (2 * t)) + (-(x * y / t) * Real.cosh v) := by
    field_simp [ht.ne'] <;> ring
  unfold macdonaldJoint zeroSchwingerDensity macdonaldWeight complexOrderIntegrand
  rw [hyperbolicDistance_sq hx hy v, hexponent, Real.exp_add]
  push_cast
  ring

/-- Evaluation along v is the actual defining positive K integral. -/
theorem macdonaldJoint_integral_v (nu : ℂ) {x y t : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    (∫ v in Ioi (0 : ℝ), macdonaldJoint nu x y v t) = macdonaldKernel nu x y t := by
  simp_rw [macdonaldJoint_factor nu hx hy ht]
  rw [integral_const_mul]
  rfl

/-- Absolute convergence of the actual Macdonald single-integral kernel,
derived from joint L1 rather than supplied as an assumption. -/
theorem macdonaldKernel_integrable (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    Integrable (macdonaldKernel nu x y) positiveMeasure := by
  have h := (macdonaldJoint_integrable nu hx hy).integral_prod_right
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact macdonaldJoint_integral_v nu hx hy ht

/-- The positive-real Macdonald transform, assembled by an actual
absolutely convergent Schwinger expansion and Fubini. -/
theorem actual_K_macdonald_positive_kernel (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    complexOrderK nu x * complexOrderK nu y =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), macdonaldKernel nu x y t := by
  have hjoint := macdonaldJoint_integrable nu hx hy
  have hexpansion : (∫ v in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      macdonaldJoint nu x y v t) =
        2 * (complexOrderK nu x * complexOrderK nu y) := by
    calc
      _ = 2 * ∫ v in Ioi (0 : ℝ), coshDistanceKernel nu x y v := by
        simp_rw [macdonaldJoint_integral_t nu hx hy]
        rw [integral_const_mul]
      _ = _ := by
        congr 1
        exact (actual_K_unequal_hyperbolic_distance nu hx hy).symm
  have heval : (∫ v in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      macdonaldJoint nu x y v t) =
        ∫ t in Ioi (0 : ℝ), macdonaldKernel nu x y t := by
    rw [integral_integral_swap hjoint]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact macdonaldJoint_integral_v nu hx hy ht
  calc
    _ = (1 / 2 : ℂ) * (2 * (complexOrderK nu x * complexOrderK nu y)) := by ring
    _ = _ := by rw [← hexpansion, heval]

theorem macdonaldKernel_eq_display (nu : ℂ) (x y t : ℝ) :
    macdonaldKernel nu x y t =
      (Real.exp (-t / 2 - (x ^ 2 + y ^ 2) / (2 * t)) : ℂ) *
        complexOrderK nu (x * y / t) / (t : ℂ) := by
  unfold macdonaldKernel macdonaldWeight
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

/-- Separately stated convergence of the displayed DLMF 10.32.18 density. -/
theorem actual_K_macdonald_positive_integrable (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun t =>
      (Real.exp (-t / 2 - (x ^ 2 + y ^ 2) / (2 * t)) : ℂ) *
        complexOrderK nu (x * y / t) / (t : ℂ)) (Ioi 0) := by
  apply (macdonaldKernel_integrable nu hx hy).congr
  exact Eventually.of_forall (macdonaldKernel_eq_display nu x y)

/-- DLMF 10.32.18 at two independently positive real arguments, with
arbitrary complex order. The printed complex-sector extension is OPEN. -/
theorem actual_K_macdonald_positive (nu : ℂ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    complexOrderK nu x * complexOrderK nu y =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ),
        (Real.exp (-t / 2 - (x ^ 2 + y ^ 2) / (2 * t)) : ℂ) *
          complexOrderK nu (x * y / t) / (t : ℂ) := by
  rw [actual_K_macdonald_positive_kernel nu hx hy]
  simp_rw [macdonaldKernel_eq_display]

end
end ImbalancedChen.Part3.ActualKMacdonaldPositive20261026b
