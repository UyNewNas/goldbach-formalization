import ImbalancedChen.Part3ComplexOrderKQCalculus
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

An actual complex-argument K model on Re(z)>0, defined by the literal
positive hyperbolic Laplace integral. All argument-derivative moment
integrands are absolutely integrable. A single proved envelope works
uniformly for Re(z)>=a>0 and bounded |Re(nu)|, including every compact
subset of the right half-plane and every compact order set. The positive
real axis is identified with the existing actual complexOrderK source.

This introduces no continuation hypothesis. Differentiation in the new
complex argument and extension beyond Re(z)>0 are separate tasks. The
large complex sectors printed in DLMF 10.32.18 remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualComplexArgumentKLaplace20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus
open RealOrderKPositiveLaplace

def rightHalfPlane : Set ℂ := {z | 0 < z.re}

def argumentMomentIntegrand (k : ℕ) (nu z : ℂ) (u : ℝ) : ℂ :=
  (-(Real.cosh u : ℂ)) ^ k * Complex.exp (-z * (Real.cosh u : ℂ)) *
    Complex.cosh (nu * (u : ℂ))

def argumentMoment (k : ℕ) (nu z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), argumentMomentIntegrand k nu z u

def complexArgumentK (nu z : ℂ) : ℂ := argumentMoment 0 nu z

theorem complexArgumentK_eq_integral (nu z : ℂ) :
    complexArgumentK nu z = ∫ u in Ioi (0 : ℝ),
      Complex.exp (-z * (Real.cosh u : ℂ)) * Complex.cosh (nu * (u : ℂ)) := by
  simp only [complexArgumentK, argumentMoment, argumentMomentIntegrand, pow_zero, one_mul]

/-- Complex argument damping has exactly the norm of its real-part
argument damping. No estimate in Im(z) is required. -/
theorem argumentMomentIntegrand_norm_eq_real (k : ℕ) (nu z : ℂ) (u : ℝ) :
    ‖argumentMomentIntegrand k nu z u‖ = ‖qMomentIntegrand k nu z.re u‖ := by
  simp only [argumentMomentIntegrand, qMomentIntegrand, norm_mul, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Uniform compact-right-half-plane envelope for every moment and every
order in a bounded real-part strip. It is stronger than compactness in z:
the imaginary part is unrestricted. -/
theorem argumentMomentIntegrand_norm_le (k : ℕ) {nu z : ℂ} {a A u : ℝ}
    (hz : a ≤ z.re) (hnu : |nu.re| ≤ A) (hu : 0 ≤ u) :
    ‖argumentMomentIntegrand k nu z u‖ ≤ tiltedCoshDensity ((k : ℝ) + A) a u := by
  rw [argumentMomentIntegrand_norm_eq_real]
  calc
    _ ≤ tiltedCoshDensity ((k : ℝ) + |nu.re|) a u :=
      qMomentIntegrand_norm_le k nu hz hu
    _ ≤ _ := by
      unfold tiltedCoshDensity
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right hnu hu
      linarith

/-- The compact envelope is an actual integrable real function. -/
theorem argumentMomentEnvelope_integrable (k : ℕ) (A : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (tiltedCoshDensity ((k : ℝ) + A) a) (Ioi (0 : ℝ)) :=
  (tiltedCoshDensity_integrable _ ha).integrableOn

theorem argumentMomentIntegrand_continuous (k : ℕ) (nu z : ℂ) :
    Continuous (argumentMomentIntegrand k nu z) := by
  unfold argumentMomentIntegrand
  fun_prop

/-- Absolute convergence of every actual complex-argument moment on the
complete right half-plane, without a restriction on the complex order. -/
theorem argumentMoment_integrable (k : ℕ) (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (argumentMomentIntegrand k nu z) (Ioi (0 : ℝ)) := by
  apply (argumentMomentEnvelope_integrable k |nu.re| hz).mono'
    (argumentMomentIntegrand_continuous k nu z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact argumentMomentIntegrand_norm_le k le_rfl le_rfl hu.le

/-- Exact agreement of the integrands at real arguments. -/
theorem argumentMomentIntegrand_real (k : ℕ) (nu : ℂ) (q u : ℝ) :
    argumentMomentIntegrand k nu (q : ℂ) u = qMomentIntegrand k nu q u := by
  have hexponent : -(q : ℂ) * (Real.cosh u : ℂ) = ((-q * Real.cosh u : ℝ) : ℂ) := by
    push_cast
    ring
  unfold argumentMomentIntegrand qMomentIntegrand
  rw [hexponent, ← Complex.ofReal_exp]

theorem argumentMoment_real (k : ℕ) (nu : ℂ) (q : ℝ) :
    argumentMoment k nu (q : ℂ) = qMoment k nu q := by
  unfold argumentMoment qMoment
  simp_rw [argumentMomentIntegrand_real]

/-- On q>0 this identifies two absolutely convergent actual K models.
The definition-level equality also holds at every other real q. -/
theorem complexArgumentK_real (nu : ℂ) (q : ℝ) :
    complexArgumentK nu (q : ℂ) = complexOrderK nu q := by
  unfold complexArgumentK
  rw [argumentMoment_real, qMoment_zero]

end
end ImbalancedChen.Part3.ActualComplexArgumentKLaplace20261026b
