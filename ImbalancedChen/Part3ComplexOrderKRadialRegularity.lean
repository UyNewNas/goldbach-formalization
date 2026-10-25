import ImbalancedChen.Part3ComplexOrderKQCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual all-complex-order K radial regularity from the literal differentiated
Laplace moments. No ODE, derivative, or regularity is supplied as a premise.
This discharges one actual-function input of the general compact Green
calculation; neither an I/K connection nor a normalized Green identity follows.
-/
namespace ImbalancedChen.Part3.ComplexOrderKRadialRegularitySourceOnly
noncomputable section
open Set
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus

def radialMoment (k : ℕ) (nu : ℂ) (r : ℝ) : ℂ := qMoment k nu (Real.exp r)

theorem radialMoment_hasDerivAt (k : ℕ) (nu : ℂ) (r : ℝ) :
    HasDerivAt (radialMoment k nu)
      (Real.exp r • radialMoment (k + 1) nu r) r := by
  simpa only [radialMoment, Function.comp_def] using
    (qMoment_hasDerivAt k nu (Real.exp_pos r)).scomp r (Real.hasDerivAt_exp r)

theorem radialMoment_deriv (k : ℕ) (nu : ℂ) :
    deriv (radialMoment k nu) = fun r => Real.exp r • radialMoment (k + 1) nu r := by
  funext r
  exact (radialMoment_hasDerivAt k nu r).deriv

theorem radialMoment_continuous (k : ℕ) (nu : ℂ) : Continuous (radialMoment k nu) := by
  exact (show Differentiable ℝ (radialMoment k nu) from
    fun r => (radialMoment_hasDerivAt k nu r).differentiableAt).continuous

theorem radialMoment_C1 (k : ℕ) (nu : ℂ) : ContDiff ℝ 1 (radialMoment k nu) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · intro r
    exact (radialMoment_hasDerivAt k nu r).differentiableAt
  · rw [radialMoment_deriv]
    exact Real.continuous_exp.smul (radialMoment_continuous (k + 1) nu)

/-- The actual next two moments imply C2 in the complete log coordinate,
without an order-strip restriction or an endpoint condition at q=0. -/
theorem radialMoment_C2 (k : ℕ) (nu : ℂ) : ContDiff ℝ 2 (radialMoment k nu) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun r => (radialMoment_hasDerivAt k nu r).differentiableAt, by simp, ?_⟩
  rw [radialMoment_deriv]
  exact Real.contDiff_exp.smul (radialMoment_C1 (k + 1) nu)

def radialK (nu : ℂ) (r : ℝ) : ℂ := complexOrderK nu (Real.exp r)

theorem radialK_eq_radialMoment_zero (nu : ℂ) : radialK nu = radialMoment 0 nu := by
  funext r
  exact (qMoment_zero nu (Real.exp r)).symm

theorem radialK_C2 (nu : ℂ) : ContDiff ℝ 2 (radialK nu) := by
  rw [radialK_eq_radialMoment_zero]
  exact radialMoment_C2 0 nu

/-- The exact Euler-coordinate derivative of the actual general K integral. -/
theorem radialK_hasDerivAt (nu : ℂ) (r : ℝ) :
    HasDerivAt (radialK nu) (Real.exp r • radialMoment 1 nu r) r := by
  rw [radialK_eq_radialMoment_zero]
  exact radialMoment_hasDerivAt 0 nu r

/-- The first moment contributes a genuine extra term under q=exp(r). -/
theorem radialK_second_deriv (nu : ℂ) (r : ℝ) :
    deriv (deriv (radialK nu)) r =
      Real.exp r • radialMoment 1 nu r +
        (Real.exp r) ^ 2 • radialMoment 2 nu r := by
  have hfirst : deriv (radialK nu) = fun s => Real.exp s • radialMoment 1 nu s := by
    funext s
    exact (radialK_hasDerivAt nu s).deriv
  rw [hfirst]
  have hd := (Real.hasDerivAt_exp r).smul (radialMoment_hasDerivAt 1 nu r)
  simpa only [smul_smul, pow_two] using hd.deriv

end
end ImbalancedChen.Part3.ComplexOrderKRadialRegularitySourceOnly
