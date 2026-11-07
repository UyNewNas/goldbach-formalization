import ImbalancedChen.Part3ActualGeneralJBessel
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual imaginary-order J transformed to the one-dimensional oscillatory
radial equation. Every derivative is derived from the literal actual J
jets. The sole differential-equation supplier is the proved actual
generalJ_jet_equation, not an assumed energy or transformed ODE.
No held small-q/Mellin convergence chain is imported or used.
-/

namespace ImbalancedChen.Part3.ActualJImaginaryRadialJet20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly

def radialCoefficient (t : ℝ) : ℝ := 1 / 4 + 4 * t ^ 2

def radialPotential (t q : ℝ) : ℝ := 1 + radialCoefficient t / q ^ 2

def radialJ (t q : ℝ) : ℂ :=
  (Real.sqrt q : ℂ) * generalJ (2 * I * (t : ℂ)) q

def radialJFirst (t q : ℝ) : ℂ :=
  (Real.sqrt q : ℂ) * generalJFirst (2 * I * (t : ℂ)) q +
    ((1 / (2 * Real.sqrt q) : ℝ) : ℂ) * generalJ (2 * I * (t : ℂ)) q

theorem radialCoefficient_pos (t : ℝ) : 0 < radialCoefficient t := by
  unfold radialCoefficient
  positivity

theorem radialPotential_ge_one (t : ℝ) {q : ℝ} (hq : 0 < q) :
    1 ≤ radialPotential t q := by
  unfold radialPotential
  exact le_add_of_nonneg_right (div_nonneg (radialCoefficient_pos t).le (sq_nonneg q))

private theorem imaginary_order_re (t : ℝ) :
    -1 < (2 * I * (t : ℂ)).re := by simp

private theorem half_inverse_sqrt_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => 1 / (2 * Real.sqrt x))
      (-(1 / (4 * (Real.sqrt q) ^ 3))) q := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have h := ((Real.hasDerivAt_sqrt hq.ne').const_mul 2).inv
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs)
  convert h using 1
  · funext x
    exact one_div _
  · field_simp [hs] <;> ring

/-- The first jet is the actual native derivative of sqrt(q)J_(2it)(q). -/
theorem radialJ_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (radialJ t) (radialJFirst t q) q := by
  have h := (Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul
    (generalJ_hasDerivAt (imaginary_order_re t) hq)
  convert h using 1
  · rfl
  · unfold radialJFirst
    ring

private theorem imaginaryJ_second_eq (t : ℝ) {q : ℝ} (hq : 0 < q) :
    generalJSecond (2 * I * (t : ℂ)) q =
      -generalJFirst (2 * I * (t : ℂ)) q / (q : ℂ) -
        (1 + 4 * (t : ℂ) ^ 2 / (q : ℂ) ^ 2) * generalJ (2 * I * (t : ℂ)) q := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have h := generalJ_jet_equation (imaginary_order_re t) hq
  have hi : (2 * I * (t : ℂ)) ^ 2 = -4 * (t : ℂ) ^ 2 := by
    calc
      (2 * I * (t : ℂ)) ^ 2 = 4 * (I * I) * (t : ℂ) ^ 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hi] at h
  have hsolve : generalJSecond (2 * I * (t : ℂ)) q =
      (-(q : ℂ) * generalJFirst (2 * I * (t : ℂ)) q -
        ((q : ℂ) ^ 2 + 4 * (t : ℂ) ^ 2) * generalJ (2 * I * (t : ℂ)) q) /
          (q : ℂ) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hqC)).2
    linear_combination h
  rw [hsolve]
  field_simp [hqC] <;> ring

/-- Actual transformed second-order ODE in first-order jet form. -/
theorem radialJFirst_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (radialJFirst t)
      (-((radialPotential t q : ℝ) : ℂ) * radialJ t q) q := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hsC : (Real.sqrt q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsq : (Real.sqrt q : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  have h1 := ((Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul
    (generalJFirst_hasDerivAt (imaginary_order_re t) hq)).add
      ((half_inverse_sqrt_hasDerivAt hq).ofReal_comp.mul
        (generalJ_hasDerivAt (imaginary_order_re t) hq))
  convert h1 using 1
  · rfl
  · rw [imaginaryJ_second_eq t hq]
    unfold radialPotential radialCoefficient radialJ
    push_cast
    rw [← hsq]
    field_simp [hsC] <;> ring

theorem radialJ_native_second_equation (t : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (deriv (radialJ t)) q +
      ((radialPotential t q : ℝ) : ℂ) * radialJ t q = 0 := by
  have hjet : deriv (radialJ t) =ᶠ[𝓝 q] radialJFirst t := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (radialJ_hasDerivAt t hx).deriv
  have hsecond := (radialJFirst_hasDerivAt t hq).congr_of_eventuallyEq hjet
  rw [hsecond.deriv]
  ring

end
end ImbalancedChen.Part3.ActualJImaginaryRadialJet20261026b
