import ImbalancedChen.Part3ActualJSecondOrderJet
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual real-order J radial jets. For |nu|<=1/2 the transformed potential
coefficient a=1/4-nu^2 is nonnegative. Native derivatives and the actual
Bessel equation, valid for nu>-1, give u''+(1+a/q^2)u=0, u=sqrt(q)J_nu(q).
No imaginary-order substitution or complementary spectral theorem is used.
-/

namespace ImbalancedChen.Part3.ActualRealOrderJRadialJet20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualJSecondOrderJet20261026b

def realRadialCoefficient (nu : ℝ) : ℝ := 1 / 4 - nu ^ 2
def realRadialPotential (nu q : ℝ) : ℝ := 1 + realRadialCoefficient nu / q ^ 2
def realRadialJ (nu q : ℝ) : ℂ := (Real.sqrt q : ℂ) * generalJ (nu : ℂ) q
def realRadialJFirst (nu q : ℝ) : ℂ :=
  (Real.sqrt q : ℂ) * generalJFirst (nu : ℂ) q +
    ((1 / (2 * Real.sqrt q) : ℝ) : ℂ) * generalJ (nu : ℂ) q

theorem real_order_lower {nu : ℝ} (hnu : |nu| ≤ 1 / 2) : -1 < (nu : ℂ).re := by
  have hn := abs_le.mp hnu
  simp only [Complex.ofReal_re]
  linarith

theorem realRadialCoefficient_nonneg {nu : ℝ} (hnu : |nu| ≤ 1 / 2) :
    0 ≤ realRadialCoefficient nu := by
  have hn := abs_le.mp hnu
  have hp : 0 ≤ (1 / 2 - nu) * (1 / 2 + nu) := mul_nonneg (by linarith [hn.2]) (by linarith [hn.1])
  unfold realRadialCoefficient
  nlinarith

theorem realRadialPotential_ge_one {nu : ℝ} (hnu : |nu| ≤ 1 / 2) (q : ℝ) :
    1 ≤ realRadialPotential nu q := by
  unfold realRadialPotential
  exact le_add_of_nonneg_right (div_nonneg (realRadialCoefficient_nonneg hnu) (sq_nonneg q))

private theorem half_inverse_sqrt_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => 1 / (2 * Real.sqrt x)) (-(1 / (4 * (Real.sqrt q) ^ 3))) q := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have h := ((Real.hasDerivAt_sqrt hq.ne').const_mul 2).inv (mul_ne_zero (by norm_num) hs)
  convert h using 1
  · funext x
    exact one_div _
  · field_simp [hs] <;> ring

theorem realRadialJ_hasDerivAt {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (realRadialJ nu) (realRadialJFirst nu q) q := by
  have h := (Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul (generalJ_hasDerivAt (real_order_lower hnu) hq)
  convert h using 1 <;> unfold realRadialJ realRadialJFirst <;> ring

/-- Actual complementary-order transformed jet equation. -/
theorem realRadialJFirst_hasDerivAt {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (realRadialJFirst nu) (-(realRadialPotential nu q) • realRadialJ nu q) q := by
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hsC : (Real.sqrt q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsq : (Real.sqrt q : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast Real.sq_sqrt hq.le
  have h := ((Real.hasDerivAt_sqrt hq.ne').ofReal_comp.mul
    (generalJFirst_hasDerivAt (real_order_lower hnu) hq)).add
      ((half_inverse_sqrt_hasDerivAt hq).ofReal_comp.mul
        (generalJ_hasDerivAt (real_order_lower hnu) hq))
  convert h using 1
  · rfl
  · rw [generalJSecond_eq_jetFormula (real_order_lower hnu) hq]
    unfold realRadialPotential realRadialCoefficient realRadialJ
    simp only [Complex.real_smul]
    push_cast
    rw [← hsq]
    field_simp [hsC] <;> ring

theorem realRadialJ_native_equation {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {q : ℝ} (hq : 0 < q) :
    deriv (deriv (realRadialJ nu)) q + (realRadialPotential nu q) • realRadialJ nu q = 0 := by
  have he : deriv (realRadialJ nu) =ᶠ[𝓝 q] realRadialJFirst nu := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (realRadialJ_hasDerivAt hnu hx).deriv
  have h := (realRadialJFirst_hasDerivAt hnu hq).congr_of_eventuallyEq he
  rw [h.deriv, neg_smul]
  abel

end
end ImbalancedChen.Part3.ActualRealOrderJRadialJet20261026b
