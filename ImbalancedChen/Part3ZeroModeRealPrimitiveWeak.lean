import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

A native indefinite Lebesgue integral has its genuine distributional derivative.
The primitive is constructed, and its weak identity follows from native
absolute continuity, Lebesgue differentiation, and integration by parts.
This does not assume a Sobolev graph approximation or a boundary trace.
No held tail-Hardy source is imported.
-/

namespace ImbalancedChen.Part3.ZeroModeRealPrimitiveWeak20261026b
noncomputable section
open MeasureTheory Set Filter

def realPrimitive (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in a..x, g t

/-- Genuine weak derivative on a finite interval. The integrals are whole-line
integrals of compact tests; no integrability of g outside (a,b) is needed. -/
theorem realPrimitive_weak_identity {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, deriv ψ x * realPrimitive a g x) = -(∫ x, ψ x * g x) := by
  have hG : AbsolutelyContinuousOnInterval (realPrimitive a g) a b :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hP : AbsolutelyContinuousOnInterval ψ a b :=
    (hψ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport (by
    intro ha
    exact (lt_irrefl a) (hψs ha).1)
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hb
    exact (lt_irrefl b) (hψs hb).2)
  have hderiv : (∫ x in a..b, deriv (realPrimitive a g) x * ψ x) =
      ∫ x in a..b, g x * ψ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxi
    have hx' : x ∈ uIcc a b := uIoc_subset_uIcc hxi
    exact congrArg (fun z : ℝ => z * ψ x) (hx hx' a (by simp)).deriv
  have hibp := hG.integral_mul_deriv_eq_deriv_mul hP
  rw [hψa, hψb, mul_zero, mul_zero, sub_self, zero_sub, hderiv] at hibp
  have hleft : support (fun x => realPrimitive a g x * deriv ψ x) ⊆ Ioc a b := by
    intro x hx
    have hd : deriv ψ x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    have hm : x ∈ tsupport ψ := by
      by_contra hn
      exact hd (deriv_of_notMem_tsupport hn)
    exact ⟨(hψs hm).1, (hψs hm).2.le⟩
  have hright : support (fun x => g x * ψ x) ⊆ Ioc a b := by
    intro x hx
    have hp : ψ x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    have hm := hψs (subset_tsupport ψ hp)
    exact ⟨hm.1, hm.2.le⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hleft,
    intervalIntegral.integral_eq_integral_of_support_subset hright] at hibp
  simpa only [mul_comm] using hibp

/-- The real primitive has an actual continuous representative up to both
endpoints, directly from the native absolute continuity theorem. -/
theorem realPrimitive_continuousOn {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (realPrimitive a g) (uIcc a b) :=
  (hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)).continuousOn

end
end ImbalancedChen.Part3.ZeroModeRealPrimitiveWeak20261026b
