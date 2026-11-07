import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A constant complex flux with integrable physical height division vanishes

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is the actual reciprocal-height obstruction, independent of any
radial scalar derivative or canonical K supplier. Multiplication by the
inverse nonzero complex constant and real projection would make 1/y
integrable on a half-line, contradicting the pinned real theorem.
-/

namespace ImbalancedChen.Part3.ConstantWeightedHeightFlux20261026b

noncomputable section
open Set MeasureTheory Filter

/-- A complex constant divided by physical height is integrable on a
half-line only when the constant is zero. No positive endpoint is needed. -/
theorem eq_zero_of_integrableOn_div_height {a : ℝ} {c : ℂ}
    (h : IntegrableOn (fun y : ℝ => c/(y : ℂ)) (Ioi a)) : c=0 := by
  by_contra hc
  have hi : IntegrableOn (fun y : ℝ => (y : ℂ)⁻¹) (Ioi a) := by
    have hs := h.const_mul c⁻¹
    simpa only [div_eq_mul_inv,← mul_assoc,inv_mul_cancel₀ hc,one_mul] using hs
  have hr : IntegrableOn (fun y : ℝ => y⁻¹) (Ioi a) := by
    simpa only [← Complex.ofReal_inv,Complex.ofReal_re] using hi.re
  exact not_integrableOn_Ioi_inv hr

/-- A flux constant on its ORIGINAL open height domain and with integrable
physical height division on any smaller far tail vanishes on that entire
original domain. This does not assert linear dependence of vector functions. -/
theorem constant_flux_zero_of_weighted_integrability
    {Y S : ℝ} {W : ℝ → ℂ} (hYS : Y≤S)
    (hconst : ∀ a b : ℝ, Y<a → Y<b → W a=W b)
    (hint : IntegrableOn (fun y : ℝ => W y/(y : ℂ)) (Ioi S)) :
    ∀ a : ℝ, Y<a → W a=0 := by
  intro a ha
  apply eq_zero_of_integrableOn_div_height (a := S)
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [hconst y a (hYS.trans_lt hy) ha]

end
end ImbalancedChen.Part3.ConstantWeightedHeightFlux20261026b
