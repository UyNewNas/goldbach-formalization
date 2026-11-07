import ImbalancedChen.HalfProductGeometry

/-!
# The fixed continuous test and its logarithmic mass

The test `u ↦ 1 / (1 - u)` is continuous on the actual closed interval
`[alpha, 1/2]`. Its mass against `du / u` is exactly the kernel integral
already proved by the fundamental theorem of calculus in
`HalfProductGeometry.halfProduct_integral`.

The balance-cutoff specialization reuses that theorem directly; the general
positive lower endpoint follows by the substitution `b = alpha / (1 - alpha)`.
No integral evaluation or limiting measure is assumed, and the calculus
proof is not duplicated here.

The final identity rewrites the actual summand
`log x / (p * log (x / p))` in terms of this fixed test at `log p / log x`;
every denominator is justified. There are no external project dependencies.
-/

namespace ImbalancedChen

open MeasureTheory Set

/-- The fixed test is continuous all the way to both integration endpoints. -/
theorem continuousOn_massLogTest (alpha : ℝ) :
    ContinuousOn (fun u : ℝ => 1 / (1 - u)) (Icc alpha (1 / 2 : ℝ)) := by
  apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
  intro u hu
  change (1 - u : ℝ) ≠ 0
  exact ne_of_gt (by linarith [hu.2])

/-- The factor `1 / u` is also harmless on the positive closed interval. -/
theorem continuousOn_massLogKernel {alpha : ℝ} (halpha : 0 < alpha) :
    ContinuousOn (fun u : ℝ => (1 / (1 - u)) / u)
      (Icc alpha (1 / 2 : ℝ)) := by
  apply (continuousOn_massLogTest alpha).div continuousOn_id
  intro u hu
  exact ne_of_gt (lt_of_lt_of_le halpha hu.1)

/-- Integrability comes from the actual continuity proof. -/
theorem intervalIntegrable_massLogKernel {alpha : ℝ}
    (halpha : 0 < alpha) (hhalf : alpha < 1 / 2) :
    IntervalIntegrable (fun u : ℝ => (1 / (1 - u)) / u)
      volume alpha (1 / 2) := by
  have hcont : ContinuousOn (fun u : ℝ => (1 / (1 - u)) / u)
      (uIcc alpha (1 / 2 : ℝ)) := by
    rw [uIcc_of_le hhalf.le]
    exact continuousOn_massLogKernel halpha
  exact hcont.intervalIntegrable

/-- Reuse the already proved half-product integral at the exact balance
cutoff. The only new step is the pointwise identity between the kernels. -/
theorem massLogIntegral_at_balanceRatio {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ u in (b / (1 + b))..(1 / 2 : ℝ), (1 / (1 - u)) / u) =
      Real.log (1 / b) := by
  have hkernel : (fun u : ℝ => (1 / (1 - u)) / u) =
      (fun u : ℝ => 1 / (u * (1 - u))) := by
    funext u
    rw [div_div, mul_comm]
  rw [hkernel]
  exact halfProduct_integral hb hb1

/-- Every positive lower endpoint below `1/2` is a balance cutoff. Thus the
general mass formula follows from the existing FTC-based integral theorem. -/
theorem massLogIntegral_eq_log_ratio {alpha : ℝ}
    (halpha : 0 < alpha) (hhalf : alpha < 1 / 2) :
    (∫ u in alpha..(1 / 2 : ℝ), (1 / (1 - u)) / u) =
      Real.log ((1 - alpha) / alpha) := by
  have hden : 0 < 1 - alpha := by linarith
  have hb : 0 < alpha / (1 - alpha) := div_pos halpha hden
  have hb1 : alpha / (1 - alpha) < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hcut : (alpha / (1 - alpha)) / (1 + alpha / (1 - alpha)) = alpha := by
    field_simp [ne_of_gt hden] <;> ring
  have hrecip : 1 / (alpha / (1 - alpha)) = (1 - alpha) / alpha := by
    field_simp [ne_of_gt halpha, ne_of_gt hden] <;> ring
  simpa only [hcut, hrecip] using massLogIntegral_at_balanceRatio hb hb1

/-- Exact conversion from the original logarithmic prime weight to the fixed
continuous test. The statement applies to every real `0 < p < x`, so in
particular to each prime in the manuscript's actual summation range. -/
theorem massLogKernel_identity {x p : ℝ}
    (hx : 1 < x) (hp : 0 < p) (hpx : p < x) :
    Real.log x / (p * Real.log (x / p)) =
      (1 / (1 - Real.log p / Real.log x)) / p := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hxp : 1 < x / p := (one_lt_div hp).mpr hpx
  have hlogxp : 0 < Real.log (x / p) := Real.log_pos hxp
  have hlogdiv : Real.log (x / p) = Real.log x - Real.log p :=
    Real.log_div hx0 hp0
  have hdiff : Real.log x - Real.log p ≠ 0 := by
    rw [← hlogdiv]
    exact ne_of_gt hlogxp
  have hratio : Real.log p / Real.log x < 1 := by
    apply (div_lt_one hlogx).mpr
    have := hlogxp
    rw [hlogdiv] at this
    linarith
  have htest : 1 - Real.log p / Real.log x ≠ 0 :=
    ne_of_gt (sub_pos.mpr hratio)
  rw [hlogdiv]
  field_simp [hp0, ne_of_gt hlogx, hdiff, htest] <;> ring

end ImbalancedChen
