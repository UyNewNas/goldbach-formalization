import ImbalancedChen.Part3ActualGreenColumnL2
import ImbalancedChen.Part3ActualRadialGreenFiniteMass
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Actual two-order resolvent composition for the canonical general I/K Green
kernel on the logarithmic line. The finite calculation retains the literal
remote fluxes and both source jumps. Actual whole-line column L2 and actual
value/derivative limits supply integrability and remove the remote fluxes.
No resolvent identity, boundary condition, or integral bound is an input.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualGreenComposition20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open GeneralActualRadialGreenSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ComplexCompactGreenGluingSourceOnly ActualRadialGreenFiniteMass20261025a
open ActualGreenColumnL220261025a

private theorem legal_order {nu : ℝ} (hnu : 0 < nu) : -1 < (nu : ℂ).re := by
  simp only [Complex.ofReal_re]
  linarith

/-- The literal min/max kernel is symmetric in its two spatial arguments. -/
theorem actualGreen_symmetric (nu : ℂ) (s t : ℝ) :
    actualRadialGreen nu s t = actualRadialGreen nu t s := by
  simp only [actualRadialGreen, kernel, min_comm, max_comm]

/-- Actual columns of different positive real orders have an integrable
product. This is the L2 Holder estimate, with no row-mass hypothesis. -/
theorem actualGreen_product_integrable {nu mu : ℝ} (hnu : 0 < nu) (hmu : 0 < mu)
    (s t : ℝ) :
    Integrable (fun r : ℝ =>
      actualRadialGreen (nu : ℂ) s r * actualRadialGreen (mu : ℂ) t r) := by
  exact (actualRadialGreen_memLp_two hnu s).integrable_mul
    (actualRadialGreen_memLp_two hmu t)

/-- Bilinear flux of two actual columns, using their explicit first
branches. The convention at the sources is immaterial at infinity. -/
def actualGreenPairFlux (nu mu s t r : ℝ) : ℂ :=
  actualGreenColumnFirst nu s r * actualRadialGreen (mu : ℂ) t r -
    actualRadialGreen (nu : ℂ) s r * actualGreenColumnFirst mu t r

private def leftPairFlux (nu mu s t r : ℝ) : ℂ :=
  radialK (nu : ℂ) s * radialK (mu : ℂ) t *
    flux (radialI (nu : ℂ)) (radialI (mu : ℂ)) r

private def rightPairFlux (nu mu s t r : ℝ) : ℂ :=
  radialI (nu : ℂ) s * radialI (mu : ℂ) t *
    flux (radialK (nu : ℂ)) (radialK (mu : ℂ)) r

private theorem leftPairFlux_eq {nu mu s t r : ℝ} (hrs : r ≤ s) (hrt : r ≤ t) :
    leftPairFlux nu mu s t r = actualGreenPairFlux nu mu s t r := by
  rw [actualGreenPairFlux, actualGreen_left_branch _ hrs,
    actualGreen_left_branch _ hrt]
  simp only [actualGreenColumnFirst, if_pos hrs, if_pos hrt, leftPairFlux, flux]
  ring

private theorem rightPairFlux_eq {nu mu s t r : ℝ} (hsr : s < r) (htr : t < r) :
    rightPairFlux nu mu s t r = actualGreenPairFlux nu mu s t r := by
  rw [actualGreenPairFlux, actualGreen_right_branch _ hsr.le,
    actualGreen_right_branch _ htr.le]
  simp only [actualGreenColumnFirst, if_neg (not_le.mpr hsr),
    if_neg (not_le.mpr htr), rightPairFlux, flux]
  ring

/-- Both actual column flux endpoints vanish, including the genuine
first derivatives rather than a supplied boundary functional. -/
theorem actualGreenPairFlux_left_zero {nu mu : ℝ} (hnu : 0 < nu) (hmu : 0 < mu)
    (s t : ℝ) : Tendsto (actualGreenPairFlux nu mu s t) atBot (𝓝 0) := by
  have h := ((actualGreenColumnFirst_tendsto_left_zero hnu s).mul
    (actualRadialGreen_tendsto_left_zero hmu t)).sub
    ((actualRadialGreen_tendsto_left_zero hnu s).mul
      (actualGreenColumnFirst_tendsto_left_zero hmu t))
  simpa only [actualGreenPairFlux, mul_zero, sub_self] using h

theorem actualGreenPairFlux_right_zero {nu mu : ℝ} (hnu : 0 < nu) (hmu : 0 < mu)
    (s t : ℝ) : Tendsto (actualGreenPairFlux nu mu s t) atTop (𝓝 0) := by
  have h := ((actualGreenColumnFirst_tendsto_right_zero hnu s).mul
    (actualRadialGreen_tendsto_right_zero hmu t)).sub
    ((actualRadialGreen_tendsto_right_zero hnu s).mul
      (actualGreenColumnFirst_tendsto_right_zero hmu t))
  simpa only [actualGreenPairFlux, mul_zero, sub_self] using h

private theorem leftPairFlux_zero {nu mu : ℝ} (hnu : 0 < nu) (hmu : 0 < mu)
    (s t : ℝ) : Tendsto (leftPairFlux nu mu s t) atBot (𝓝 0) := by
  have he : actualGreenPairFlux nu mu s t =ᶠ[atBot] leftPairFlux nu mu s t := by
    filter_upwards [eventually_le_atBot s, eventually_le_atBot t] with r hrs hrt
    exact (leftPairFlux_eq hrs hrt).symm
  exact (actualGreenPairFlux_left_zero hnu hmu s t).congr' he

private theorem rightPairFlux_zero {nu mu : ℝ} (hnu : 0 < nu) (hmu : 0 < mu)
    (s t : ℝ) : Tendsto (rightPairFlux nu mu s t) atTop (𝓝 0) := by
  have he : actualGreenPairFlux nu mu s t =ᶠ[atTop] rightPairFlux nu mu s t := by
    filter_upwards [eventually_gt_atTop s, eventually_gt_atTop t] with r hrs hrt
    exact (rightPairFlux_eq hrs hrt).symm
  exact (actualGreenPairFlux_right_zero hnu hmu s t).congr' he

/-- The finite Lagrange calculation reuses the native flux derivative.
The two equations below are instantiated only with actual I/K modes. -/
private theorem integral_pair_flux (nu mu : ℂ) (u v : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huODE : ∀ r, deriv (deriv u) r = potential nu r * u r)
    (hvODE : ∀ r, deriv (deriv v) r = potential mu r * v r) (a b : ℝ) :
    (nu ^ 2 - mu ^ 2) * (∫ r in a..b, u r * v r) =
      flux u v b - flux u v a := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r _
    have hd := ((flux_C1 u v hu hv).differentiable_one r).hasDerivAt
    rw [flux_derivative u v hu hv r, huODE r, hvODE r] at hd
    convert hd using 1 <;> dsimp [potential] <;> ring
  · exact ((hu.continuous.mul hv.continuous).const_mul _).intervalIntegrable a b

/-- For ordered sources, the exact finite identity contains two actual
source masses and both unmodified remote pair fluxes. It remains valid
when the sources coincide. -/
theorem actualGreen_finite_composition_ordered {nu mu : ℝ}
    (hnu : 0 < nu) (hnuUpper : nu < 1)
    (hmu : 0 < mu) (hmuUpper : mu < 1)
    {a s t b : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ((nu : ℂ) ^ 2 - (mu : ℂ) ^ 2) *
        (∫ r in a..b, actualRadialGreen (nu : ℂ) s r *
          actualRadialGreen (mu : ℂ) t r) =
      actualRadialGreen (mu : ℂ) t s - actualRadialGreen (nu : ℂ) s t +
        rightPairFlux nu mu s t b - leftPairFlux nu mu s t a := by
  have hi := legal_order hnu
  have hj := legal_order hmu
  have hc : Continuous (fun r : ℝ => actualRadialGreen (nu : ℂ) s r *
      actualRadialGreen (mu : ℂ) t r) :=
    (actualRadialGreen_continuous hi s).mul (actualRadialGreen_continuous hj t)
  have hleft : (∫ r in a..s, actualRadialGreen (nu : ℂ) s r *
      actualRadialGreen (mu : ℂ) t r) =
      radialK (nu : ℂ) s * radialK (mu : ℂ) t *
        (∫ r in a..s, radialI (nu : ℂ) r * radialI (mu : ℂ) r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le has] at hr
    rw [actualGreen_left_branch _ hr.2, actualGreen_left_branch _ (hr.2.trans hst)]
    ring
  have hmiddle : (∫ r in s..t, actualRadialGreen (nu : ℂ) s r *
      actualRadialGreen (mu : ℂ) t r) =
      radialI (nu : ℂ) s * radialK (mu : ℂ) t *
        (∫ r in s..t, radialK (nu : ℂ) r * radialI (mu : ℂ) r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hst] at hr
    rw [actualGreen_right_branch _ hr.1, actualGreen_left_branch _ hr.2]
    ring
  have hright : (∫ r in t..b, actualRadialGreen (nu : ℂ) s r *
      actualRadialGreen (mu : ℂ) t r) =
      radialI (nu : ℂ) s * radialI (mu : ℂ) t *
        (∫ r in t..b, radialK (nu : ℂ) r * radialK (mu : ℂ) r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le htb] at hr
    rw [actualGreen_right_branch _ (hst.trans hr.1), actualGreen_right_branch _ hr.1]
    ring
  have hII := integral_pair_flux (nu : ℂ) (mu : ℂ)
    (radialI (nu : ℂ)) (radialI (mu : ℂ)) (radialI_C2 hi) (radialI_C2 hj)
    (actual_radialI_second_derivative hi) (actual_radialI_second_derivative hj) a s
  have hKI := integral_pair_flux (nu : ℂ) (mu : ℂ)
    (radialK (nu : ℂ)) (radialI (mu : ℂ)) (radialK_C2 _) (radialI_C2 hj)
    (actual_radialK_second_derivative _) (actual_radialI_second_derivative hj) s t
  have hKK := integral_pair_flux (nu : ℂ) (mu : ℂ)
    (radialK (nu : ℂ)) (radialK (mu : ℂ)) (radialK_C2 _) (radialK_C2 _)
    (actual_radialK_second_derivative _) (actual_radialK_second_derivative _) t b
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a s) (hc.intervalIntegrable s b),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable s t) (hc.intervalIntegrable t b), hleft, hmiddle, hright]
  have hwNu := actual_radial_source_wronskian
    (show 0 < (nu : ℂ).re by simpa using hnu)
    (show (nu : ℂ).re < 1 by simpa using hnuUpper) s
  have hwMu := actual_radial_source_wronskian
    (show 0 < (mu : ℂ).re by simpa using hmu)
    (show (mu : ℂ).re < 1 by simpa using hmuUpper) t
  rw [actualGreen_left_branch _ hst, actualGreen_right_branch _ hst]
  dsimp only [leftPairFlux, rightPairFlux, flux] at *
  linear_combination
    (radialK (nu : ℂ) s * radialK (mu : ℂ) t) * hII +
    (radialI (nu : ℂ) s * radialK (mu : ℂ) t) * hKI +
    (radialI (nu : ℂ) s * radialI (mu : ℂ) t) * hKK +
    (radialI (mu : ℂ) s * radialK (mu : ℂ) t) * hwNu -
    (radialI (nu : ℂ) s * radialK (nu : ℂ) t) * hwMu

private theorem composition_ordered {nu mu : ℝ}
    (hnu : 0 < nu) (hnuUpper : nu < 1)
    (hmu : 0 < mu) (hmuUpper : mu < 1) {s t : ℝ} (hst : s ≤ t) :
    ((mu : ℂ) ^ 2 - (nu : ℂ) ^ 2) *
        (∫ r : ℝ, actualRadialGreen (nu : ℂ) s r *
          actualRadialGreen (mu : ℂ) t r) =
      actualRadialGreen (nu : ℂ) s t - actualRadialGreen (mu : ℂ) t s := by
  have hint := actualGreen_product_integrable hnu hmu s t
  have hInt := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have hL := hInt.const_mul ((mu : ℂ) ^ 2 - (nu : ℂ) ^ 2)
  have hR : Tendsto
      (fun R : ℝ => actualRadialGreen (nu : ℂ) s t -
        actualRadialGreen (mu : ℂ) t s + leftPairFlux nu mu s t (-R) -
          rightPairFlux nu mu s t R) atTop
      (𝓝 (actualRadialGreen (nu : ℂ) s t - actualRadialGreen (mu : ℂ) t s)) := by
    simpa only [add_zero, sub_zero] using
      (tendsto_const_nhds.add ((leftPairFlux_zero hnu hmu s t).comp
        tendsto_neg_atTop_atBot)).sub (rightPairFlux_zero hnu hmu s t)
  have he : (fun R : ℝ => ((mu : ℂ) ^ 2 - (nu : ℂ) ^ 2) *
      (∫ r in (-R)..R, actualRadialGreen (nu : ℂ) s r *
        actualRadialGreen (mu : ℂ) t r)) =ᶠ[atTop]
      (fun R : ℝ => actualRadialGreen (nu : ℂ) s t -
        actualRadialGreen (mu : ℂ) t s + leftPairFlux nu mu s t (-R) -
          rightPairFlux nu mu s t R) := by
    filter_upwards [eventually_ge_atTop (-s), eventually_ge_atTop t] with R hRs hRt
    have h := actualGreen_finite_composition_ordered hnu hnuUpper hmu hmuUpper
      (show -R ≤ s by linarith) hst hRt
    linear_combination -h
  exact tendsto_nhds_unique (hL.congr' he) hR

/-- Whole-line multiplied identity for the actual canonical kernel.
The two orders may coincide here; no division has yet been taken. -/
theorem actualGreen_composition_mul {nu mu : ℝ}
    (hnu : 0 < nu) (hnuUpper : nu < 1)
    (hmu : 0 < mu) (hmuUpper : mu < 1) (s t : ℝ) :
    ((mu : ℂ) ^ 2 - (nu : ℂ) ^ 2) *
        (∫ r : ℝ, actualRadialGreen (nu : ℂ) s r *
          actualRadialGreen (mu : ℂ) r t) =
      actualRadialGreen (nu : ℂ) s t - actualRadialGreen (mu : ℂ) s t := by
  have hsym : (fun r : ℝ => actualRadialGreen (nu : ℂ) s r *
      actualRadialGreen (mu : ℂ) r t) =
      (fun r : ℝ => actualRadialGreen (nu : ℂ) s r *
        actualRadialGreen (mu : ℂ) t r) := by
    funext r
    rw [actualGreen_symmetric (mu : ℂ) r t]
  rw [hsym]
  by_cases hst : s ≤ t
  · simpa only [actualGreen_symmetric (mu : ℂ) t s] using
      composition_ordered hnu hnuUpper hmu hmuUpper hst
  · have hts : t ≤ s := (lt_of_not_ge hst).le
    have h := composition_ordered hmu hmuUpper hnu hnuUpper hts
    have hprod : (fun r : ℝ => actualRadialGreen (mu : ℂ) t r *
        actualRadialGreen (nu : ℂ) s r) =
        (fun r : ℝ => actualRadialGreen (nu : ℂ) s r *
          actualRadialGreen (mu : ℂ) t r) := by
      funext r
      ring
    rw [hprod, actualGreen_symmetric (mu : ℂ) t s] at h
    linear_combination -h

/-- Actual two-order resolvent-kernel family identity, with the displayed
sign fixed by the operator -d²/dr²+exp(2r)+nu². -/
theorem actualGreen_composition {nu mu : ℝ}
    (hnu : 0 < nu) (hnuUpper : nu < 1)
    (hmu : 0 < mu) (hmuUpper : mu < 1) (hne : nu ≠ mu) (s t : ℝ) :
    (∫ r : ℝ, actualRadialGreen (nu : ℂ) s r *
      actualRadialGreen (mu : ℂ) r t) =
      (actualRadialGreen (nu : ℂ) s t - actualRadialGreen (mu : ℂ) s t) /
        ((mu : ℂ) ^ 2 - (nu : ℂ) ^ 2) := by
  have hdenReal : mu ^ 2 - nu ^ 2 ≠ 0 := by
    intro h
    have hsum : 0 < mu + nu := add_pos hmu hnu
    have hsq : mu ^ 2 = nu ^ 2 := sub_eq_zero.mp h
    have hz : (mu - nu) * (mu + nu) = 0 := by nlinarith [hsq]
    have hzSub : mu - nu = 0 :=
      (mul_eq_zero.mp hz).resolve_right (ne_of_gt hsum)
    exact hne (sub_eq_zero.mp hzSub).symm
  have hden : (mu : ℂ) ^ 2 - (nu : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast hdenReal
  apply (eq_div_iff hden).mpr
  simpa only [mul_comm] using actualGreen_composition_mul hnu hnuUpper hmu hmuUpper s t

end
end ImbalancedChen.Part3.ActualGreenComposition20261025a
