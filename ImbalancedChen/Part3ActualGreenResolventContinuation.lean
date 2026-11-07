import ImbalancedChen.Part3ActualGreenPairingHolomorphy
import ImbalancedChen.Part3ActualOrderResolventHolomorphy
import ImbalancedChen.Part3ActualGreenSmoothFormInverse
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Topology

/-!
# Actual I/K Green pairing equals the same native complex resolvent

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The positive real-order anchor is the actual smooth-forcing Green/form
identity and the proved kappa-to-one native form-domain shift bridge.
Both sides are independently proved analytic on the ONE connected interior
strip. Real orders accumulating at 1/2 therefore give the complex equality.
No hEquality, kernel analyticity, normal convergence, abstract form-domain
identification or shift law is assumed. No boundary/Stone result is asserted.
-/

namespace ImbalancedChen.Part3.ActualGreenResolventContinuation20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ActualGreenCompactOrderMajorant20261025a ActualGreenPairingHolomorphy20261025a
open ActualOrderResolventHolomorphy20261025a RadialSchrodingerL2Form20261025a
open ActualGreenCompactForcing20261025a ActualGreenSmoothFormInverse20261025a

theorem isPreconnected_interiorOrderStrip : IsPreconnected interiorOrderStrip := by
  have hc : Convex ℝ interiorOrderStrip :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage Complex.reCLM.toLinearMap
  exact hc.isPreconnected

/-- The real anchor is proved for every actual compact smooth forcing,
using the same native operator as the complex CFC family. -/
theorem actualGreenPairing_eq_native_real_order
    (F G : RadialTest) {kappa : ℝ} (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) :
    actualGreenPairing F.function (fun r => star (G.function r)) (kappa : ℂ) =
      inner ℂ (radialCoreL2 G) (actualRadialOrderResolvent (kappa : ℂ) (radialCoreL2 F)) := by
  have hi : -1 < (kappa : ℂ).re := by simpa only [Complex.ofReal_re] using
    (show -1 < kappa by linarith only [hkappa])
  have hGcont : Continuous (fun r => star (G.function r)) := G.smooth.continuous.star
  have hGcompact : HasCompactSupport (fun r => star (G.function r)) :=
    G.compact.comp_left (star_zero ℂ)
  rw [actualGreenPairing_eq_greenForcing hi F.smooth.continuous hGcont F.compact hGcompact]
  have hop : actualRadialOrderResolvent (kappa : ℂ) = radialShiftedVariationalInverse kappa :=
    actualRadialComplexResolvent_neg_kappa_sq kappa hkappa
  rw [hop, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actualGreen_eq_form_inverse_smooth hkappa hkappaUpper F,
    G.function_memLp.coeFn_toLp] with r hF hG
  change greenForcing (kappa : ℂ) F.function r * star (G.function r) =
    inner ℂ (radialCoreL2 G r) (radialShiftedVariationalInverse kappa (radialCoreL2 F) r)
  change (G.function_memLp.toLp G.function : ℝ → ℂ) r = G.function r at hG
  rw [hF, hG, RCLike.inner_apply']
  ring

/-- Interior complex-order continuation of the actual double integral.
The only inputs are the actual compact smooth tests and the order itself. -/
theorem actualGreenPairing_eq_same_native_order_resolvent
    (F G : RadialTest) {nu : ℂ} (hnu : 0 < nu.re) (hnuUpper : nu.re < 1) :
    actualGreenPairing F.function (fun r => star (G.function r)) nu =
      inner ℂ (radialCoreL2 G) (actualRadialOrderResolvent nu (radialCoreL2 F)) := by
  let f : ℂ → ℂ := actualGreenPairing F.function (fun r => star (G.function r))
  let g : ℂ → ℂ := fun z =>
    inner ℂ (radialCoreL2 G) (actualRadialOrderResolvent z (radialCoreL2 F))
  have hf : AnalyticOnNhd ℂ f interiorOrderStrip :=
    analyticOnNhd_actualGreenPairing F.smooth.continuous G.smooth.continuous.star
      F.compact (G.compact.comp_left (star_zero ℂ))
  have hg : AnalyticOnNhd ℂ g interiorOrderStrip :=
    (analyticOnNhd_actualRadialOrder_pairing (radialCoreL2 F) (radialCoreL2 G)).mono
      (fun _ hz => hz.1)
  let u : ℕ → ℂ := fun n => (((1 / 2 : ℝ) + 1 / ((n : ℝ) + 3) : ℝ) : ℂ)
  have hden (n : ℕ) : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hsmall (n : ℕ) : 1 / ((n : ℝ) + 3) ≤ (1 / 3 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by have := Nat.cast_nonneg n; linarith)
  have hu0 (n : ℕ) : (0 : ℝ) < (1 / 2 : ℝ) + 1 / ((n : ℝ) + 3) := by
    have hh := one_div_pos.mpr (hden n)
    linarith only [hh]
  have hu1 (n : ℕ) : (1 / 2 : ℝ) + 1 / ((n : ℝ) + 3) < 1 := by
    linarith only [hsmall n]
  have huneq (n : ℕ) : u n ≠ ((1 / 2 : ℝ) : ℂ) := by
    intro heq
    have hh := congrArg Complex.re heq
    simp only [u, Complex.ofReal_re] at hh
    have hp := one_div_pos.mpr (hden n)
    linarith only [hh, hp]
  have huEq (n : ℕ) : f (u n) = g (u n) :=
    actualGreenPairing_eq_native_real_order F G (hu0 n) (hu1 n)
  have hrealLimit : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + 1 / ((n : ℝ) + 3))
      atTop (nhds (1 / 2 : ℝ)) := by
    have h := ((tendsto_natCast_atTop_atTop.add_const 3).const_div_atTop (1 : ℝ)).const_add
      (1 / 2 : ℝ)
    simpa only [add_zero] using h
  have hlimit : Tendsto u atTop (nhds (((1 / 2 : ℝ) : ℂ))) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hrealLimit
  have hclosure : ((1 / 2 : ℝ) : ℂ) ∈ closure ({z : ℂ | f z = g z} \ {((1 / 2 : ℝ) : ℂ)}) := by
    apply mem_closure_of_tendsto hlimit
    exact Eventually.of_forall (fun n => ⟨huEq n, by simpa only [mem_singleton_iff] using huneq n⟩)
  have hbase : ((1 / 2 : ℝ) : ℂ) ∈ interiorOrderStrip := by
    norm_num [interiorOrderStrip]
  exact hf.eqOn_of_preconnected_of_mem_closure hg isPreconnected_interiorOrderStrip
    hbase hclosure ⟨hnu, hnuUpper⟩

/-- The literal iterated Green convolution/test integral has the same
complex-order native-resolvent value. This is a matrix-element identity;
no unproved global complex-kernel L2 bound is inferred from it. -/
theorem greenForcing_pairing_eq_same_native_order_resolvent
    (F G : RadialTest) {nu : ℂ} (hnu : 0 < nu.re) (hnuUpper : nu.re < 1) :
    (∫ r : ℝ, greenForcing nu F.function r * star (G.function r)) =
      inner ℂ (radialCoreL2 G) (actualRadialOrderResolvent nu (radialCoreL2 F)) := by
  have hi : -1 < nu.re := by linarith only [hnu]
  rw [← actualGreenPairing_eq_greenForcing hi F.smooth.continuous G.smooth.continuous.star
    F.compact (G.compact.comp_left (star_zero ℂ))]
  exact actualGreenPairing_eq_same_native_order_resolvent F G hnu hnuUpper

end
end ImbalancedChen.Part3.ActualGreenResolventContinuation20261025a
