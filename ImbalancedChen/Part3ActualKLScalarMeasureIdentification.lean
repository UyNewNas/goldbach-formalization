import ImbalancedChen.Part3ActualRadialCompactScalarStone
import ImbalancedChen.Part3ActualKLCompactDensityMeasure
import ImbalancedChen.Part3HalfEndpointPositiveMeasureUniqueness
import ImbalancedChen.Part3ActualStoneSqrtPathUniform

/-!
# Identification of the actual compact-test radial spectral measure

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Both limits are already actual: the native form resolvent satisfies Stone's
half-endpoint theorem, and its literal I/K Green pairing has the proved
sqrt-path boundary integral.  Their equality holds on one eventual epsilon
event uniformly over the entire positive spectral interval.  Half-atoms
are retained until the shrinking-interval argument eliminates them.
No density, atomlessness, boundary exchange or spectral identification is
assumed for the native measure.
-/

namespace ImbalancedChen.Part3.ActualKLScalarMeasureIdentification20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RadialSchrodingerL2Form20261025a
open ActualRadialCompactScalarStone20261025a ActualKLCompactDensityMeasure20261025a
open ActualGreenPairingHolomorphy20261025a ActualGreenResolventContinuation20261025a
open ActualGreenStoneBoundaryIntegral20261025a ActualStoneSqrtPath20261025a
open HalfEndpointPositiveMeasureUniqueness20261025a

private theorem normalized_conjugate_difference (w : ℂ) :
    (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (w - star w) =
      (((1 / Real.pi) * w.im : ℝ) : ℂ) := by
  rw [Complex.sub_conj]
  push_cast
  field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  <;> ring

/-- The positive-real sqrt paths lie in the actual continued Green strip,
so their difference is exactly the native diagonal imaginary part. -/
theorem normalizedStonePairJump_eq_native_imaginary
    (F : RadialTest) {x eps : ℝ} (hx : 0 < x)
    (hp : 0 < (nuPlus x eps).re) (hpUpper : (nuPlus x eps).re < 1)
    (hm : 0 < (nuMinus x eps).re) (hmUpper : (nuMinus x eps).re < 1) :
    normalizedStonePairJump F.function x eps =
      (((1 / Real.pi) *
        (radialDiagonalMoment (radialCoreL2 F) (zPlus x eps)).im : ℝ) : ℂ) := by
  have hplus := actualGreenPairing_eq_same_native_order_resolvent F F hp hpUpper
  have hminus := actualGreenPairing_eq_same_native_order_resolvent F F hm hmUpper
  change actualGreenPairing F.function (fun r => star (F.function r)) (nuPlus x eps) =
    radialDiagonalMoment (radialCoreL2 F) (-((nuPlus x eps) ^ 2)) at hplus
  change actualGreenPairing F.function (fun r => star (F.function r)) (nuMinus x eps) =
    radialDiagonalMoment (radialCoreL2 F) (-((nuMinus x eps) ^ 2)) at hminus
  rw [neg_nuPlus_sq hx eps] at hplus
  rw [neg_nuMinus_sq hx eps] at hminus
  have hz : zMinus x eps = star (zPlus x eps) := by simp [zPlus, zMinus]
  unfold normalizedStonePairJump
  rw [hplus, hminus, hz, radialDiagonalMoment_conjugate]
  exact normalized_conjugate_difference _

/-- One epsilon event works for every x in [a,b]; no pointwise-dependent
choice is smuggled through the spectral interval integral. -/
theorem eventually_actualBoundaryIntegral_eq_nativeStone
    (F : RadialTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ᶠ eps : ℝ in 𝓝[>] 0,
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
        (∫ x in a..b,
          actualGreenPairing F.function (fun r => star (F.function r)) (nuPlus x eps) -
            actualGreenPairing F.function (fun r => star (F.function r)) (nuMinus x eps)) =
      (radialCompactStoneInterval F a b eps : ℂ) := by
  filter_upwards [eventually_uniform_orderRange (B := b) ha] with eps heps
  calc
    _ = ∫ x in a..b, normalizedStonePairJump F.function x eps := by
      simp only [normalizedStonePairJump, intervalIntegral.integral_const_mul]
    _ = ∫ x in a..b, ((((1 / Real.pi) *
        (radialDiagonalMoment (radialCoreL2 F) (zPlus x eps)).im : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxab : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hx
      have h := heps x hxab
      exact normalizedStonePairJump_eq_native_imaginary F (ha.trans_le hxab.1)
        h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    _ = _ := by
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
      rfl

/-- Comparison of two proved limits gives Stone's half-endpoint mass as
the literal KL lambda-density integral.  Endpoint atoms remain visible. -/
theorem actual_compact_half_endpoint_density (F : RadialTest)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (compactRadialScalarMeasure F).real (Ioo a b) +
        ((compactRadialScalarMeasure F).real {a} +
          (compactRadialScalarMeasure F).real {b}) / 2 =
      (compactKLDensityMeasure F).real (Ioo a b) := by
  have hStone := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (compactRadialScalarMeasure_Stone_interval F hab)
  have hBoundary := actualGreenPairing_Stone_interval_tendsto ha hab.le
    F.smooth.continuous F.compact
  have hNative : Tendsto
      (fun eps : ℝ => (radialCompactStoneInterval F a b eps : ℂ))
      (𝓝[>] 0)
      (𝓝 ((∫ x in a..b, compactLambdaDensity F x : ℝ) : ℂ)) := by
    apply hBoundary.congr'
    exact eventually_actualBoundaryIntegral_eq_nativeStone F ha hab.le
  have heq := tendsto_nhds_unique hStone hNative
  have hreal := congrArg Complex.re heq
  simp only [Complex.ofReal_re] at hreal
  rw [compactKLDensityMeasure_real_Ioo F ha hab.le]
  exact hreal

/-- Positive native spectral atoms vanish as a conclusion of the actual
half-endpoint identity, rather than being dropped in the Stone caller. -/
theorem compactRadialScalarMeasure_positive_atom (F : RadialTest)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    compactRadialScalarMeasure F ({lambda} : Set ℝ) = 0 := by
  exact positive_atom_zero_of_half_interval
    (compactRadialScalarMeasure F) (compactKLDensityMeasure F)
    (fun a b ha hab => actual_compact_half_endpoint_density F ha hab) hlambda

/-- Actual spectral identification: the native radial scalar measure of
every compact smooth test is the literal K-transform-square density. -/
theorem compactRadialScalarMeasure_eq_actual_KL_density (F : RadialTest) :
    compactRadialScalarMeasure F = compactKLDensityMeasure F := by
  exact positive_measure_eq_of_half_interval
    (compactRadialScalarMeasure F) (compactKLDensityMeasure F)
    (compactRadialScalarMeasure_nonpositive_mass F)
    (compactKLDensityMeasure_nonpositive F)
    (compactKLDensityMeasure_singleton F)
    (fun a b ha hab => actual_compact_half_endpoint_density F ha hab)

end
end ImbalancedChen.Part3.ActualKLScalarMeasureIdentification20261025a
