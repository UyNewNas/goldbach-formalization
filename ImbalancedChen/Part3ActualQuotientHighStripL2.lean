import ImbalancedChen.Part3ActualPoincareSpectralCoefficient
import ImbalancedChen.Part3Gamma0ActualHighCuspTail
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
Actual quotient L2 restricts to the literal width-one high cusp strip.
The norm bound is proved by true nonnegative parabolic unfolding and the
proved uniqueness of an actual coset entering the high cusp. No quotient
embedding, trace L2, or overlap bound is a hypothesis. Canonical hyperbolic
volume and the actual canonical quotient measure retain their normalization.
-/

namespace ImbalancedChen.Part3.ActualQuotientHighStripL220261026a
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open ActualPoincareSpectralCoefficient20261026a
open Gamma0ActualHighCuspTail20261025a GammaInfinityTranslationStrip20261025a
open Gamma0ParabolicEffectiveDecomposition20261025a Gamma0ActualParabolicUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a

def actualHighStrip (Y : ℝ) : Set UpperHalfPlane := {z | Y < z.im} ∩ strip

theorem actualHighStrip_measurable (Y : ℝ) : MeasurableSet (actualHighStrip Y) :=
  (UpperHalfPlane.continuous_im.measurable measurableSet_Ioi).inter strip_measurable

def highNormSeed (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (Y : ℝ)
    (z : UpperHalfPlane) : ℝ≥0∞ :=
  strictHighSeed Y z * ENNReal.ofReal (‖testLift N U z‖^2)

theorem highNormSeed_measurable (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) (Y : ℝ) : Measurable (highNormSeed N U Y) :=
  (measurable_const.indicator (UpperHalfPlane.continuous_im.measurable measurableSet_Ioi)).mul
    (hU.norm.pow 2).measurable.ennreal_ofReal

theorem highNormSeed_periodic (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (Y : ℝ)
    (k : ℤ) (z : UpperHalfPlane) : highNormSeed N U Y (translate k z) = highNormSeed N U Y z := by
  have him : (translate k z).im = z.im := by
    rw [translate_eq_vadd, UpperHalfPlane.vadd_im]
  simp only [highNormSeed, strictHighSeed, Set.indicator, mem_setOf_eq, him, testLift_periodic]

theorem highNormSeed_trace (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (Y : ℝ)
    (z : UpperHalfPlane) :
    parabolicTraceNN N (highNormSeed N U Y) z =
      parabolicTraceNN N (strictHighSeed Y) z * ENNReal.ofReal (‖testLift N U z‖^2) := by
  unfold parabolicTraceNN highNormSeed
  simp_rw [testLift_invariant]
  exact ENNReal.tsum_mul_right

/-- The real geometric uniqueness theorem, with the central sign counted once,
is precisely what makes the restriction a contraction. -/
theorem highNormSeed_trace_le (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (Y : ℝ)
    (hY : 1 ≤ Y) (z : UpperHalfPlane) :
    parabolicTraceNN N (highNormSeed N U Y) z ≤ ENNReal.ofReal (‖testLift N U z‖^2) := by
  rw [highNormSeed_trace]
  rcases strictHighTrace_zero_or_one N Y hY z with hz | hz <;> simp [hz]

theorem highNormSeed_strip_integral (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (Y : ℝ) :
    (∫⁻ z in strip, highNormSeed N U Y z) =
      ∫⁻ z in actualHighStrip Y, ENNReal.ofReal (‖testLift N U z‖^2) := by
  have heq : highNormSeed N U Y = {z : UpperHalfPlane | Y < z.im}.indicator
      (fun z => ENNReal.ofReal (‖testLift N U z‖^2)) := by
    funext z
    by_cases hz : Y < z.im <;> simp [highNormSeed, strictHighSeed, hz]
  rw [heq, lintegral_indicator (UpperHalfPlane.continuous_im.measurable measurableSet_Ioi),
    Measure.restrict_restrict (UpperHalfPlane.continuous_im.measurable measurableSet_Ioi)]
  rfl

theorem quotient_norm_mass_eq_carrier (N : ℕ) [NeZero N] (U : Gamma0OrbitSpace N → ℂ) :
    (∫⁻ q, ENNReal.ofReal (‖U q‖^2) ∂carrierPushforward N) =
      ∫⁻ z in reducedCarrier N, ENNReal.ofReal (‖testLift N U z‖^2) := by
  rw [← reducedProjection_map_measure N,
    (reducedProjection_measurableEmbedding N).lintegral_map]
  exact lintegral_subtype_comap (reducedCarrier_measurable N) _

/-- Actual geometric norm restriction, independent of any Maass PDE. -/
theorem actual_quotient_high_strip_energy_le (N : ℕ) [NeZero N]
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U))
    (Y : ℝ) (hY : 1 ≤ Y) :
    (∫⁻ z in actualHighStrip Y, ENNReal.ofReal (‖testLift N U z‖^2)) ≤
      ∫⁻ q, ENNReal.ofReal (‖U q‖^2) ∂carrierPushforward N := by
  rw [← highNormSeed_strip_integral, ← nonnegative_parabolic_carrier_unfolding N _
    (highNormSeed_periodic N U Y) (highNormSeed_measurable N U hU Y),
    quotient_norm_mass_eq_carrier]
  exact lintegral_mono (highNormSeed_trace_le N U Y hY)

/-- True quotient L2 supplies true spatial-strip square integrability.
No coefficient-energy or Bessel-tail premise is introduced. -/
theorem actual_quotient_high_strip_sq_integrable (N : ℕ) [NeZero N]
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U))
    (hU2 : MemLp U 2 (carrierPushforward N)) (Y : ℝ) (hY : 1 ≤ Y) :
    IntegrableOn (fun z => ‖testLift N U z‖^2) (actualHighStrip Y) := by
  have hsq := (memLp_two_iff_integrable_sq_norm hU2.aestronglyMeasurable).mp hU2
  have hfinite : (∫⁻ q, ENNReal.ofReal (‖U q‖^2) ∂carrierPushforward N) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg (‖U q‖)))).mp
      hsq.hasFiniteIntegral
  refine ⟨(hU.norm.pow 2).aestronglyMeasurable.restrict, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun z => sq_nonneg (‖testLift N U z‖)))).mpr
  exact (actual_quotient_high_strip_energy_le N U hU Y hY).trans_lt hfinite

theorem actual_quotient_high_strip_memLp (N : ℕ) [NeZero N]
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U))
    (hU2 : MemLp U 2 (carrierPushforward N)) (Y : ℝ) (hY : 1 ≤ Y) :
    MemLp (testLift N U) 2 ((volume : Measure UpperHalfPlane).restrict (actualHighStrip Y)) :=
  (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable.restrict).mpr
    (actual_quotient_high_strip_sq_integrable N U hU hU2 Y hY)

end
end ImbalancedChen.Part3.ActualQuotientHighStripL220261026a
