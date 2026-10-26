import ImbalancedChen.Part3Gamma0ActualHighCuspTail
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The true width-one infinity high strip pushes forward to the restriction
of the actual Gamma quotient measure to its genuine single-cusp tail.
This weighted statement extends the existing tail MASS theorem using
actual parabolic unfolding and the proved high-coset 0/1 multiplicity.
It supplies arbitrary quotient Lp and representative-AE transport on this
one high cusp. It asserts neither an all-cusps decomposition nor an
infinite low-height strip estimate or an automorphic spectral expansion.
-/
namespace ImbalancedChen.Part3.ActualInfinityHighTailMeasureTransport20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a
open GammaInfinityTranslationStrip20261025a
open Gamma0ParabolicCosetRows20261025a
open Gamma0ActualParabolicUnfolding20261025a
open Gamma0ActualHighCuspTail20261025a
open ActualCuspStripCutoff20261025a

def weightedHighSeed (N : ℕ) (Y : ℝ)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (z : UpperHalfPlane) : ℝ≥0∞ :=
  highSeed Y z * W (orbitProjection N z)

theorem weightedHighSeed_measurable (N : ℕ) (Y : ℝ)
    {W : Gamma0OrbitSpace N → ℝ≥0∞} (hW : Measurable W) :
    Measurable (weightedHighSeed N Y W) :=
  (highSeed_measurable Y).mul (hW.comp (orbitProjection_measurable N))

theorem weightedHighSeed_periodic (N : ℕ) (Y : ℝ)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (k : ℤ) (z : UpperHalfPlane) :
    weightedHighSeed N Y W (translate k z) = weightedHighSeed N Y W z := by
  have hq := orbitProjection_smul N
    (⟨ModularGroup.T ^ k, translation_mem_gamma0 N k⟩ : CongruenceSubgroup.Gamma0 N) z
  change orbitProjection N (translate k z) = orbitProjection N z at hq
  rw [weightedHighSeed, weightedHighSeed, highSeed_periodic, hq]

/-- The actual quotient observable factors through the actual parabolic
trace; no integrability or overlap-count hypothesis is imposed. -/
theorem weightedHighSeed_trace (N : ℕ) (Y : ℝ)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (z : UpperHalfPlane) :
    parabolicTraceNN N (weightedHighSeed N Y W) z =
      parabolicTraceNN N (highSeed Y) z * W (orbitProjection N z) := by
  unfold parabolicTraceNN weightedHighSeed
  simp_rw [orbitProjection_smul]
  exact ENNReal.tsum_mul_right

theorem weightedHighSeed_quotient_ae (N : ℕ) [NeZero N] (Y : ℝ)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) :
    parabolicNonnegativePoincare N (weightedHighSeed N Y W) =ᵐ[carrierPushforward N]
      fun q => quotientHighIndicator N Y q * W q := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [parabolicNonnegativePoincare_projection, weightedHighSeed_trace,
    quotientHighIndicator, parabolicNonnegativePoincare_projection]
  rfl

/-- Exact weighted tail identity for every nonnegative measurable
observable on the original quotient, retaining the original volume. -/
theorem actual_infinity_high_tail_lintegral (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) (W : Gamma0OrbitSpace N → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ q in quotientHighTail N Y, W q ∂carrierPushforward N) =
      ∫⁻ z in highWidthStrip 1 Y, W (orbitProjection N z) := by
  calc
    _ = ∫⁻ q, quotientHighIndicator N Y q * W q ∂carrierPushforward N := by
      rw [quotientHighIndicator_eq_indicator N Y hY,
        ← lintegral_indicator (quotientHighTail_measurable N Y)]
      apply lintegral_congr
      intro q
      by_cases hq : q ∈ quotientHighTail N Y <;> simp [hq]
    _ = ∫⁻ q, parabolicNonnegativePoincare N (weightedHighSeed N Y W) q
        ∂carrierPushforward N :=
      lintegral_congr_ae (weightedHighSeed_quotient_ae N Y W).symm
    _ = ∫⁻ z in strip, weightedHighSeed N Y W z :=
      nonnegative_parabolic_quotient_unfolding N _
        (weightedHighSeed_periodic N Y W) (weightedHighSeed_measurable N Y hW)
    _ = _ := by
      have hi : weightedHighSeed N Y W =
          (highRegion Y).indicator (fun z => W (orbitProjection N z)) := by
        funext z
        by_cases hz : z ∈ highRegion Y <;> simp [weightedHighSeed, highSeed, hz]
      rw [hi, lintegral_indicator (highRegion_measurable Y),
        Measure.restrict_restrict (highRegion_measurable Y)]
      have hs : highRegion Y ∩ strip = highWidthStrip 1 Y := by
        ext z
        simp only [highRegion, strip, highWidthStrip, widthStrip,
          mem_inter_iff, mem_setOf_eq]
        tauto
      rw [hs]

/-- The single ACTUAL high cusp has multiplicity exactly one as a
measure statement, not merely a total-volume comparison. -/
theorem actual_infinity_high_strip_map_measure (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) :
    ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)).map (orbitProjection N) =
      (carrierPushforward N).restrict (quotientHighTail N Y) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (orbitProjection_measurable N) hS]
  have h := actual_infinity_high_tail_lintegral N hY
    (S.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hS)
  have hi : (fun z : UpperHalfPlane => S.indicator (fun _ => (1 : ℝ≥0∞)) (orbitProjection N z)) =
      (orbitProjection N ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    rfl
  rw [hi, lintegral_indicator hS,
    lintegral_indicator ((orbitProjection_measurable N) hS)] at h
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using h.symm

theorem actual_infinity_high_strip_quasiMeasurePreserving (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) :
    QuasiMeasurePreserving (orbitProjection N)
      ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y))
      (carrierPushforward N) := by
  refine ⟨orbitProjection_measurable N, ?_⟩
  rw [actual_infinity_high_strip_map_measure N hY]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

/-- Arbitrary quotient Lp representatives now pull back to this whole
high infinity strip, without continuity or a low-height strip claim. -/
theorem quotient_memLp_actual_infinity_high_strip (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) {p : ℝ≥0∞} {F : Gamma0OrbitSpace N → ℂ}
    (hF : MemLp F p (carrierPushforward N)) :
    MemLp (fun z => F (orbitProjection N z)) p
      ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)) := by
  have hm : MemLp F p
      (((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)).map (orbitProjection N)) := by
    rw [actual_infinity_high_strip_map_measure N hY]
    exact MemLp.mono_measure Measure.restrict_le_self hF
  exact hm.comp_of_map (orbitProjection_measurable N).aemeasurable

theorem quotient_ae_eq_actual_infinity_high_strip (N : ℕ) [NeZero N]
    {Y : ℝ} (hY : 1 < Y) {F G : Gamma0OrbitSpace N → ℂ}
    (hFG : F =ᵐ[carrierPushforward N] G) :
    (fun z => F (orbitProjection N z)) =ᵐ[
      (volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)]
      (fun z => G (orbitProjection N z)) :=
  (actual_infinity_high_strip_quasiMeasurePreserving N hY).ae_eq hFG

end
end ImbalancedChen.Part3.ActualInfinityHighTailMeasureTransport20261026b
