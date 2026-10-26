import ImbalancedChen.Part3StrictInfinityHighIndicator
import ImbalancedChen.Part3StrictHighStripCanonicalMeasure

/-! True strict infinity high-neighborhood quotient normalization,
including Y=1. Weighted actual parabolic unfolding derives the measure
pushforward; its mass and L1/integral transport are then consequences.
No measure-preserving cusp embedding is a premise.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ActualHighCuspTail20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b
open ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b
open ImbalancedChen.Part3.StrictInfinityHighIndicator20261026b
open ImbalancedChen.Part3.StrictHighStripCanonicalMeasure20261026b
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz

namespace ImbalancedChen.Part3.ActualStrictInfinityTailMeasure20261026b

def weightedStrictSeed (N : ℕ) (Y : ℝ)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (z : UpperHalfPlane) : ℝ≥0∞ :=
  strictHighSeed Y z * W (orbitProjection N z)

private theorem weightedStrict_periodic (N : ℕ) (Y : ℝ)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) (k : ℤ) (z : UpperHalfPlane) :
    weightedStrictSeed N Y W (translate k z) = weightedStrictSeed N Y W z := by
  have hq := orbitProjection_smul N (translationGamma N k) z
  change orbitProjection N (translate k z) = orbitProjection N z at hq
  rw [weightedStrictSeed, weightedStrictSeed, strictHighSeed_periodic, hq]

private theorem weightedStrict_measurable (N : ℕ) (Y : ℝ)
    {W : Gamma0OrbitSpace N → ℝ≥0∞} (hW : Measurable W) :
    Measurable (weightedStrictSeed N Y W) :=
  (strictHighSeed_measurable Y).mul (hW.comp (orbitProjection_measurable N))

private theorem weightedStrict_poincare_ae (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (W : Gamma0OrbitSpace N → ℝ≥0∞) :
    parabolicNonnegativePoincare N (weightedStrictSeed N Y W) =ᵐ[carrierPushforward N]
      (fun q => (infinityHighNeighborhood N Y).indicator (fun _ => (1 : ℝ≥0∞)) q * W q) := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [parabolicNonnegativePoincare_projection]
  have htrace : parabolicTraceNN N (weightedStrictSeed N Y W) z =
      parabolicTraceNN N (strictHighSeed Y) z * W (orbitProjection N z) := by
    unfold parabolicTraceNN weightedStrictSeed
    simp_rw [orbitProjection_smul]
    exact ENNReal.tsum_mul_right
  rw [htrace, strict_trace_eq_geometric_indicator N Y hY z]

/-- Exact nonnegative transport on the ACTUAL strict geometric quotient
neighborhood, including the thresholdY=1. -/
theorem strict_infinity_tail_lintegral (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (W : Gamma0OrbitSpace N → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ q in infinityHighNeighborhood N Y, W q ∂carrierPushforward N) =
      ∫⁻ z in strictHighStrip Y, W (orbitProjection N z) := by
  calc
    _ = ∫⁻ q, (infinityHighNeighborhood N Y).indicator (fun _ => (1 : ℝ≥0∞)) q * W q
        ∂carrierPushforward N := by
      rw [← lintegral_indicator (infinityHighNeighborhood_measurable N Y hY)]
      apply lintegral_congr
      intro q
      by_cases hq : q ∈ infinityHighNeighborhood N Y <;> simp [hq]
    _ = ∫⁻ q, parabolicNonnegativePoincare N (weightedStrictSeed N Y W) q
        ∂carrierPushforward N := lintegral_congr_ae (weightedStrict_poincare_ae N Y hY W).symm
    _ = ∫⁻ z in strip, weightedStrictSeed N Y W z :=
      nonnegative_parabolic_quotient_unfolding N _ (weightedStrict_periodic N Y W)
        (weightedStrict_measurable N Y hW)
    _ = _ := by
      have hS : MeasurableSet (strictHeightHalfSpace Y) :=
        (isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet
      have hi : weightedStrictSeed N Y W =
          (strictHeightHalfSpace Y).indicator (fun z => W (orbitProjection N z)) := by
        funext z
        by_cases hz : Y < z.im <;>
          simp [weightedStrictSeed, strictHighSeed, strictHeightHalfSpace, hz]
      rw [hi, lintegral_indicator hS, Measure.restrict_restrict hS]
      have hs : strictHeightHalfSpace Y ∩ strip = strictHighStrip Y := Set.inter_comm _ _
      rw [hs]

/-- The actual width-one quotient pushforward, derived from unfolding;
injective set charts are NOT used as a measure-preservation assumption. -/
theorem strict_infinity_strip_map_measure (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) :
    ((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map (orbitProjection N) =
      (carrierPushforward N).restrict (infinityHighNeighborhood N Y) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (orbitProjection_measurable N) hS]
  have h := strict_infinity_tail_lintegral N Y hY
    (S.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hS)
  have hi : (fun z : UpperHalfPlane => S.indicator (fun _ => (1 : ℝ≥0∞)) (orbitProjection N z)) =
      (orbitProjection N ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) := rfl
  rw [hi, lintegral_indicator hS,
    lintegral_indicator ((orbitProjection_measurable N) hS)] at h
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using h.symm

theorem strict_infinity_tail_volume (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) :
    carrierPushforward N (infinityHighNeighborhood N Y) = ENNReal.ofReal (1 / Y) := by
  have hm := congrArg (fun μ : Measure (Gamma0OrbitSpace N) => μ Set.univ)
    (strict_infinity_strip_map_measure N Y hY)
  simp only [Measure.map_apply (orbitProjection_measurable N) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ] at hm
  exact hm.symm.trans (strictHighStrip_volume Y ((by norm_num : (0 : ℝ) < 1).trans_le hY))

theorem strict_infinity_tail_const_integrable (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) :
    IntegrableOn (fun _ : Gamma0OrbitSpace N => (1 : ℂ))
      (infinityHighNeighborhood N Y) (carrierPushforward N) := by
  apply integrableOn_const
  rw [strict_infinity_tail_volume N Y hY]
  exact ENNReal.ofReal_ne_top

/-- Genuine L1 equivalence on the tail, with the original quotient and
canonical strip measures. F is never assumed L1 on all ofH. -/
theorem strict_infinity_tail_integrable_iff (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F) :
    IntegrableOn F (infinityHighNeighborhood N Y) (carrierPushforward N) ↔
      IntegrableOn (fun z => F (orbitProjection N z)) (strictHighStrip Y) := by
  have hi : Integrable F
      (((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map (orbitProjection N)) ↔
      Integrable (fun z => F (orbitProjection N z))
        ((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)) :=
    integrable_map_measure hF.aestronglyMeasurable (orbitProjection_measurable N).aemeasurable
  rw [strict_infinity_strip_map_measure N Y hY] at hi
  exact hi

theorem strict_infinity_tail_integral (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F) :
    (∫ q in infinityHighNeighborhood N Y, F q ∂carrierPushforward N) =
      ∫ z in strictHighStrip Y, F (orbitProjection N z) := by
  have h : (∫ q, F q ∂(((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map
        (orbitProjection N))) = ∫ z in strictHighStrip Y, F (orbitProjection N z) :=
    integral_map (orbitProjection_measurable N).aemeasurable hF.aestronglyMeasurable
  rwa [strict_infinity_strip_map_measure N Y hY] at h

/-- Explicit real coordinate transport: x∈[0,1),y>Y, with canonical
dx times the original physical y^-2dy measure. -/
theorem strict_infinity_tail_coordinate_integral (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F) :
    (∫ q in infinityHighNeighborhood N Y, F q ∂carrierPushforward N) =
      ∫ p : ℝ × ℝ, chartPullback (fun z => F (orbitProjection N z)) p
        ∂(((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
          (verticalWeightedMeasure.restrict (Ioi Y))) := by
  rw [strict_infinity_tail_integral N Y hY F hF]
  have h := chartMap_measurableEmbedding.integral_map
    (μ := (volume : Measure UpperHalfPlane).restrict (strictHighStrip Y))
    (g := chartPullback (fun z => F (orbitProjection N z)))
  rw [strictHighStrip_chart_map_measure Y] at h
  simpa only [chartMap, chartPullback_at_upper] using h.symm

end ImbalancedChen.Part3.ActualStrictInfinityTailMeasure20261026b
