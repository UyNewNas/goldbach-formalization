import ImbalancedChen.Part3ActualStrictInfinityTailMeasure
import ImbalancedChen.Part3ActualFrickeQuotientMeasure

/-! Native zero-cusp strict-tail normalization, transported through the
EXISTING proved canonical quotient Fricke measure. The full global measure
theorem is consumed, not re-proved from whole-H volume. Each cusp has mass
1/Y and their proved disjoint union has mass2/Y forY>=1.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b
open ImbalancedChen.Part3.StrictInfinityHighIndicator20261026b
open ImbalancedChen.Part3.StrictHighStripCanonicalMeasure20261026b
open ImbalancedChen.Part3.ActualStrictInfinityTailMeasure20261026b
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz

namespace ImbalancedChen.Part3.ActualStrictZeroTailMeasure20261026b

theorem zeroHighNeighborhood_eq_fricke_preimage (p : ℕ) (hp : p.Prime) (Y : ℝ) :
    zeroHighNeighborhood p hp Y =
      quotientFricke p hp.pos ⁻¹' infinityHighNeighborhood p Y := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    change quotientFricke p hp.pos (orbitProjection p (frickeSL p hp.pos • z)) ∈
      infinityHighNeighborhood p Y
    rw [quotientFricke_projection, frickeSL_action_involutive p hp.pos]
    exact ⟨z, hz, rfl⟩
  · intro hq
    obtain ⟨z, hz, he⟩ := hq
    refine ⟨z, hz, ?_⟩
    have h := congrArg (quotientFricke p hp.pos) he
    simpa only [quotientFricke_projection, quotientFricke_involutive p hp.pos] using h

theorem infinityHighNeighborhood_eq_fricke_preimage (p : ℕ) (hp : p.Prime) (Y : ℝ) :
    infinityHighNeighborhood p Y = quotientFricke p hp.pos ⁻¹' zeroHighNeighborhood p hp Y := by
  rw [zeroHighNeighborhood_eq_fricke_preimage p hp Y]
  ext q
  change (q ∈ infinityHighNeighborhood p Y) ↔
    (quotientFricke p hp.pos (quotientFricke p hp.pos q) ∈ infinityHighNeighborhood p Y)
  rw [quotientFricke_involutive p hp.pos]

theorem zeroHighNeighborhood_measurable (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    MeasurableSet (zeroHighNeighborhood p hp Y) := by
  rw [zeroHighNeighborhood_eq_fricke_preimage p hp Y]
  exact (infinityHighNeighborhood_measurable p Y hY).preimage (quotientFricke_measurable p hp.pos)

/-- Restriction transport follows from the valid global quotient measure
supplier and the actual geometric neighborhood preimage identity. -/
theorem fricke_restricted_tail_map (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    ((carrierPushforward p).restrict (infinityHighNeighborhood p Y)).map (quotientFricke p hp.pos) =
      (carrierPushforward p).restrict (zeroHighNeighborhood p hp Y) := by
  rw [infinityHighNeighborhood_eq_fricke_preimage p hp Y,
    ← Measure.restrict_map (quotientFricke_measurable p hp.pos)
      (zeroHighNeighborhood_measurable p hp Y hY), quotientFricke_map_measure p hp.pos]

/-- Actual normalized zero-chart strip pushforward, with the canonical
quotient restriction derived rather than assumed. -/
theorem strict_zero_strip_map_measure (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    ((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map
        (fun z => orbitProjection p (frickeSL p hp.pos • z)) =
      (carrierPushforward p).restrict (zeroHighNeighborhood p hp Y) := by
  have he : (fun z : UpperHalfPlane => orbitProjection p (frickeSL p hp.pos • z)) =
      quotientFricke p hp.pos ∘ orbitProjection p := rfl
  rw [he, ← Measure.map_map (quotientFricke_measurable p hp.pos) (orbitProjection_measurable p),
    strict_infinity_strip_map_measure p Y hY, fricke_restricted_tail_map p hp Y hY]

theorem strict_zero_tail_volume (p : ℕ) [NeZero p] (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    carrierPushforward p (zeroHighNeighborhood p hp Y) = ENNReal.ofReal (1 / Y) := by
  have hmap : Measurable (fun z : UpperHalfPlane => orbitProjection p (frickeSL p hp.pos • z)) :=
    (orbitProjection_measurable p).comp (continuous_const_smul (frickeSL p hp.pos)).measurable
  have hm := congrArg (fun μ : Measure (Gamma0OrbitSpace p) => μ Set.univ)
    (strict_zero_strip_map_measure p hp Y hY)
  simp only [Measure.map_apply hmap MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ] at hm
  exact hm.symm.trans (strictHighStrip_volume Y ((by norm_num : (0 : ℝ) < 1).trans_le hY))

theorem strict_zero_tail_const_integrable (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    IntegrableOn (fun _ : Gamma0OrbitSpace p => (1 : ℂ))
      (zeroHighNeighborhood p hp Y) (carrierPushforward p) := by
  apply integrableOn_const
  rw [strict_zero_tail_volume p hp Y hY]
  exact ENNReal.ofReal_ne_top

theorem strict_zero_tail_integrable_iff (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F) :
    IntegrableOn F (zeroHighNeighborhood p hp Y) (carrierPushforward p) ↔
      IntegrableOn (fun z => F (orbitProjection p (frickeSL p hp.pos • z))) (strictHighStrip Y) := by
  have hmap : Measurable (fun z : UpperHalfPlane => orbitProjection p (frickeSL p hp.pos • z)) :=
    (orbitProjection_measurable p).comp (continuous_const_smul (frickeSL p hp.pos)).measurable
  have hi : Integrable F (((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map
      (fun z => orbitProjection p (frickeSL p hp.pos • z))) ↔
      Integrable (fun z => F (orbitProjection p (frickeSL p hp.pos • z)))
        ((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)) :=
    integrable_map_measure hF.aestronglyMeasurable hmap.aemeasurable
  rw [strict_zero_strip_map_measure p hp Y hY] at hi
  exact hi

theorem strict_zero_tail_integral (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F) :
    (∫ q in zeroHighNeighborhood p hp Y, F q ∂carrierPushforward p) =
      ∫ z in strictHighStrip Y, F (orbitProjection p (frickeSL p hp.pos • z)) := by
  have hmap : Measurable (fun z : UpperHalfPlane => orbitProjection p (frickeSL p hp.pos • z)) :=
    (orbitProjection_measurable p).comp (continuous_const_smul (frickeSL p hp.pos)).measurable
  have h : (∫ q, F q ∂(((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map
      (fun z => orbitProjection p (frickeSL p hp.pos • z)))) =
      ∫ z in strictHighStrip Y, F (orbitProjection p (frickeSL p hp.pos • z)) :=
    integral_map hmap.aemeasurable hF.aestronglyMeasurable
  rwa [strict_zero_strip_map_measure p hp Y hY] at h

theorem strict_zero_tail_coordinate_integral (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F) :
    (∫ q in zeroHighNeighborhood p hp Y, F q ∂carrierPushforward p) =
      ∫ v : ℝ × ℝ, chartPullback (fun z => F (orbitProjection p (frickeSL p hp.pos • z))) v
        ∂(((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
          (verticalWeightedMeasure.restrict (Ioi Y))) := by
  rw [strict_zero_tail_integral p hp Y hY F hF]
  have h := chartMap_measurableEmbedding.integral_map
    (μ := (volume : Measure UpperHalfPlane).restrict (strictHighStrip Y))
    (g := chartPullback (fun z => F (orbitProjection p (frickeSL p hp.pos • z))))
  rw [strictHighStrip_chart_map_measure Y] at h
  simpa only [chartMap, chartPullback_at_upper] using h.symm

/-- The literal disjoint two-cusp high union has exactly the two width-one
tail masses; no index-scaled mass or spectral density is substituted. -/
theorem two_cusp_high_union_volume (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    carrierPushforward p (infinityHighNeighborhood p Y ∪ zeroHighNeighborhood p hp Y) =
      ENNReal.ofReal (2 / Y) := by
  rw [measure_union (prime_high_neighborhoods_disjoint hp Y hY)
    (zeroHighNeighborhood_measurable p hp Y hY), strict_infinity_tail_volume p Y hY,
    strict_zero_tail_volume p hp Y hY]
  have hpos : 0 ≤ 1 / Y := div_nonneg (by norm_num) (by linarith)
  rw [← ENNReal.ofReal_add hpos hpos]
  congr 1
  ring

end ImbalancedChen.Part3.ActualStrictZeroTailMeasure20261026b
