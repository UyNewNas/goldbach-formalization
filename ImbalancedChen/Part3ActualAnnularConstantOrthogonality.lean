import ImbalancedChen.Part3ActualTruncationConstantBands
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Canonical annular transport and genuine zero-mean separation for
the ACTUAL quotient truncations. Native L2 Hölder pays for Fubini. The
original physical two-cusp remainder means kill both mixed terms, and
the same-band pairing has exactly the completed-constant height Gram.
No model cylinder pairing, Green/Stokes identity or completeness input.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeCommonHeightAnnulusConversion20261026b
open ImbalancedChen.Part3.ActualStrictZeroTailMeasure20261026b
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.ActualCompletedTwoCuspTruncation20261026b
open ImbalancedChen.Part3.ActualTruncatedCompletedL220261026b
open ImbalancedChen.Part3.ActualTruncationConstantBands20261026b
open ImbalancedChen.Part3.ActualTwoCuspHeightRemainders20261026b
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a

namespace ImbalancedChen.Part3.ActualAnnularConstantOrthogonality20261026b

theorem zeroAnnulus_eq_fricke_preimage (p : ℕ) (hp : p.Prime) (Y Z : ℝ) :
    cuspAnnulus p hp Y Z true = quotientFricke p hp.pos ⁻¹' infinityAnnulus p Y Z := by
  ext q
  simp only [cuspAnnulus, cuspTail, Bool.true_eq_true, if_true,
    zeroHighNeighborhood_eq_fricke_preimage, infinityAnnulus, mem_sdiff, mem_preimage]

/-- The second annular measure is derived from the actual global
Fricke quotient measure and the already proved infinity annulus. -/
theorem cuspAnnulus_strip_map_measure (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool) :
    ((volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z)).map
      (cuspProjection p hp b) = (carrierPushforward p).restrict (cuspAnnulus p hp Y Z b) := by
  cases b
  · exact infinityAnnulus_strip_map_measure p Y Z hY hYZ
  · have he : cuspProjection p hp true = quotientFricke p hp.pos ∘ orbitProjection p := rfl
    have hi : infinityAnnulus p Y Z =
        quotientFricke p hp.pos ⁻¹' cuspAnnulus p hp Y Z true := by
      rw [zeroAnnulus_eq_fricke_preimage]
      ext q
      simp only [mem_preimage, quotientFricke_involutive p hp.pos]
    rw [he, ← Measure.map_map (quotientFricke_measurable p hp.pos)
      (orbitProjection_measurable p), infinityAnnulus_strip_map_measure p Y Z hY hYZ,
      hi, ← Measure.restrict_map (quotientFricke_measurable p hp.pos)
        (cuspAnnulus_measurable p hp Y Z hY hYZ true), quotientFricke_map_measure p hp.pos]

theorem cuspAnnulus_integrable_iff (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool)
    (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F) :
    IntegrableOn F (cuspAnnulus p hp Y Z b) (carrierPushforward p) ↔
      IntegrableOn (fun z => F (cuspProjection p hp b z)) (infinityAnnulusStrip Y Z) := by
  have h := integrable_map_measure hF.aestronglyMeasurable
    (cuspProjection_measurable p hp b).aemeasurable
    (μ := (volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z))
  rwa [cuspAnnulus_strip_map_measure p hp Y Z hY hYZ b] at h

theorem cuspAnnulus_integral (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool)
    (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F) :
    (∫ q in cuspAnnulus p hp Y Z b, F q ∂carrierPushforward p) =
      ∫ z in infinityAnnulusStrip Y Z, F (cuspProjection p hp b z) := by
  have h := integral_map (cuspProjection_measurable p hp b).aemeasurable hF.aestronglyMeasurable
    (μ := (volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z))
  rwa [cuspAnnulus_strip_map_measure p hp Y Z hY hYZ b] at h

theorem cuspAnnulus_chart_integrable (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool)
    (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F)
    (hFi : IntegrableOn F (cuspAnnulus p hp Y Z b) (carrierPushforward p)) :
    Integrable (chartPullback (fun z => F (cuspProjection p hp b z)))
      (((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
        (verticalWeightedMeasure.restrict (Ioc Y Z))) := by
  rw [← infinityAnnulusStrip_chart_map_measure Y Z]
  apply chartMap_measurableEmbedding.integrable_map_iff.mpr
  have h := (cuspAnnulus_integrable_iff p hp Y Z hY hYZ b F hF).mp hFi
  simpa only [Function.comp_def, chartMap, chartPullback_at_upper] using h

theorem cuspAnnulus_iterated_integral (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool)
    (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F)
    (hFi : IntegrableOn F (cuspAnnulus p hp Y Z b) (carrierPushforward p)) :
    (∫ q in cuspAnnulus p hp Y Z b, F q ∂carrierPushforward p) =
      ∫ y in Ioc Y Z, (∫ x in Ico (0 : ℝ) 1,
        chartPullback (fun z => F (cuspProjection p hp b z)) (x, y)) ∂verticalWeightedMeasure := by
  rw [cuspAnnulus_integral p hp Y Z hY hYZ b F hF]
  have h := chartMap_measurableEmbedding.integral_map
    (μ := (volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z))
    (g := chartPullback (fun z => F (cuspProjection p hp b z)))
  rw [infinityAnnulusStrip_chart_map_measure Y Z] at h
  have he : (∫ z in infinityAnnulusStrip Y Z, F (cuspProjection p hp b z)) =
      ∫ a : ℝ × ℝ, chartPullback (fun z => F (cuspProjection p hp b z)) a
        ∂(((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
          (verticalWeightedMeasure.restrict (Ioc Y Z))) := by
    simpa only [chartMap, chartPullback_at_upper] using h.symm
  rw [he]
  exact integral_prod_symm _ (cuspAnnulus_chart_integrable p hp Y Z hY hYZ b F hF hFi)

theorem truncatedCompleted_cusp_high (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (s : ℂ) (hs : s ∈ completedRegularDomain p) (b : Bool)
    (z : UpperHalfPlane) (hz : Y < z.im) :
    truncatedCompleted p hp Y hY s hs (cuspProjection p hp b z) =
      physicalCuspRemainder p hp.pos s b z.im z.re := by
  rw [physicalCuspRemainder, physicalCuspChart_eq_native p hp.pos s b z]
  cases b
  · exact truncatedCompleted_infinity p hp Y hY s hs z hz
  · exact truncatedCompleted_zero p hp Y hY s hs z hz

private theorem physicalRemainder_Ico_mean (p : ℕ) (hp : p.Prime) (s : ℂ)
    (hs : s ∈ completedRegularDomain p) (b : Bool) (y : ℝ) (hy : 0 < y) :
    (∫ x in Ico (0 : ℝ) 1, physicalCuspRemainder p hp.pos s b y x) = 0 := by
  rw [integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact physicalCuspRemainder_mean_zero p hp.pos s hs.1 hs.2.1 b hy

private theorem full_integral_eq_band (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (b : Bool) (F : Gamma0OrbitSpace p → ℂ)
    (hF : ∀ q, q ∉ cuspAnnulus p hp Y Z b → F q = 0) :
    (∫ q, F q ∂carrierPushforward p) = ∫ q in cuspAnnulus p hp Y Z b, F q ∂carrierPushforward p := by
  classical
  have he : F = (cuspAnnulus p hp Y Z b).indicator F := by
    funext q
    by_cases hq : q ∈ cuspAnnulus p hp Y Z b
    · rw [indicator_of_mem hq]
    · rw [indicator_of_notMem hq, hF q hq]
  calc
    (∫ q, F q ∂carrierPushforward p) =
        ∫ q, (cuspAnnulus p hp Y Z b).indicator F q ∂carrierPushforward p :=
      congrArg (fun G => ∫ q, G q ∂carrierPushforward p) he
    _ = _ := integral_indicator (cuspAnnulus_measurable p hp Y Z hY hYZ b)

/-- Constant/nonconstant annular orthogonality on the ORIGINAL quotient.
The actual L2 representatives supply the product integrability for Fubini. -/
theorem truncated_constantBand_integral_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) (b : Bool) :
    (∫ q, star (truncatedCompleted p hp Y hY s hs q) *
      cuspConstantBand p hp Y Z hY (hY.trans hYZ) u b q ∂carrierPushforward p) = 0 := by
  let F : Gamma0OrbitSpace p → ℂ := fun q => star (truncatedCompleted p hp Y hY s hs q) *
    cuspConstantBand p hp Y Z hY (hY.trans hYZ) u b q
  have hFm : Measurable F := (truncatedCompleted_measurable p hp Y hY s hs).star.mul
    (cuspConstantBand_measurable p hp Y Z hY (hY.trans hYZ) u b)
  have hFi : Integrable F (carrierPushforward p) :=
    (truncatedCompleted_memLp_two p hp Y hY s hs).star.integrable_mul
      (cuspConstantBand_memLp_two p hp Y Z hY hYZ u hu b)
  change (∫ q, F q ∂carrierPushforward p) = 0
  rw [full_integral_eq_band p hp Y Z hY hYZ b F (by
    intro q hq
    simp only [F, cuspConstantBand_off p hp Y Z hY hYZ u b q hq, mul_zero]),
    cuspAnnulus_iterated_integral p hp Y Z hY hYZ b F hFm hFi.integrableOn]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hY.trans hy.1.le)
  have he (x : ℝ) : chartPullback (fun z => F (cuspProjection p hp b z)) (x, y) =
      star (physicalCuspRemainder p hp.pos s b y x) * physicalCuspConstant p u b y := by
    let z : UpperHalfPlane := ⟨⟨x, y⟩, hy0⟩
    change chartPullback (fun z => F (cuspProjection p hp b z)) (z.re, z.im) = _
    rw [show (z.re, z.im) = chartMap z from rfl]
    simp only [chartMap, chartPullback_at_upper, F]
    rw [truncatedCompleted_cusp_high p hp Y hY s hs b z hy.1,
      cuspConstantBand_high p hp Y Z hY hYZ u b z hy.1 hy.2]
  calc
    _ = ∫ x in Ico (0 : ℝ) 1,
        star (physicalCuspRemainder p hp.pos s b y x) * physicalCuspConstant p u b y :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = 0 := by
      rw [integral_mul_const]
      simp only [Complex.star_def, integral_conj,
        physicalRemainder_Ico_mean p hp s hs b y hy0, map_zero, zero_mul]

theorem constantBand_truncated_integral_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) (b : Bool) :
    (∫ q, star (cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b q) *
      truncatedCompleted p hp Y hY u hu q ∂carrierPushforward p) = 0 := by
  have he : (fun q => star (cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b q) *
      truncatedCompleted p hp Y hY u hu q) = fun q =>
      star (star (truncatedCompleted p hp Y hY u hu q) *
        cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b q) := by
    funext q
    simp only [star_mul, star_star]
    ring
  rw [he]
  simp only [Complex.star_def, integral_conj,
    truncated_constantBand_integral_zero p hp Y Z hY hYZ u s hu hs b, map_zero]

/-- Physical finite-height Gram, with the existing completed constants
and the canonical vertical y^-2dy measure retained literally. -/
def completedConstantBandGram (p : ℕ) (Y Z : ℝ) (s u : ℂ) (b : Bool) : ℂ :=
  ∫ y in Ioc Y Z, star (physicalCuspConstant p s b y) * physicalCuspConstant p u b y
    ∂verticalWeightedMeasure

theorem constantBand_pair_integral (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) (b : Bool) :
    (∫ q, star (cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b q) *
      cuspConstantBand p hp Y Z hY (hY.trans hYZ) u b q ∂carrierPushforward p) =
      completedConstantBandGram p Y Z s u b := by
  let F : Gamma0OrbitSpace p → ℂ := fun q =>
    star (cuspConstantBand p hp Y Z hY (hY.trans hYZ) s b q) *
      cuspConstantBand p hp Y Z hY (hY.trans hYZ) u b q
  have hFm : Measurable F :=
    (cuspConstantBand_measurable p hp Y Z hY (hY.trans hYZ) s b).star.mul
      (cuspConstantBand_measurable p hp Y Z hY (hY.trans hYZ) u b)
  have hFi : Integrable F (carrierPushforward p) :=
    (cuspConstantBand_memLp_two p hp Y Z hY hYZ s hs b).star.integrable_mul
      (cuspConstantBand_memLp_two p hp Y Z hY hYZ u hu b)
  change (∫ q, F q ∂carrierPushforward p) = _
  rw [full_integral_eq_band p hp Y Z hY hYZ b F (by
    intro q hq
    simp only [F, cuspConstantBand_off p hp Y Z hY hYZ u b q hq, mul_zero]),
    cuspAnnulus_iterated_integral p hp Y Z hY hYZ b F hFm hFi.integrableOn]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hY.trans hy.1.le)
  have he (x : ℝ) : chartPullback (fun z => F (cuspProjection p hp b z)) (x, y) =
      star (physicalCuspConstant p s b y) * physicalCuspConstant p u b y := by
    let z : UpperHalfPlane := ⟨⟨x, y⟩, hy0⟩
    change chartPullback (fun z => F (cuspProjection p hp b z)) (z.re, z.im) = _
    rw [show (z.re, z.im) = chartMap z from rfl]
    simp only [chartMap, chartPullback_at_upper, F]
    rw [cuspConstantBand_high p hp Y Z hY hYZ s b z hy.1 hy.2,
      cuspConstantBand_high p hp Y Z hY hYZ u b z hy.1 hy.2]
  calc
    _ = ∫ _x in Ico (0 : ℝ) 1, star (physicalCuspConstant p s b y) *
        physicalCuspConstant p u b y := integral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by simp

theorem cross_cusp_constantBand_integral_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ) :
    (∫ q, star (cuspConstantBand p hp Y Z hY (hY.trans hYZ) s false q) *
      cuspConstantBand p hp Y Z hY (hY.trans hYZ) u true q ∂carrierPushforward p) = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q ∈ cuspAnnulus p hp Y Z false
  · have ho : q ∉ cuspAnnulus p hp Y Z true := fun h =>
      (Set.disjoint_left.mp (cuspAnnuli_disjoint p hp Y Z hY)) hq h
    rw [cuspConstantBand_off p hp Y Z hY hYZ u true q ho, mul_zero]
  · rw [cuspConstantBand_off p hp Y Z hY hYZ s false q hq, star_zero, zero_mul]

end ImbalancedChen.Part3.ActualAnnularConstantOrthogonality20261026b
