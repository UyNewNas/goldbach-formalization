import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.
Pinned mathlib already supplies the canonical `UpperHalfPlane` volume
`dx dy / y^2`. This file adapts that actual measure as a future cusp L2
base: its density formula, compact finiteness, positivity, and equality of
null sets with the unweighted complex-coordinate Lebesgue measure pulled
back to the upper half-plane. No spectral decomposition is assumed.
-/

namespace ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane NNReal

/-- Unweighted planar Lebesgue measure pulled back through the canonical
inclusion of the upper half-plane into ℂ. -/
def coordinateMeasure : Measure UpperHalfPlane :=
  (volume : Measure ℂ).comap UpperHalfPlane.coe

/-- The existing mathlib invariant hyperbolic measure, with no new choice
of normalization. -/
def hyperbolicMeasure : Measure UpperHalfPlane := volume

/-- The exact mathlib density `(1 / y)^2` as an extended nonnegative real. -/
def hyperbolicDensity (z : UpperHalfPlane) : ℝ≥0∞ :=
  ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)

theorem hyperbolicMeasure_eq_withDensity :
    hyperbolicMeasure = coordinateMeasure.withDensity hyperbolicDensity := by
  exact UpperHalfPlane.volume_def

private theorem hyperbolicDensity_nnreal_pos (z : UpperHalfPlane) :
    0 < NNReal.mk z.im z.im_pos.le := by
  change 0 < z.im
  exact z.im_pos

theorem hyperbolicDensity_ne_zero (z : UpperHalfPlane) :
    hyperbolicDensity z ≠ 0 := by
  have hn : (NNReal.mk z.im z.im_pos.le : ℝ≥0) ≠ 0 :=
    (hyperbolicDensity_nnreal_pos z).ne'
  have hq : ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (div_ne_zero one_ne_zero hn)
  exact ENNReal.coe_ne_zero.mpr hq

theorem hyperbolicDensity_measurable : Measurable hyperbolicDensity := by
  have hnn : Continuous (fun z : UpperHalfPlane =>
      NNReal.mk z.im z.im_pos.le) :=
    UpperHalfPlane.continuous_im.subtype_mk (fun z => z.im_pos.le)
  have hnn0 (z : UpperHalfPlane) :
      (NNReal.mk z.im z.im_pos.le : ℝ≥0) ≠ 0 :=
    (hyperbolicDensity_nnreal_pos z).ne'
  have hc : Continuous hyperbolicDensity := by
    unfold hyperbolicDensity
    exact ENNReal.continuous_coe.comp
      ((continuous_const.div₀ hnn hnn0).pow 2)
  exact hc.measurable

/-- The canonical measure has finite mass on every compact upper-half-plane
set. This consumes mathlib's local-finiteness instance for its exact volume. -/
theorem hyperbolicMeasure_compact_finite {K : Set UpperHalfPlane}
    (hK : IsCompact K) : hyperbolicMeasure K < ∞ := by
  exact hK.measure_lt_top

theorem hyperbolicMeasure_sigmaFinite : SigmaFinite hyperbolicMeasure :=
  inferInstance

/-- The two actual measures have identical null sets. -/
theorem hyperbolicMeasure_absolutelyContinuous_coordinate :
    hyperbolicMeasure ≪ coordinateMeasure := by
  rw [hyperbolicMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous coordinateMeasure hyperbolicDensity

theorem coordinateMeasure_absolutelyContinuous_hyperbolic :
    coordinateMeasure ≪ hyperbolicMeasure := by
  rw [hyperbolicMeasure_eq_withDensity]
  apply withDensity_absolutelyContinuous' hyperbolicDensity_measurable.aemeasurable
  exact Filter.Eventually.of_forall hyperbolicDensity_ne_zero

theorem ae_hyperbolic_iff_ae_coordinate (p : UpperHalfPlane → Prop) :
    (∀ᵐ z ∂hyperbolicMeasure, p z) ↔
      (∀ᵐ z ∂coordinateMeasure, p z) := by
  constructor
  · intro h
    exact coordinateMeasure_absolutelyContinuous_hyperbolic.ae_le h
  · intro h
    exact hyperbolicMeasure_absolutelyContinuous_coordinate.ae_le h

/-- The measure is nonzero, since the positive density preserves the
positive mass of a nonempty open subset of the complex plane. -/
theorem hyperbolicMeasure_ne_zero : hyperbolicMeasure ≠ 0 := by
  have hbaseOpen : Measure.IsOpenPosMeasure coordinateMeasure := by
    exact Measure.IsOpenPosMeasure.comap (volume : Measure ℂ)
      UpperHalfPlane.isOpenEmbedding_coe
  letI : Measure.IsOpenPosMeasure coordinateMeasure := hbaseOpen
  have hbase : coordinateMeasure Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos coordinateMeasure Set.univ_nonempty).ne'
  intro hz
  have hzero : coordinateMeasure Set.univ = 0 :=
    coordinateMeasure_absolutelyContinuous_hyperbolic (by simp [hz])
  exact hbase hzero

end
end ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z
