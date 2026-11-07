import ImbalancedChen.Part3ImaginaryOrderKPositiveAxis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

This file constructs a positive candidate density for the order convention
in `ImaginaryOrderKBesselSourceOnly.imaginaryOrderK`: its defining integrand
is `exp (-q * cosh u) * cos (2*t*u)`, so its imaginary order is `2it`.

We define w(t) = t * sinh (2*pi*t), prove its elementary analytic and
measure-theoretic properties, and construct volume.withDensity (ofReal w).
This is an unnormalized CANDIDATE measure. Its identification as a spectral,
Kontorovich--Lebedev Plancherel, or Kuznetsov measure is NOT established.
In particular, this file contains no transform norm equality, inversion
formula, cusp spectral decomposition, or desired spectral estimate.
-/

namespace ImbalancedChen.Part3.P3KLDensityMeasureSourceOnly

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

/-- Candidate density for the actual `K_{2it}` order convention. -/
def candidateDensity (t : ℝ) : ℝ :=
  t * Real.sinh (2 * Real.pi * t)

@[simp] theorem candidateDensity_zero : candidateDensity 0 = 0 := by
  simp [candidateDensity]

@[simp] theorem candidateDensity_neg (t : ℝ) :
    candidateDensity (-t) = candidateDensity t := by
  unfold candidateDensity
  rw [mul_neg, Real.sinh_neg, neg_mul_neg]

theorem candidateDensity_continuous : Continuous candidateDensity := by
  unfold candidateDensity
  fun_prop

/-- Strict positivity includes both signs of the real order parameter. -/
theorem candidateDensity_pos {t : ℝ} (ht : t ≠ 0) :
    0 < candidateDensity t := by
  have hpi : 0 < (2 : ℝ) * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · exact mul_pos_of_neg_of_neg hneg
      (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hpi hneg))
  · exact mul_pos hpos (Real.sinh_pos_iff.mpr (mul_pos hpi hpos))

theorem candidateDensity_nonneg (t : ℝ) : 0 ≤ candidateDensity t := by
  by_cases ht : t = 0
  · simp [ht]
  · exact (candidateDensity_pos ht).le

@[simp] theorem candidateDensity_eq_zero_iff (t : ℝ) :
    candidateDensity t = 0 ↔ t = 0 := by
  constructor
  · intro hw
    by_contra ht
    exact (ne_of_gt (candidateDensity_pos ht)) hw
  · rintro rfl
    exact candidateDensity_zero

/-- The ENNReal density is finite everywhere, including the origin. -/
def candidateDensityENN (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (candidateDensity t)

theorem candidateDensityENN_measurable : Measurable candidateDensityENN := by
  exact candidateDensity_continuous.measurable.ennreal_ofReal

@[simp] theorem candidateDensityENN_ne_top (t : ℝ) :
    candidateDensityENN t ≠ ∞ := by
  exact ENNReal.ofReal_ne_top

@[simp] theorem candidateDensityENN_eq_zero_iff (t : ℝ) :
    candidateDensityENN t = 0 ↔ t = 0 := by
  change ENNReal.ofReal (candidateDensity t) = 0 ↔ t = 0
  rw [ENNReal.ofReal_eq_zero]
  constructor
  · intro ht
    exact (candidateDensity_eq_zero_iff t).mp
      (le_antisymm ht (candidateDensity_nonneg t))
  · rintro rfl
    simp

theorem candidateDensityENN_pos {t : ℝ} (ht : 0 < t) :
    0 < candidateDensityENN t := by
  exact ENNReal.ofReal_pos.mpr (candidateDensity_pos (ne_of_gt ht))

/-- A concrete measure; no spectral identification is part of this definition. -/
def candidateMeasure : Measure ℝ :=
  volume.withDensity candidateDensityENN

theorem candidateMeasure_absolutelyContinuous : candidateMeasure ≪ volume := by
  exact withDensity_absolutelyContinuous volume candidateDensityENN

/-- Compact restrictions have finite mass because the real density is continuous. -/
theorem candidateMeasure_compact_lt_top {s : Set ℝ} (hs : IsCompact s) :
    candidateMeasure s < ∞ := by
  have hi : IntegrableOn candidateDensity s volume :=
    candidateDensity_continuous.continuousOn.integrableOn_compact hs
  have hn : 0 ≤ᵐ[volume.restrict s] candidateDensity :=
    Filter.Eventually.of_forall candidateDensity_nonneg
  have hl : (∫⁻ t in s, ENNReal.ofReal (candidateDensity t)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hn).mp hi.hasFiniteIntegral
  rw [candidateMeasure, withDensity_apply _ hs.measurableSet]
  exact hl

theorem candidateMeasure_restrict_compact_isFinite {s : Set ℝ} (hs : IsCompact s) :
    IsFiniteMeasure (candidateMeasure.restrict s) := by
  exact isFiniteMeasure_restrict.mpr (ne_of_lt (candidateMeasure_compact_lt_top hs))

/-- The same concrete construction on the positive half-axis. -/
theorem candidateMeasure_restrict_Ioi :
    candidateMeasure.restrict (Ioi (0 : ℝ)) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity candidateDensityENN := by
  exact restrict_withDensity measurableSet_Ioi candidateDensityENN

theorem candidateMeasure_restrict_Ioi_absolutelyContinuous :
    candidateMeasure.restrict (Ioi (0 : ℝ)) ≪ volume.restrict (Ioi (0 : ℝ)) := by
  rw [candidateMeasure_restrict_Ioi]
  exact withDensity_absolutelyContinuous _ _

theorem volume_restrict_Ioi_absolutelyContinuous :
    volume.restrict (Ioi (0 : ℝ)) ≪ candidateMeasure.restrict (Ioi (0 : ℝ)) := by
  rw [candidateMeasure_restrict_Ioi]
  apply withDensity_absolutelyContinuous' candidateDensityENN_measurable.aemeasurable
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with t ht
  exact (candidateDensityENN_pos ht).ne'

/-- Arbitrary predicates have the same a.e. meaning for both measures on `t > 0`. -/
theorem ae_candidateMeasure_restrict_Ioi_iff {p : ℝ → Prop} :
    (∀ᵐ t ∂candidateMeasure.restrict (Ioi (0 : ℝ)), p t) ↔
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), p t := by
  rw [candidateMeasure_restrict_Ioi, ae_withDensity_iff candidateDensityENN_measurable]
  constructor
  · intro hp
    filter_upwards [hp,
      ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht hpos
    exact ht (candidateDensityENN_pos hpos).ne'
  · intro hp
    exact hp.mono (fun _ ht _ => ht)

end
end ImbalancedChen.Part3.P3KLDensityMeasureSourceOnly

