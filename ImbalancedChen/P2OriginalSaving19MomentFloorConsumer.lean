import ImbalancedChen.P2OriginalSaving19SimplexMoments
import ImbalancedChen.P2OriginalLogMomentQ96Checker
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Consume the NEW physical mass/mean proof for the actual saving19
R/M/g/factors, the original maximum-of-nine top, and the unchanged
degree6/Q80/exp3/Q96 evaluator. The record below intentionally has NO
integral mass, integral mean, log-gap, density enclosure or final-bound
field. Its remaining semantic field is the precisely stated degree2..6
power identity. It is an OPEN internal obligation, not an axiom or an
external classical input. No instance for the 28,918 archived rows is
asserted. The aggregate is a sum of true simplex integrals, not an
unproved identification with J.selectedSaving.
-/

namespace ImbalancedChen.P2OriginalSaving19MomentFloorConsumer

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SourceMeasure
open P2OriginalSaving19SimplexMoments
open P2PositiveAffineSimplexLogJensenSourceOnly
open P2DegreeSixLogGapSoundnessSourceOnly
open P2OriginalLogMomentQ96CheckerSourceOnly

def simplexMeasure (L : Point ≃L[ℝ] Point) (b : Point) : Measure Point :=
  volume.restrict (support L b)

def simplexProbability (L : Point ≃L[ℝ] Point) (b : Point) : Measure Point :=
  weightedProbability (simplexMeasure L b) gap

theorem simplex_gap_integrable (L : Point ≃L[ℝ] Point) (b : Point) :
    Integrable gap (simplexMeasure L b) :=
  continuous_gap.continuousOn.integrableOn_compact (support_compact L b)

theorem simplex_gap_nonneg (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) :
    ∀ᵐ t ∂simplexMeasure L b, 0 ≤ gap t := by
  filter_upwards [ae_restrict_mem (support_measurable L b)] with t ht
  exact (support_gap_bounds L b hv ht).1

theorem simplex_factors_pos (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) :
    ∀ᵐ t ∂simplexMeasure L b, ∀ j : Fin 10, 0 < factors t j := by
  filter_upwards [ae_restrict_mem (support_measurable L b)] with t ht
  exact support_factor_pos L b hv ht

theorem simplex_factor_integrable (L : Point ≃L[ℝ] Point) (b : Point) (j : Fin 10) :
    Integrable (fun t => gap t * factors t j) (simplexMeasure L b) :=
  (continuous_gap.mul (continuous_factor j)).continuousOn.integrableOn_compact
    (support_compact L b)

theorem simplex_log_integrable (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) (j : Fin 10) :
    Integrable (fun t => gap t * Real.log (factors t j)) (simplexMeasure L b) := by
  exact (continuous_gap.continuousOn.mul
    ((continuous_factor j).continuousOn.log
      (fun t ht => (support_factor_pos L b hv ht j).ne'))).integrableOn_compact
        (support_compact L b)

theorem simplex_reciprocal_integrable (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) :
    Integrable (fun t => gap t / ∏ j : Fin 10, factors t j) (simplexMeasure L b) := by
  have hp : Continuous (fun t : Point => ∏ j : Fin 10, factors t j) := by
    have hc := continuous_factor
    fun_prop
  exact (continuous_gap.continuousOn.div hp.continuousOn
    (fun t ht => (Finset.prod_pos (fun j _ => support_factor_pos L b hv ht j)).ne')).
      integrableOn_compact (support_compact L b)

theorem simplex_probability (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) (hG : 0 < gapTotal (vertices L b)) :
    IsProbabilityMeasure (simplexProbability L b) :=
  weightedProbability_isProbability _ _ (simplex_gap_integrable L b)
    (simplex_gap_nonneg L b hv) (gap_mass_pos L b hG)

theorem simplex_power_integrable (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, PhysicalRows (vertices L b i)) (hG : 0 < gapTotal (vertices L b))
    (top : ℝ) (j : Fin 10) (k : ℕ) :
    Integrable (fun t => scaledDeviation top (fun t => factors t j) t ^ k)
      (simplexProbability L b) := by
  have hc : Continuous
      (fun t : Point => gap t * scaledDeviation top (fun t => factors t j) t ^ k) :=
    continuous_gap.mul
      ((continuous_const.sub ((continuous_factor j).div_const top)).pow k)
  exact integrable_weightedProbability _ _ continuous_gap.measurable
    (simplex_gap_nonneg L b hv) (gap_mass_pos L b hG)
    (hc.continuousOn.integrableOn_compact (support_compact L b))

/-- Typed input boundary for one ORIGINAL-kind physical row. This record
is not inhabited here by a source witness. The encoding equalities
are finite vertex/determinant algebra; only the power moment field still
mentions an integral. In particular no desired lower bound is stored. -/
structure MomentRow where
  linear : Point ≃L[ℝ] Point
  base : Point
  physicalVertices : ∀ i, PhysicalRows (vertices linear base i)
  positiveGapTotal : 0 < gapTotal (vertices linear base)
  massQ : ℚ
  meansQ : Fin 10 → ℚ
  topsQ : Fin 10 → ℚ
  momentsQ : Fin 10 → ℕ → ℚ
  massEncoding : (massQ : ℝ) =
    physicalVolume linear * gapTotal (vertices linear base) / 9
  meansEncoding : ∀ j, (meansQ j : ℝ) = factorMean (vertices linear base) j
  topsEncoding : ∀ j, (topsQ j : ℝ) = vertexTop (vertices linear base) j
  firstMomentEncoding : ∀ j, momentsQ j 1 = 1 - meansQ j / topsQ j
  higherPowerMoments : ∀ j k, 2 ≤ k → k ≤ 6 →
    (momentsQ j k : ℝ) = ∫ t,
      scaledDeviation (topsQ j : ℝ) (fun t => factors t j) t ^ k
        ∂simplexProbability linear base

theorem row_mass_semantics (r : MomentRow) :
    (r.massQ : ℝ) = mass (simplexMeasure r.linear r.base) gap := by
  rw [r.massEncoding]
  exact (integral_gap r.linear r.base).symm

theorem row_means_semantics (r : MomentRow) (j : Fin 10) :
    (r.meansQ j : ℝ) =
      (∫ t, gap t * factors t j ∂simplexMeasure r.linear r.base) /
        mass (simplexMeasure r.linear r.base) gap := by
  rw [r.meansEncoding]
  exact (normalized_factor_mean r.linear r.base j r.positiveGapTotal).symm

theorem row_means_pos (r : MomentRow) (j : Fin 10) : 0 < r.meansQ j := by
  have h := factorMean_pos (vertices r.linear r.base) r.physicalVertices r.positiveGapTotal j
  rw [← r.meansEncoding j] at h
  exact_mod_cast h

theorem row_tops_pos (r : MomentRow) (j : Fin 10) : 0 < r.topsQ j := by
  have h := vertexTop_pos (vertices r.linear r.base) r.physicalVertices j
  rw [← r.topsEncoding j] at h
  exact_mod_cast h

def rowRangeTop (r : MomentRow) (j : Fin 10) : ℝ := 1 - cutoff / (r.topsQ j : ℝ)

theorem rowRangeTop_lt_one (r : MomentRow) (j : Fin 10) : rowRangeTop r j < 1 := by
  have ht : (0 : ℝ) < r.topsQ j := by exact_mod_cast row_tops_pos r j
  have h := div_pos cutoff_pos ht
  dsimp [rowRangeTop]
  linarith

theorem row_deviation_range (r : MomentRow) (j : Fin 10) :
    ∀ᵐ t ∂simplexMeasure r.linear r.base,
      scaledDeviation (r.topsQ j : ℝ) (fun t => factors t j) t ∈ Icc 0 (rowRangeTop r j) := by
  filter_upwards [ae_restrict_mem (support_measurable r.linear r.base)] with t ht
  have hb := support_factor_bounds r.linear r.base r.physicalVertices ht j
  rw [← r.topsEncoding j] at hb
  exact (scaledDeviation_range (by exact_mod_cast row_tops_pos r j) cutoff_pos hb).1

/-- The producer's degree-one assertion is now analytic output: the
same physical weighted law has mean 1-m/top. No first moment integral
is a record field. -/
theorem row_first_power_moment (r : MomentRow) (j : Fin 10) :
    (r.momentsQ j 1 : ℝ) = ∫ t,
      scaledDeviation (r.topsQ j : ℝ) (fun t => factors t j) t ^ 1
        ∂simplexProbability r.linear r.base := by
  let ν := simplexProbability r.linear r.base
  letI : IsProbabilityMeasure ν := simplex_probability r.linear r.base
    r.physicalVertices r.positiveGapTotal
  have hL : Integrable (fun t => factors t j) ν :=
    integrable_weightedProbability _ _ continuous_gap.measurable
      (simplex_gap_nonneg r.linear r.base r.physicalVertices)
      (gap_mass_pos r.linear r.base r.positiveGapTotal)
      (simplex_factor_integrable r.linear r.base j)
  have hm : (∫ t, factors t j ∂ν) = (r.meansQ j : ℝ) := by
    rw [show ν = weightedProbability (simplexMeasure r.linear r.base) gap from rfl,
      integral_weightedProbability _ _ continuous_gap.measurable
        (simplex_gap_nonneg r.linear r.base r.physicalVertices)
        (gap_mass_pos r.linear r.base r.positiveGapTotal)]
    exact (row_means_semantics r j).symm
  have h := scaledDeviation_mean ν (r.topsQ j : ℝ) (fun t => factors t j) hL
  rw [hm] at h
  rw [r.firstMomentEncoding j]
  push_cast
  simpa only [pow_one] using h.symm

theorem row_power_moments (r : MomentRow) (j : Fin 10) (k : ℕ)
    (hk : 1 ≤ k) (hk6 : k ≤ 6) :
    (r.momentsQ j k : ℝ) = ∫ t,
      scaledDeviation (r.topsQ j : ℝ) (fun t => factors t j) t ^ k
        ∂simplexProbability r.linear r.base := by
  by_cases h : k = 1
  · subst k
    exact row_first_power_moment r j
  · exact r.higherPowerMoments j k (by omega) hk6

/-- All analytic ports except the explicitly OPEN power-moment identity
are derived from original physical vertices and proved polynomial moments. -/
theorem row_computed_Q96_sound (r : MomentRow) :
    (simplexLowerQ96 r.massQ r.meansQ r.momentsQ : ℝ) ≤
      ∫ t in support r.linear r.base, conservativeDensity t := by
  have h := simplex_Q96_sound
    (simplexMeasure r.linear r.base) gap (fun j t => factors t j)
    r.massQ r.meansQ r.topsQ r.momentsQ
    continuous_gap.measurable (simplex_gap_integrable r.linear r.base)
    (simplex_gap_nonneg r.linear r.base r.physicalVertices)
    (gap_mass_pos r.linear r.base r.positiveGapTotal)
    (row_mass_semantics r) (row_means_pos r) (row_tops_pos r) (row_means_semantics r)
    (simplex_factors_pos r.linear r.base r.physicalVertices)
    (simplex_factor_integrable r.linear r.base)
    (simplex_log_integrable r.linear r.base r.physicalVertices)
    (simplex_reciprocal_integrable r.linear r.base r.physicalVertices)
    (rowRangeTop r) (rowRangeTop_lt_one r) (row_deviation_range r)
    (fun j k _ _ => simplex_power_integrable r.linear r.base r.physicalVertices
      r.positiveGapTotal (r.topsQ j : ℝ) j k)
    (row_power_moments r)
  simpa only [simplexMeasure, ← density_factor_dictionary] using h

theorem row_factor_floor_nonneg (r : MomentRow) (j : Fin 10) :
    0 ≤ factorLowerQ80 (r.momentsQ j) := by
  let ν := simplexProbability r.linear r.base
  letI : IsProbabilityMeasure ν := simplex_probability r.linear r.base
    r.physicalVertices r.positiveGapTotal
  have hr : ∀ᵐ t ∂ν,
      scaledDeviation (r.topsQ j : ℝ) (fun t => factors t j) t ∈ Icc 0 (rowRangeTop r j) :=
    (withDensity_absolutelyContinuous _ _).ae_le (row_deviation_range r j)
  have hg := probability_gapSix_nonneg ν
    (scaledDeviation (r.topsQ j : ℝ) (fun t => factors t j))
    (hr.mono fun t ht => ht.1)
    (fun k _ _ => simplex_power_integrable r.linear r.base r.physicalVertices
      r.positiveGapTotal (r.topsQ j : ℝ) j k)
  have he := gapEvaluator_cast ν
    (scaledDeviation (r.topsQ j : ℝ) (fun t => factors t j)) (r.momentsQ j)
    (row_power_moments r j)
  have hgQ : 0 ≤ gapEvaluator (r.momentsQ j) := by
    rw [← he] at hg
    exact_mod_cast hg
  exact roundDownQ_nonneg 80 hgQ

def originalRowFloor (r : MomentRow) : ℚ :=
  ((max (oldFloorQ96 r.massQ r.meansQ)
    (newFloorQ96 r.massQ r.meansQ r.momentsQ) : ℤ) : ℚ) / (2 : ℚ)^96

/-- The author's max(old,new) operation is retained literally. -/
theorem originalRowFloor_eq (r : MomentRow) :
    originalRowFloor r = simplexLowerQ96 r.massQ r.meansQ r.momentsQ := by
  have hmR : (0 : ℝ) ≤ r.massQ := by
    rw [row_mass_semantics]
    exact (gap_mass_pos r.linear r.base r.positiveGapTotal).le
  have hmQ : 0 ≤ r.massQ := by exact_mod_cast hmR
  have hle := oldFloorQ96_le_newFloorQ96 hmQ r.meansQ (row_means_pos r)
    r.momentsQ (row_factor_floor_nonneg r)
  simp only [originalRowFloor, max_eq_right hle, simplexLowerQ96, roundDownQ, newFloorQ96]

theorem originalRowFloor_sound (r : MomentRow) :
    (originalRowFloor r : ℝ) ≤ ∫ t in support r.linear r.base, conservativeDensity t := by
  rw [originalRowFloor_eq]
  exact row_computed_Q96_sound r

/-- Exactly the thirteen original source-cell row counts, read from
their existing manifests. These 13 counts are only an index shape,
not a typed vertex archive or proof of source authentication. -/
def originalRowCount : Fin 13 → ℕ :=
  ![56, 144, 2938, 427, 2864, 56, 113, 2799, 2842, 3693, 2017, 4369, 6600]

abbrev OriginalRowIndex := (i : Fin 13) × Fin (originalRowCount i)

theorem originalRowCount_sum : (∑ i : Fin 13, originalRowCount i) = 28918 := by
  norm_num [originalRowCount, Fin.sum_univ_succ]

/-- The genuine row-integral aggregate consumer. The original row
shape is fixed, but its MomentRow family has NOT been constructed.
No equality with the thirteen selected-domain integral is assumed.
That ownership/source step and all original typed rows remain OPEN. -/
theorem original_family_floor_sum_le_integral_sum
    (rows : OriginalRowIndex → MomentRow) :
    (∑ r : OriginalRowIndex, (originalRowFloor (rows r) : ℝ)) ≤
      ∑ r : OriginalRowIndex,
        ∫ t in support (rows r).linear (rows r).base, conservativeDensity t := by
  exact Finset.sum_le_sum (fun r _ => originalRowFloor_sound (rows r))

/-- The same finite source consumes the new mass normalization on all
its slots. There is no implicit same-family coverage premise. -/
theorem original_family_gap_mass_sum
    (rows : OriginalRowIndex → MomentRow) :
    (∑ r : OriginalRowIndex, ∫ t in support (rows r).linear (rows r).base, gap t) =
      ∑ r : OriginalRowIndex,
        physicalVolume (rows r).linear * gapTotal (vertices (rows r).linear (rows r).base) / 9 := by
  exact Finset.sum_congr rfl (fun r _ => integral_gap (rows r).linear (rows r).base)

end

end ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
