import ImbalancedChen.OriginalAscendingThirteenExportOwnershipJoin
import ImbalancedChen.P2PositiveAffineSimplexLogJensen
import ImbalancedChen.P2DegreeSixLogGapSoundness
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual saving 19: the thirteen A23/s23_low cells, with their unchanged
R=A(t1+t4), M=A(t2+t4+t8)-10^-6 and ten denominator factors.
This file proves the analytic source regularity and thirteen-cell
additivity needed before attaching the original 28,918 simplex floors.
It does not import or identify the different 11,026 unequal-seed rows.

The common compact hull is DERIVED from the existing physical rows.
Neither integrability, a cell integral bound, disjointness nor coverage
is supplied as a hypothesis. The original simplex-to-cell maps, moment
identities, Q80/Q96 floors and final endpoint remain OPEN.
-/

namespace ImbalancedChen.P2OriginalSaving19SourceMeasure

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal
open P2OriginalThirdMinorantLogDictionarySourceOnly VariableEnvelope
open OriginalAscendingThirteenCellOwnership
open OriginalAscendingThirteenLiteralAffineRows
open OriginalAscendingThirteenExportOwnershipJoin
open OriginalDescendingFifteenLiteralAffineRows (evaluateCoefficients)
open P2PositiveAffineSimplexLogJensenSourceOnly
open P2DegreeSixLogGapSoundnessSourceOnly

def cutoff : ℝ := 53 / 13824

theorem cutoff_pos : 0 < cutoff := by norm_num [cutoff]

theorem continuous_comparisonCap : Continuous comparisonCap := by
  unfold comparisonCap A
  fun_prop

theorem continuous_newCap : Continuous newCap := by
  unfold newCap selectedSum A eta
  fun_prop

theorem continuous_total : Continuous total := by
  unfold total
  fun_prop

theorem continuous_gap : Continuous gap :=
  continuous_newCap.sub continuous_comparisonCap

theorem continuous_factor (j : Fin 10) : Continuous (fun t : Point => factors t j) := by
  fin_cases j <;>
    simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact continuous_comparisonCap.sub continuous_total
  · exact continuous_newCap.sub continuous_total
  all_goals exact continuous_apply _

/-- Common analytic hull only. It is NOT asserted to be any source cell,
simplex union, or an exact cover of the original selected domains. -/
def analyticHull : Set Point :=
  Icc (fun _ => cutoff) (fun _ => mu) ∩
    {t | comparisonCap t - total t ∈ Icc cutoff (3 * mu)} ∩
    {t | newCap t - total t ∈ Icc cutoff (3 * mu)} ∩
    {t | gap t ∈ Icc 0 (2 * mu)}

theorem physical_coordinate_bounds {t : Point} (ht : PhysicalRows t) (j : Fin 8) :
    cutoff ≤ t j ∧ t j ≤ mu := by
  exact ⟨ht.eighthCutoff.trans (ht.ordered (by omega)),
    (ht.ordered (by omega : (0 : Fin 8) ≤ j)).trans ht.largestBelowMu⟩

theorem physical_factor_bounds {t : Point} (ht : PhysicalRows t) (j : Fin 10) :
    factors t j ∈ Icc cutoff (3 * mu) := by
  have hr := physical_residual_range ht
  have hlast := physical_coordinate_bounds ht 7
  have hcoord (k : Fin 8) : t k ∈ Icc cutoff (3 * mu) := by
    have hk := physical_coordinate_bounds ht k
    constructor
    · exact hk.1
    · have hm : (0 : ℝ) ≤ mu := by norm_num [mu]
      linarith [hk.2]
  fin_cases j <;>
    simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact ⟨hlast.1.trans hr.1, by linarith [hr.2.1, hr.2.2, hlast.2]⟩
  · exact ⟨hlast.1.trans (hr.1.trans hr.2.1), by linarith [hr.2.2, hlast.2]⟩
  all_goals exact hcoord _

theorem physical_gap_bounds {t : Point} (ht : PhysicalRows t) :
    gap t ∈ Icc 0 (2 * mu) := by
  have hr := physical_residual_range ht
  have hlast := physical_coordinate_bounds ht 7
  dsimp [gap]
  constructor
  · exact sub_nonneg.mpr ht.improvement
  · linarith [hr.1, hr.2.2, hlast.2]

theorem physicalRows_mem_hull {t : Point} (ht : PhysicalRows t) : t ∈ analyticHull := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, physical_gap_bounds ht⟩
  · exact ⟨fun j => (physical_coordinate_bounds ht j).1,
      fun j => (physical_coordinate_bounds ht j).2⟩
  · simpa only [factors, Matrix.cons_val_zero] using physical_factor_bounds ht 0
  · simpa only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ] using
      physical_factor_bounds ht 1

theorem analyticHull_closed : IsClosed analyticHull := by
  exact ((isClosed_Icc.inter
    (isClosed_Icc.preimage (continuous_comparisonCap.sub continuous_total))).inter
    (isClosed_Icc.preimage (continuous_newCap.sub continuous_total))).inter
    (isClosed_Icc.preimage continuous_gap)

theorem analyticHull_compact : IsCompact analyticHull := by
  apply (isCompact_Icc : IsCompact
    (Icc (fun _ : Fin 8 => cutoff) (fun _ => mu))).of_isClosed_subset analyticHull_closed
  intro t ht
  exact ht.1.1.1

theorem hull_factor_lower {t : Point} (ht : t ∈ analyticHull) (j : Fin 10) :
    cutoff ≤ factors t j := by
  fin_cases j <;>
    simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact ht.1.1.2.1
  · exact ht.1.2.1
  all_goals exact ht.1.1.1.1 _

theorem hull_factor_pos {t : Point} (ht : t ∈ analyticHull) (j : Fin 10) :
    0 < factors t j := cutoff_pos.trans_le (hull_factor_lower ht j)

theorem hull_gap_nonneg {t : Point} (ht : t ∈ analyticHull) : 0 ≤ gap t := ht.2.1

theorem continuousOn_density_hull : ContinuousOn conservativeDensity analyticHull := by
  have he : conservativeDensity = fun t => 4 * gap t / ∏ j, factors t j := by
    funext t
    exact density_factor_dictionary t
  rw [he]
  apply (continuous_const.mul continuous_gap).continuousOn.div
    (show Continuous (fun t : Point => ∏ j, factors t j) by
      have hc := continuous_factor
      fun_prop).continuousOn
  intro t ht
  exact (Finset.prod_pos (fun j _ => hull_factor_pos ht j)).ne'

theorem hull_density_integrable : IntegrableOn conservativeDensity analyticHull :=
  continuousOn_density_hull.integrableOn_compact analyticHull_compact

/-- A typed source-to-hull theorem for EVERY original selected cell. -/
theorem cell_subset_hull (i : Fin 13) : cell i ⊆ analyticHull := by
  intro t ht
  exact physicalRows_mem_hull (rows_physical ht)

theorem cell_measurable (i : Fin 13) : MeasurableSet (cell i) := by
  have he : cell i = ⋂ r : Fin 97,
      {t : Point | 0 < evaluateCoefficients (exportedCoefficients i r) t} := by
    ext t
    simp only [mem_iInter, mem_setOf_eq]
    exact (strictExportedRows_iff_StrictRows i t).symm
  rw [he]
  apply MeasurableSet.iInter
  intro r
  apply (isOpen_lt continuous_const ?_).measurableSet
  unfold evaluateCoefficients
  fun_prop

theorem cell_density_integrable (i : Fin 13) : IntegrableOn conservativeDensity (cell i) :=
  hull_density_integrable.mono_set (cell_subset_hull i)

theorem cell_density_nonneg {i : Fin 13} {t : Point} (ht : t ∈ cell i) :
    0 ≤ conservativeDensity t := conservativeDensity_nonneg (rows_physical ht)

theorem cell_gap_integrable (i : Fin 13) : IntegrableOn gap (cell i) :=
  (continuous_gap.continuousOn.integrableOn_compact analyticHull_compact).mono_set
    (cell_subset_hull i)

/-- All factor-weighted logarithms in the actual moment engine exist as
genuine real Lebesgue integrals, including near closed-cell boundaries. -/
theorem cell_log_moment_integrable (i : Fin 13) (j : Fin 10) :
    IntegrableOn (fun t => gap t * Real.log (factors t j)) (cell i) := by
  have hc : ContinuousOn (fun t => gap t * Real.log (factors t j)) analyticHull :=
    continuous_gap.continuousOn.mul
      ((continuous_factor j).continuousOn.log (fun t ht => (hull_factor_pos ht j).ne'))
  exact (hc.integrableOn_compact analyticHull_compact).mono_set (cell_subset_hull i)

/-- Degree is arbitrary here; in the original producer it is at most six.
The top parameter is retained literally, not replaced by a global top. -/
theorem cell_power_moment_integrable (i : Fin 13) (j : Fin 10) (top : ℝ) (k : ℕ) :
    IntegrableOn
      (fun t => gap t * (scaledDeviation top (fun t => factors t j) t)^k) (cell i) := by
  have hc : Continuous
      (fun t => gap t * (scaledDeviation top (fun t => factors t j) t)^k) :=
    continuous_gap.mul ((continuous_const.sub ((continuous_factor j).div_const top)).pow k)
  exact (hc.continuousOn.integrableOn_compact analyticHull_compact).mono_set
    (cell_subset_hull i)

def cellGapMass (i : Fin 13) : ℝ := ∫ t in cell i, gap t

theorem cell_gapMass_nonneg (i : Fin 13) : 0 ≤ cellGapMass i := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (cell_measurable i)] with t ht
  exact hull_gap_nonneg (cell_subset_hull i ht)

/-- The measure is the original physical gap density divided by its true
mass. This is not an asserted abstract Dirichlet law or a moment table. -/
def cellProbability (i : Fin 13) : Measure Point :=
  weightedProbability (volume.restrict (cell i)) gap

theorem cellProbability_isProbability (i : Fin 13) (hm : 0 < cellGapMass i) :
    IsProbabilityMeasure (cellProbability i) := by
  apply weightedProbability_isProbability _ _ (cell_gap_integrable i) _ hm
  filter_upwards [ae_restrict_mem (cell_measurable i)] with t ht
  exact hull_gap_nonneg (cell_subset_hull i ht)

theorem cell_probability_power_integrable (i : Fin 13) (j : Fin 10)
    (top : ℝ) (k : ℕ) (hm : 0 < cellGapMass i) :
    Integrable (fun t => (scaledDeviation top (fun t => factors t j) t)^k)
      (cellProbability i) := by
  apply integrable_weightedProbability _ _ continuous_gap.measurable _ hm
    (cell_power_moment_integrable i j top k)
  filter_upwards [ae_restrict_mem (cell_measurable i)] with t ht
  exact hull_gap_nonneg (cell_subset_hull i ht)

def selectedSource : Set Point := ⋃ i : Fin 13, cell i

def selectedSaving : ℝ := ∫ t in selectedSource, conservativeDensity t

theorem selectedSource_measurable : MeasurableSet selectedSource :=
  MeasurableSet.iUnion cell_measurable

theorem selectedSource_subset_hull : selectedSource ⊆ analyticHull := by
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  exact cell_subset_hull i hi

theorem selectedSource_density_integrable : IntegrableOn conservativeDensity selectedSource :=
  hull_density_integrable.mono_set selectedSource_subset_hull

/-- Exact additivity on the ACTUAL thirteen complete strict domains.
All domains, disjointness and integrability are derived from original
source formulas; there is no desired saving or coverage input. -/
theorem selectedSaving_eq_sum_cells :
    selectedSaving = ∑ i : Fin 13, ∫ t in cell i, conservativeDensity t := by
  unfold selectedSaving selectedSource
  exact integral_iUnion_fintype cell_measurable
    (fun _ _ hij => strict_cells_disjoint hij) cell_density_integrable

theorem selectedSaving_nonneg : 0 ≤ selectedSaving := by
  rw [selectedSaving_eq_sum_cells]
  apply Finset.sum_nonneg
  intro i _
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (cell_measurable i)] with t ht
  exact cell_density_nonneg ht

end

end ImbalancedChen.P2OriginalSaving19SourceMeasure
