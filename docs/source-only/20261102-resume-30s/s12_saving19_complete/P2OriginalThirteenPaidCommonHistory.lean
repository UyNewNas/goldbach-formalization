import ImbalancedChen.P2OriginalSaving19OwnedIntegral
import ImbalancedChen.P4AOriginalFourteenThirteenCurrentSource
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original 97 strict rows give concrete compact inner trims of exactly
the original thirteen source.  Their actual density omission tends to zero.
The existing no-argument Q96 endpoint and the existing common ancestor
constructor then hold on the same paid trim with one precision before N.
No endpoint, compact coverage, positive history margin or cap licence is
an input.  Arithmetic tuple admission and the integrated mean are separate.
-/
namespace ImbalancedChen.P2OriginalThirteenPaidCommonHistory
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P2OriginalThirdMinorantLogDictionarySourceOnly
open OriginalAscendingThirteenCellOwnership
open OriginalAscendingThirteenLiteralAffineRows
open OriginalAscendingThirteenExportOwnershipJoin
open OriginalDescendingFifteenLiteralAffineRows (evaluateCoefficients)
open P2OriginalSaving19SourceMeasure
open P4AOriginalSaving19CommonHistory
open P4AOriginalArchiveFourteenPositivePresieve
open P4AOriginalFourteenThirteenCurrentSource
open P4AOriginalLive171819PrimeBank P4AOriginalLive171819CommonParent
open P5OriginalCommonRefinedConstructor

def width (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

theorem width_tendsto : Tendsto width atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The two source identities are absent from the original 97 strict
rows.  This trim preserves their identities and the original cell labels. -/
def trimmedCell (delta : ℝ) (i : Fin 13) : Set Point :=
  analyticHull ∩ ⋂ r : Fin 97, {t | delta ≤ evaluateCoefficients (exportedCoefficients i r) t}

def trimmedSource (delta : ℝ) : Set Point := ⋃ i : Fin 13, trimmedCell delta i

def trimmedSaving (delta : ℝ) : ℝ := ∫ t in trimmedSource delta, conservativeDensity t

theorem isCompact_trimmedCell (delta : ℝ) (i : Fin 13) :
    IsCompact (trimmedCell delta i) := by
  apply analyticHull_compact.of_isClosed_subset
  · apply analyticHull_closed.inter
    apply isClosed_iInter
    intro r
    apply isClosed_le continuous_const
    unfold evaluateCoefficients
    fun_prop
  · exact inter_subset_left

theorem isCompact_trimmedSource (delta : ℝ) : IsCompact (trimmedSource delta) :=
  isCompact_iUnion (fun i => isCompact_trimmedCell delta i)

theorem trimmedCell_subset_original (delta : ℝ) (hdelta : 0 < delta) (i : Fin 13) :
    trimmedCell delta i ⊆ cell i := by
  intro t ht
  apply (strictExportedRows_iff_StrictRows i t).mp
  intro r
  exact hdelta.trans_le (mem_iInter.mp ht.2 r)

theorem trimmedSource_subset_original (delta : ℝ) (hdelta : 0 < delta) :
    trimmedSource delta ⊆ selectedSource := by
  intro t ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨i, trimmedCell_subset_original delta hdelta i hi⟩

theorem source_eventually_trimmed {t : Point} (ht : t ∈ selectedSource) :
    ∀ᶠ n : ℕ in atTop, t ∈ trimmedSource (width n) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  have hrows := (strictExportedRows_iff_StrictRows i t).mpr hi
  have hall : ∀ᶠ n : ℕ in atTop, ∀ r : Fin 97,
      width n < evaluateCoefficients (exportedCoefficients i r) t := by
    apply eventually_all.mpr
    intro r
    exact width_tendsto.eventually (gt_mem_nhds (hrows r))
  filter_upwards [hall] with n hn
  exact mem_iUnion.mpr ⟨i, cell_subset_hull i hi, mem_iInter.mpr (fun r => (hn r).le)⟩

/-- Actual density convergence on the original selected source.  It uses
the existing source-specific integrability and all original proper rows. -/
theorem tendsto_trimmedSaving :
    Tendsto (fun n => trimmedSaving (width n)) atTop (𝓝 selectedSaving) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict selectedSource)
    (F := fun n => (trimmedSource (width n)).indicator conservativeDensity)
    (f := conservativeDensity) (fun t => ‖conservativeDensity t‖)
    (fun n => (selectedSource_density_integrable.indicator
      (isCompact_trimmedSource (width n)).measurableSet).aestronglyMeasurable)
    selectedSource_density_integrable.norm
    (fun n => Eventually.of_forall (fun t =>
      norm_indicator_le_norm_self (s := trimmedSource (width n)) conservativeDensity t))
    (show ∀ᵐ t ∂volume.restrict selectedSource,
      Tendsto (fun n => (trimmedSource (width n)).indicator conservativeDensity t)
        atTop (𝓝 (conservativeDensity t)) from by
      filter_upwards [ae_restrict_mem selectedSource_measurable] with t ht
      apply tendsto_const_nhds.congr'
      filter_upwards [source_eventually_trimmed ht] with n hn
      simp only [indicator_of_mem hn])
  have hinter (n : ℕ) : selectedSource ∩ trimmedSource (width n) = trimmedSource (width n) :=
    inter_eq_right.mpr (trimmedSource_subset_original (width n) (width_pos n))
  simpa only [setIntegral_indicator (isCompact_trimmedSource _).measurableSet, hinter,
    trimmedSaving, selectedSaving] using hlim

/-- One actual paid source and precision for ALL thirteen cells.  This
combines the existing complete M endpoint with the original causal third
lookup; it does not substitute B3 for lambda3 or R for the current lambda6.
Every e,q,omega and later arithmetic state uses that one precision. -/
theorem exists_paid_original_history (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ precision : ℝ, 0 < precision ∧
      |selectedSaving - trimmedSaving (width n)| < epsilon ∧
      (283388722705335806564439 : ℝ) / (2 : ℝ)^96 - epsilon < trimmedSaving (width n) ∧
      ∀ (e : ℚ), 0 ≤ e → (e : ℝ) ≤ precision → ∀ (q : ℕ) (omega : ℝ)
        (i : Fin 13) (N cap : ℕ), 1 < N → ∀ (w z : ℝ) (s : FirstExitDepthState ℕ),
        s ∈ selected (.ascending19 i) (data e q omega).e (data e q omega).chi
          (data e q omega).m (data e q omega).omega N cap w z
          (fourteenPolicy e q omega (N : ℝ)) →
        point8 (N : ℝ) s.selectedPrefix ∈ trimmedSource (width n) →
        3 * point8 (N : ℝ) s.selectedPrefix 0 <
            lambda3 (data e q omega) (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
          history3 (point8 (N : ℝ) s.selectedPrefix) <
            lambda3 (data e q omega) (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
          history5 (point8 (N : ℝ) s.selectedPrefix) <
            lambda3 (data e q omega) (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
          history7 (point8 (N : ℝ) s.selectedPrefix) <
            lambda3 (data e q omega) (N : ℝ) (rosserAncestor 4 s.selectedPrefix) := by
  have hzero : Tendsto (fun n => |selectedSaving - trimmedSaving (width n)|)
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds.sub tendsto_trimmedSaving).abs
    simpa only [sub_self, abs_zero] using hh
  obtain ⟨n, hn⟩ := (hzero.eventually (gt_mem_nhds hepsilon)).exists
  have hsource : ∀ t ∈ trimmedSource (width n), ∃ i : Fin 13, StrictRows i t := by
    intro t ht
    exact mem_iUnion.mp (trimmedSource_subset_original (width n) (width_pos n) ht)
  obtain ⟨precision, hp, hcommon⟩ := compact_selected_common_third_histories
    (trimmedSource (width n)) (isCompact_trimmedSource _) hsource
  refine ⟨n, precision, hp, hn, ?_, ?_⟩
  · have hendpoint := P2OriginalSaving19OwnedIntegral.original_endpoint_le_selectedSaving
    have hloss := (abs_lt.mp hn).2
    linarith
  · intro e he heprecision q omega i N cap hN w z s hs ht
    have heR : 0 ≤ (e : ℝ) := by exact_mod_cast he
    have hchi : (data e q omega).chi ≤ precision := by
      change (e : ℝ) / 20 ≤ precision
      linarith
    have hs6 := hs
    rw [original_thirteen_selected_list_preserved] at hs6
    have hs8 : s ∈ selected (.ascending19 i) (data e q omega).e (data e q omega).chi
        (data e q omega).m (data e q omega).omega N cap w z
        (policy8 (data e q omega) (N : ℝ)) := by
      unfold selected at hs6 ⊢
      rwa [P5OriginalCommonRefinedAncestry.policy8_frontier_eight_eq_six]
    exact hcommon (data e q omega) heR heprecision hchi i N cap hN w z s hs8 ht

end
end ImbalancedChen.P2OriginalThirteenPaidCommonHistory
