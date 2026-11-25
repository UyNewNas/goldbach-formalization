import ImbalancedChen.P2OriginalCompactQ80CompleteSoundness
import ImbalancedChen.P2OriginalCompactCachedEndpointCandidate
import ImbalancedChen.P2OriginalCompactQ80FixedBindings
import ImbalancedChen.P2OriginalCompactArchivedTotalCandidate
import ImbalancedChen.P4AOrdinaryRootFirstIntegral
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNCHECKED / ALL FINITE BODIES UNEVALUATED.

Whole original functional consumer. Every complete source-forest entry is
paid by frozen L analytic soundness. The actual original run supplies its
forest and proved cached-total invariant; the frozen cached historical
candidate supplies the closed two-million-split comparison. Frozen N pays
the original first integral and original table/log32 tail, with no later
tail substitution. The compact correction occurs exactly once.

The shared production split/tail modules also contain later P112/Tnew
declarations. This consumer invokes their original split only and uses N's
original table-anchor tail supplier; those later declarations are unused.

All final interfaces have no arguments: no leaf, geometry, Run, total,
fixed-source, tail, compact or global endpoint premise is accepted.
Importing the UNEVALUATED candidates is not kernel closure or a claim that
their finite guards returned true. Broad targets remain OPEN, credit zero.
-/
namespace ImbalancedChen.P2OriginalCompactWholeFunctionalEndpointSourceOnly

noncomputable section
open MeasureTheory
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactConcreteLoopSourceOnly
open P2OriginalPriorityForestLedgerSourceOnly
open P2OriginalCompactArchivedTotalCandidateSourceOnly

/-- The production compact correction and frozen source partition use the
same entire original domain and kernel. The cutoff face is paid by the
existing strict/closed-domain theorem; the kernel already contains factor 4. -/
theorem original_production_compact_eq_source_integral :
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection =
      ∫ t in OriginalThirdCompactPartitionSourceOnly.compactRegion,
        OriginalThirdCompactPartitionSourceOnly.compactKernel t := by
  simpa only [OriginalThirdCompactPartitionSourceOnly.compactRegion,
    OriginalThirdCompactPartitionSourceOnly.compactKernel] using
    OriginalThirdCompactEndpointSourceOnly.originalCompactThirdCorrection_eq_literal_closed_compact

/-- All terminal source entries, including exact and empty leaves, contribute
to this integer total. The guarded complete multiplicity is 21 + 2000000,
with no heap filter. Both fields consume the frozen historical candidate. -/
theorem original_complete_forest_upper_sum_and_length :
    upperSum (entries originalRun.state.forest) = historicalUpper ∧
      (entries originalRun.state.forest).length = 2000021 := by
  have hcheck :=
    P2OriginalCompactCachedEndpointCandidateSourceOnly.originalHistoricalEndpointCheck_viaCache_candidate
  have hfields := historical_check_fields hcheck
  have hcharges := historical_ordered_charge_fields hcheck
  refine ⟨originalRun_ledger.2.symm.trans hfields.2.1, ?_⟩
  simpa only [orderedUpperCharges, List.length_map] using hcharges.2

/-- Complete L analytic soundness is instantiated at the actual original
source forest. No K.Run witness or local charge/enclosure premise occurs. -/
theorem original_compact_le_historical_upper :
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection ≤
      val historicalUpper := by
  have h :=
    P2OriginalCompactQ80CompleteSoundnessSourceOnly.forest_integral_enclosure
      originalRun.state.forest
  rw [original_complete_forest_upper_sum_and_length.1] at h
  exact h.2

/-- Literal source-domain version of the same complete compact enclosure. -/
theorem original_source_compact_integral_le_historical_upper :
    (∫ t in OriginalThirdCompactPartitionSourceOnly.compactRegion,
      OriginalThirdCompactPartitionSourceOnly.compactKernel t) ≤
        val historicalUpper := by
  rw [← original_production_compact_eq_source_integral]
  exact original_compact_le_historical_upper

/-- Exact whole-functional dictionary. The full original noncompact tail
and the entire compact correction each appear once; there is no subtraction
of an old tail and no replacement by a later anchor. -/
theorem original_whole_functional_eq_fixed_source_add_compact :
    4 / (299 / 500 : ℝ) + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
        actualExtendedThirdIdealFunctional =
      (4 / (299 / 500 : ℝ) + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
        (∫ t in actualExtendedThirdManuscriptTailRegion 0 (1 / 100),
          actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2))) +
        (∫ t in OriginalThirdCompactPartitionSourceOnly.compactRegion,
          OriginalThirdCompactPartitionSourceOnly.compactKernel t) := by
  rw [OriginalThirdFiniteReserveSourceOnly.idealFunctional_eq_compact_add_original_tail,
    ← original_production_compact_eq_source_integral]
  ring

/-- Real cast of the exact source equality candidate. The original fixed
source formula is retained, including its original directed tail rounding. -/
theorem original_fixed_plus_compact_cast_eq_archived_candidate :
    (P2OriginalCompactQ80EncloserSourceOnly.fixedUpper : ℝ) + val historicalUpper =
      (1230679674488580033396846301 / 180734410032387061618573312 : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ))
    original_fixed_plus_original_compact_eq_archived_candidate
  simpa only [archivedOriginalUpper, val, Rat.cast_add, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_ofNat] using h

/-- Closed whole-original endpoint source candidate. Frozen L supplies the
actual complete compact bound, N supplies its original fixed source, and the
separate finite equality candidate identifies the exact archived rational. -/
theorem original_whole_functional_le_archived_upper :
    4 / (299 / 500 : ℝ) + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
        actualExtendedThirdIdealFunctional ≤
      (1230679674488580033396846301 / 180734410032387061618573312 : ℝ) := by
  calc
    _ = _ := original_whole_functional_eq_fixed_source_add_compact
    _ ≤ (P2OriginalCompactQ80EncloserSourceOnly.fixedUpper : ℝ) + val historicalUpper :=
      add_le_add
        P2OriginalCompactQ80FixedBindingsSourceOnly.original_fixed_manuscript_source_le_fixedUpper
        original_source_compact_integral_le_historical_upper
    _ = _ := original_fixed_plus_compact_cast_eq_archived_candidate

/-- Transparent small rational comparison, authored but UNEVALUATED. -/
theorem archived_upper_lt_681 :
    (1230679674488580033396846301 / 180734410032387061618573312 : ℝ) < 681 / 100 := by
  norm_num

/-- The actual envelope is above the old 6809/1000 stopping target. This is
only an order fact about the archived upper rational, not a lower bound on
the original integral and not an assertion of successful target crossing. -/
theorem stop_target_lt_archived_upper :
    (6809 / 1000 : ℝ) <
      1230679674488580033396846301 / 180734410032387061618573312 := by
  norm_num

/-- Original whole functional at the supported 681/100 endpoint. -/
theorem original_whole_functional_le_681 :
    4 / (299 / 500 : ℝ) + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
        actualExtendedThirdIdealFunctional ≤ (681 / 100 : ℝ) :=
  original_whole_functional_le_archived_upper.trans archived_upper_lt_681.le

/-- Exact ordinary-root dictionary consumer. This states an original
analytic functional bound, with no physical-density or current-K claim. -/
theorem original_ordinary_root_and_third_le_archived_upper :
    P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdIdealFunctional ≤
      (1230679674488580033396846301 / 180734410032387061618573312 : ℝ) := by
  rw [P4AOrdinaryRootFirstIntegral20261024zSourceOnly.originalOrdinaryRoot_eq_literal_constant_add_U1]
  exact original_whole_functional_le_archived_upper

end
end ImbalancedChen.P2OriginalCompactWholeFunctionalEndpointSourceOnly
