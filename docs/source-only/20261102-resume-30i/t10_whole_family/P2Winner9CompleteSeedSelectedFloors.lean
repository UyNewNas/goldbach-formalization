import ImbalancedChen.P2Winner9CompleteSeedLogBranch
import ImbalancedChen.P2Winner9CompleteSeedChronology
import ImbalancedChen.P2Winner9CompleteSeedGapReserve
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
All original11026 selected maxima, and their common inward crop.
These remain sums of actual row integrals. No union/triangulation identity,
policy licence, density-to-count identity or current-c conclusion is asserted.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedSelectedFloors
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9CompleteSeedT10Q6
open ImbalancedChen.P2Winner9CompleteSeedLogBranch
open ImbalancedChen.P2Winner9CompleteSeedGapReserve

local notation "Q96" => P2Winner9CompleteSeedMomentDecoder.q96

/-- Every original array ordinal, including nonwinning candidates and zero
increments, is present. This is exact source coverage, not physical coverage. -/
theorem full_source_membership (n : ℕ) (hn : n < allRows.size) :
    ∃ i : RowIndex, i.val = n ∧ entry i = allRows[n]! ∧ (entry i).parentId = n := by
  have hn' : n < 11026 := by simpa only [full_source_shapes_and_chronology.1] using hn
  refine ⟨⟨n, hn'⟩, rfl, rfl, ?_⟩
  exact (full_source_shapes_and_chronology.2.2 ⟨n, hn'⟩).1

/-- Ordinal uniqueness does not assert null overlap of physical supports. -/
theorem source_member_unique (i j : RowIndex)
    (h : (entry i).parentId = (entry j).parentId) : i = j := by
  apply Fin.ext
  simpa only [(full_source_shapes_and_chronology.2.2 i).1,
    (full_source_shapes_and_chronology.2.2 j).1] using h

/-- Both branches have genuine same-support analytic proofs. No selected
row enclosure, arbitrary selected index cover or log-floor premise is used. -/
theorem all_original_selected_floors (i : RowIndex) :
    ((entry i).mixedSelected : ℝ) / (Q96 : ℝ) ≤ fullMass i := by
  have hq : (0 : ℝ) < (Q96 : ℝ) := by norm_num [P2Winner9CompleteSeedMomentDecoder.q96]
  have hlog := (div_le_iff₀ hq).1 (all_original_log_floors i)
  have hcur := (div_le_iff₀ hq).1 (all_original_curvature_raw_floors i)
  have hraw := (div_le_iff₀ hq).1 (all_original_raw_floors i)
  have hmax := P2Winner9CompleteSeedChronology.all_actual_row_maxima i
  have he : ((entry i).mixedSelected : ℝ) =
      max (max ((entry i).logSelected : ℝ) ((entry i).curvatureRaw : ℝ))
        ((entry i).mixedRaw : ℝ) := by
    rw [hmax.2.2.2, hmax.2.2.1]
    norm_cast
  apply (div_le_iff₀ hq).2
  rw [he]
  exact max_le (max_le hlog hcur) hraw

/-- The earlier selected curvature stage is also justified on all rows. -/
theorem all_original_curvature_selected_floors (i : RowIndex) :
    ((entry i).curvatureSelected : ℝ) / (Q96 : ℝ) ≤ fullMass i := by
  have hm : ((entry i).curvatureSelected : ℝ) ≤ (entry i).mixedSelected :=
    by exact_mod_cast (P2Winner9CompleteSeedChronology.all_actual_row_maxima i).2.1
  have hq : (0 : ℝ) ≤ (Q96 : ℝ) := by norm_num [P2Winner9CompleteSeedMomentDecoder.q96]
  exact (div_le_div_of_nonneg_right hm hq).trans (all_original_selected_floors i)

def selectedFloorSum : ℝ := ∑ i : RowIndex, ((entry i).mixedSelected : ℝ) / (Q96 : ℝ)

theorem selected_sum_eq_original : selectedFloorSum =
    (P2Winner9CompleteSeedChronology.mixedSelectedTotal : ℝ) := by
  norm_num [selectedFloorSum, P2Winner9CompleteSeedChronology.mixedSelectedTotal,
    P2Winner9CompleteSeedChronology.q96, P2Winner9CompleteSeedMomentDecoder.q96,
    Finset.sum_div]

theorem complete_selected_floor_sum : selectedFloorSum ≤ ∑ i : RowIndex, fullMass i :=
  Finset.sum_le_sum (fun i _ => all_original_selected_floors i)

/-- The original log sum and ledger slots21/22 occur exactly once. The slot
numbers are whole-family replacements, not simplex ordinals21 and22. -/
theorem original_slot_normalization : selectedFloorSum =
    (P2Winner9CompleteSeedChronology.adoptedLogTotal : ℝ) +
      (P2OriginalCertificateBudget.savingLower P2OriginalSeedChronologicalMaxArithmetic.slot21 : ℝ) +
      (P2OriginalCertificateBudget.savingLower P2OriginalSeedChronologicalMaxArithmetic.slot22 : ℝ) := by
  rw [selected_sum_eq_original]
  have h := congrArg (fun q : ℚ => (q : ℝ))
    P2Winner9CompleteSeedChronology.full_seed_slot_telescope
  push_cast at h
  linarith

/-- Actual all-row physical floors survive H's same common gap crop,
with one reserve charge for the full11026 family. No disjointness is used. -/
theorem complete_selected_floors_after_crop {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ reserveCutoff ε) :
    selectedFloorSum - ε < ∑ i : RowIndex, retainedMass i δ :=
  lt_of_le_of_lt (sub_le_sub_right complete_selected_floor_sum ε)
    (complete_family_retained_mass hε hδ hsmall)

theorem exists_common_margin_with_complete_floors {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℝ, 0 ≤ η → η ≤ δ →
      selectedFloorSum - ε < ∑ i : RowIndex, retainedMass i η := by
  refine ⟨reserveCutoff ε, reserveCutoff_pos hε, ?_⟩
  intro η hη hsmall
  exact complete_selected_floors_after_crop hε hη hsmall

end
end ImbalancedChen.P2Winner9CompleteSeedSelectedFloors

