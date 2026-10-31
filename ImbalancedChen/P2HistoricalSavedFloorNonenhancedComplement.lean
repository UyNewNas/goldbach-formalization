import ImbalancedChen.P2HistoricalSavedFloorSourceChecksFinite
import ImbalancedChen.P2HistoricalSavedFloorStoredTotalFinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! UNCOMPILED DRAFT. Literal nonenhanced [mu,d] x [a,h] author-512 grid,
with the original actual sf/log producer and the original selected mask.
The unchanged enhanced [h,mu] block is not removed or represented by a
surrogate kernel. No complete L6 numeric replay or analytic licence is
assumed. The final theorem is the exact retained INTEGER-estimator identity. -/

namespace ImbalancedChen.P2HistoricalSavedFloorNonenhancedComplement

open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup (sourceSavedRectangle)
open P2HistoricalSavedFloorRowsBinder P2HistoricalSavedFloorFullBinder
open P2HistoricalSavedFloorSourceChecks P2HistoricalSavedFloorStoredTotal
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000

abbrev Grid := Fin 512 × Fin 512

/-- The selected row is embedded using its original grid indices, not
its provenance ordinal or its local strip index. -/
def gridIndex (r : Row) : Grid :=
  (⟨(indices r).1, (indices_bounds r).1⟩,
   ⟨(indices r).2, (indices_bounds r).2.2⟩)

theorem gridIndex_injective : Function.Injective gridIndex := by
  intro r s hrs
  apply indices_injective
  exact congrArg (fun p : Grid => (p.1.val, p.2.val)) hrs

def gridEmbedding : Row ↪ Grid := ⟨gridIndex, gridIndex_injective⟩

def selectedGrid : Finset Grid := Finset.univ.map gridEmbedding

theorem selectedGrid_card : selectedGrid.card = 17572 := by
  simpa only [selectedGrid, Finset.card_map, Finset.card_univ] using row_count

/-- Literal loop coordinates from author run(512,...): t0=mu+i*dt,
u0=a+j*du and upper endpoints are t0+dt,u0+du. -/
theorem grid_coordinates (p : Grid) :
    tLower p.1.val = mu + (p.1.val : ℚ) * ((d - mu) / 512) ∧
    tUpper p.1.val = (mu + (p.1.val : ℚ) * ((d - mu) / 512)) + (d - mu) / 512 ∧
    uLower p.2.val = a + (p.2.val : ℚ) * ((h - a) / 512) ∧
    uUpper p.2.val = (a + (p.2.val : ℚ) * ((h - a) / 512)) + (h - a) / 512 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    dsimp [tLower, tUpper, uLower, uUpper] <;> ring

/-- Exactly pair_cell(False,False), including its positive defect credit,
with sf(16384,8) and the original Q80 logarithm wrapper. -/
noncomputable def gridSourceOutput (p : Grid) : ℤ :=
  sourceSavedRectangle actualSf actualLog
    (tLower p.1.val) (tUpper p.1.val) (uLower p.2.val) (uUpper p.2.val)

theorem gridSourceOutput_on_row (r : Row) :
    gridSourceOutput (gridIndex r) = rowSourceOutput actualSf actualLog r := rfl

/-- Uses the proved original complete-output check, not an assumed saved
value or an ordinary-only check. -/
theorem original_row_source_eq_saved (r : Row) :
    rowSourceOutput actualSf actualLog r = (frozenSavedRow r).savedQ80 := by
  have hc : (frozenSavedRow r).tIndex = (indices r).1 ∧
      (frozenSavedRow r).uIndex = (indices r).2 ∧
      (frozenSavedRow r).savedQ80 = rowSourceOutput actualSf actualLog r :=
    of_decide_eq_true (all_source_checks r)
  exact hc.2.2.symm

/-- Actual selected producer outputs equal the independently proved exact
saved-field total. Neither the full 512² grid nor sf/log is evaluated again. -/
theorem selected_grid_source_sum :
    (∑ p ∈ selectedGrid, gridSourceOutput p) = (11290806845175652020270 : ℤ) := by
  calc
    (∑ p ∈ selectedGrid, gridSourceOutput p) =
        ∑ r : Row, rowSourceOutput actualSf actualLog r := by
      rw [selectedGrid, Finset.sum_map] <;> rfl
    _ = ∑ r : Row, (frozenSavedRow r).savedQ80 := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact original_row_source_eq_saved r
    _ = (11290806845175652020270 : ℤ) := frozen_saved_total

noncomputable def fullNonenhancedQ80 : ℤ := ∑ p : Grid, gridSourceOutput p

noncomputable def retainedNonenhancedQ80 : ℤ :=
  ∑ p ∈ Finset.univ \ selectedGrid, gridSourceOutput p

/-- Exact original nonenhanced estimator subtraction, with no duplicate
selected indices and no hypothesis about a desired lower integral bound. -/
theorem retained_non_enhanced_eq_full_sub_saved :
    retainedNonenhancedQ80 = fullNonenhancedQ80 - (11290806845175652020270 : ℤ) := by
  calc
    retainedNonenhancedQ80 = fullNonenhancedQ80 -
        ∑ p ∈ selectedGrid, gridSourceOutput p :=
      Finset.sum_sdiff_eq_sub (Finset.subset_univ selectedGrid)
    _ = fullNonenhancedQ80 - (11290806845175652020270 : ℤ) := by
      rw [selected_grid_source_sum]

end ImbalancedChen.P2HistoricalSavedFloorNonenhancedComplement
