import ImbalancedChen.P2Winner9ArchiveIntegral
import ImbalancedChen.P2Winner9OriginalPullingFlags
import ImbalancedChen.P2Winner9RowZeroLog
import ImbalancedChen.P2Winner9SeedArchiveCheck00
import ImbalancedChen.P2Winner9SelectedRowArchiveBinding

/-! The contribution of original rows 0, 21, and 22 to terminal 41. -/

namespace ImbalancedChen.P2Winner9Terminal41ThreeRows

open MeasureTheory
open P2Winner9CompleteSeedBlock00 (rows)
open P2Winner9CurvatureExactMomentFloor (q96)
open P2Winner9RowArithmeticChecker (archiveVertices)
open P2Winner9SelectedRowRealJacobian (sourceSupport)
open P2Winner9PhysicalAffineTransfer (physicalUpperIntegrand)
open P2Winner9OriginalTerminal (terminal41Integral terminal41_integral_eq)
open P2Winner9ArchiveIntegral (archive_family_integrals_le_original)

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def index (i : Fin 3) : Fin 256 := (![0, 21, 22] : Fin 3 → Fin 256) i

private theorem index_injective : Function.Injective index := by
  unfold Function.Injective
  decide +kernel

private def entry (i : Fin 3) : P2Winner9CompleteSeedTypes.RawRow := rows[(index i).val]!

private theorem vertex_ids_lt (i : Fin 3) (k : Fin 9) : (entry i).vertexIds k < 201 :=
  (P2Winner9SeedArchiveCheck00.checked.2 (index i)).1.2.2.2.2.1 k

private theorem overlap_null : Pairwise fun i j : Fin 3 =>
    volume (sourceSupport (archiveVertices (entry i)) ∩
      sourceSupport (archiveVertices (entry j))) = 0 := by
  intro i j hij
  exact @P2Winner9OriginalPullingFlags.block00_actual_overlap_null (index i) (index j)
    (fun h => hij (index_injective h))

private theorem row_floor (i : Fin 3) :
    ((entry i).mixedSelected : ℝ) / (q96 : ℝ) ≤
      ∫ z in sourceSupport (archiveVertices (entry i)), physicalUpperIntegrand z := by
  fin_cases i
  · exact P2Winner9RowZeroLog.row_zero_selected_floor
  · exact P2Winner9SelectedRowArchiveBinding.archive_selected_floor 0
  · exact P2Winner9SelectedRowArchiveBinding.archive_selected_floor 1

private theorem numerator : ∑ i : Fin 3, (entry i).mixedSelected = 1481070658756950770602 := by
  decide +kernel

theorem terminal41_lower_three_rows :
    (1481070658756950770602 : ℝ) / 79228162514264337593543950336 ≤ terminal41Integral := by
  rw [terminal41_integral_eq]
  calc
    (1481070658756950770602 : ℝ) / 79228162514264337593543950336 =
        ∑ i : Fin 3, ((entry i).mixedSelected : ℝ) / (q96 : ℝ) := by
      change (1481070658756950770602 : ℝ) / (q96 : ℝ) = _
      rw [← Finset.sum_div, ← Nat.cast_sum, numerator]
      norm_num
    _ ≤ ∑ i : Fin 3, ∫ z in sourceSupport (archiveVertices (entry i)), physicalUpperIntegrand z :=
      Finset.sum_le_sum fun i _ => row_floor i
    _ ≤ _ := archive_family_integrals_le_original entry vertex_ids_lt overlap_null

end ImbalancedChen.P2Winner9Terminal41ThreeRows
