import ImbalancedChen.P2Winner9LedgerBridge
import ImbalancedChen.P2Winner9ArchiveIntegral
import ImbalancedChen.P2Winner9CompletePullingGeometry
import ImbalancedChen.P2Winner9CompleteNumericalChecks

/-! SOURCE ONLY / NOT COMPILED.
Assembly of the original complete Winner9 ledger at literal terminal 41.
The complete numerical and pulling modules must be accepted before this
closed statement receives any formal credit. The original Full87 cellIntegral
identity is a separate bridge; it is not asserted by this file.
-/

namespace ImbalancedChen.P2Winner9CompleteSeedTerminal

open Set MeasureTheory
open P2Winner9CompleteSeedData (RowIndex entry full_source_shapes_and_chronology selected_eq_max_log_mixed)
open P2Winner9CompleteSeedChronology (adoptedLogTotal selected_real_sum_eq)
open P2Winner9RowArithmeticChecker (archiveVertices)
open P2Winner9SelectedRowRealJacobian (sourceSupport)
open P2Winner9SeedVertexAnalyticGuards (VertexIndex originalPoint)
open P2Winner9OriginalSourceGates (originalClosedSource originalPhysicalSource sourceWalls
  sourceWalls_null all_supports_in_closed_source support_off_walls_in_original_source)
open P2Winner9OriginalSourceIntegral (original_closed_source_density_integrable)
open P2Winner9PhysicalAffineTransfer (Ambient physicalUpperIntegrand)
open P2Winner9OriginalTerminal (terminal41Integral terminal41_integral_eq)
open P2Winner9ArchiveIntegral (checked_family_floor)
open P2OriginalCertificateBudget (savingLower)
open P2OriginalSeedChronologicalMaxArithmetic (slot21 slot22)

private def vertexIndex (i : RowIndex) (k : Fin 9) : VertexIndex :=
  ⟨(entry i).vertexIds k, (full_source_shapes_and_chronology.2.2 i).2.2.2.2.1 k⟩

theorem each_support_in_closed_source (i : RowIndex) :
    sourceSupport (archiveVertices (entry i)) ⊆ originalClosedSource :=
  all_supports_in_closed_source (archiveVertices (entry i)) (vertexIndex i) (fun _ => rfl)

theorem each_support_ae_in_original_source (i : RowIndex) :
    sourceSupport (archiveVertices (entry i)) ≤ᵐ[volume] originalPhysicalSource := by
  have hnull : ∀ᵐ x : Ambient ∂volume, x ∉ sourceWalls := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using sourceWalls_null
  filter_upwards [hnull] with x hx hmem
  exact support_off_walls_in_original_source (archiveVertices (entry i)) (vertexIndex i)
    (fun _ => rfl) ⟨hmem, hx⟩

theorem each_support_density_integrable (i : RowIndex) :
    IntegrableOn physicalUpperIntegrand (sourceSupport (archiveVertices (entry i))) :=
  original_closed_source_density_integrable.mono_set (each_support_in_closed_source i)

/-- The finite row checks and geometric null-overlap certificates supply
the adopted log bound plus the two original ledger increments. -/
theorem complete_seed_ledger_le_terminal41 :
    (adoptedLogTotal : ℝ) + (savingLower slot21 : ℝ) + (savingLower slot22 : ℝ) ≤
      terminal41Integral := by
  rw [← selected_real_sum_eq, terminal41_integral_eq]
  exact checked_family_floor entry
    (fun i k => (full_source_shapes_and_chronology.2.2 i).2.2.2.2.1 k)
    selected_eq_max_log_mixed P2Winner9CompleteNumericalChecks.selected_checked
    P2Winner9CompletePullingGeometry.complete_seed_actual_overlap_null

end ImbalancedChen.P2Winner9CompleteSeedTerminal
