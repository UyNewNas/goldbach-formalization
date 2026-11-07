import ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
import ImbalancedChen.P5HistoricalCanonicalFilterReserve
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
One positive rational buffer precedes one refinement for all292633 original
typed positions. The TRUE22 support-gate and3 canonical-filter affine strips are paid by
augmenting the actual old-literal kernel modulus. History-invalid
and pointwise-invalid cores remain real geometric residuals.
This old-literal B13 estimate is not a new-common density/gain identity.
-/
namespace ImbalancedChen.P1HistoricalFifthFullBankStripSchedule
noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthJointMeshSchedule
open P1OriginalFifthLiteralKernelModulus P1HistoricalFifthIndexedOwnerArchive
open P1OriginalFifthQuantitativeGateRefinement
open P1HistoricalFifthIndexedBankError P1HistoricalFifthTypedBaseGeometry
open P1OriginalFifthAdoptedOwnerBank P5HistoricalIndexedTrimGeometry
open P5HistoricalRejectedCoreReserve P5HistoricalCanonicalFilterReserve

/-- The extra term is exactly the independently proved proper-affine
support+canonical-filter payment416*M_i*e after division by the raw-parent volume. -/
def stripAugmentedModulus (i : ArchiveIndex) (e : ℝ) : ℝ :=
  rowModulus (archiveRow i) e + (400 : ℝ)^5 * 416 * rowMassBound (archiveRow i) * e

theorem stripAugmentedModulus_continuousAt_zero (i : ArchiveIndex) :
    ContinuousAt (stripAugmentedModulus i) 0 := by
  have hc : ContinuousAt (rowModulus (archiveRow i)) 0 :=
    (rowModulus_continuous (archiveRow i)).continuousAt
  simpa only [stripAugmentedModulus] using hc.add
    (by fun_prop : ContinuousAt (fun e : ℝ =>
      (400 : ℝ)^5 * 416 * rowMassBound (archiveRow i) * e) 0)

theorem stripAugmentedModulus_zero (i : ArchiveIndex) : stripAugmentedModulus i 0 = 0 := by
  simp only [stripAugmentedModulus, rowModulus_zero, mul_zero, add_zero]

theorem augmented_rowEnvelope_eq (i : ArchiveIndex) (e : ℝ) :
    rowEnvelope stripAugmentedModulus (fun k => rowMassBound (archiveRow k)) i e =
      rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e + 416 * rowMassBound (archiveRow i) * e := by
  unfold rowEnvelope stripAugmentedModulus
  field_simp <;> ring

theorem augmented_bankEnvelope_eq (S : Finset ArchiveIndex) (e : ℝ) :
    bankEnvelope S stripAugmentedModulus (fun k => rowMassBound (archiveRow k)) e =
      bankEnvelope S (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) e + 416 * sourceMassSum S * e := by
  simp only [bankEnvelope, augmented_rowEnvelope_eq, Finset.sum_add_distrib,
    sourceMassSum, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- Complete source-index B13 bank, before choosing the parameters.
Only the actual old-literal kernel and its exact omitted trim are used. -/
theorem full_indexed_error_le_actual_envelope_trim
    (q : ℕ) (hq : 0 < q) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    |∑ i : ArchiveIndex, (indexedIntegral i e q chi omega e - parentIntegral (archiveRow i))| ≤
      bankEnvelope Finset.univ (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) e + licensedTrimCost e q chi omega := by
  calc
    _ ≤ ∑ i : ArchiveIndex,
        |indexedIntegral i e q chi omega e - parentIntegral (archiveRow i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ArchiveIndex,
        (rowEnvelope (fun k => rowModulus (archiveRow k)) (fun k => rowMassBound (archiveRow k)) i e +
          indexedTrimCost i e q chi omega) :=
      Finset.sum_le_sum (fun i _ => indexed_parent_error i (all_archive_indices_licensed i)
        q hq e he hemax chi omega hchi hstep)
    _ = _ := by simp only [bankEnvelope, licensedTrimCost, licensedIndices_eq_univ,
      Finset.sum_add_distrib]

/-- The single actual buffer/mesh schedule pays all kernel, crossing and
proper-affine support-gate errors. Only the two explicitly unpaid original
geometric cores remain. No smallness premise is substituted for them. -/
theorem exists_full_archive_schedule_with_actual_unpaid_cores
    (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      |∑ i : ArchiveIndex,
        (indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i))| <
        eta / 2 + canonicalHistoryBankCost q ((e : ℝ) / 20) omega +
          invalidCoreBankCost Finset.univ e q ((e : ℝ) / 20) omega := by
  obtain ⟨e, q, he, hecap, hq, _hchi, hchi10, hstep, hstepOmega, hbudget, _hcover⟩ :=
    exists_joint_buffer_mesh_complete_cover (Finset.univ : Finset ArchiveIndex)
      stripAugmentedModulus (fun i => rowMassBound (archiveRow i))
      (fun i _ => stripAugmentedModulus_continuousAt_zero i)
      (fun i _ => stripAugmentedModulus_zero i) (eta / 2) omega (by positivity) homega
  have heQ : (0 : ℚ) < e := by exact_mod_cast he
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by exact_mod_cast hecap.le
  have herror := full_indexed_error_le_actual_envelope_trim q hq e heQ.le hemaxQ
    ((e : ℝ) / 20) omega hchi10.le hstep
  have hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800 := by
    have hs : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ 1 / 800 := by
      linarith
    simpa only [cast_meshStepQ] using hs
  have htrim := actual_licensedTrimCost_le_invalid_regions_add_buffer_rate e heQ.le q
    ((e : ℝ) / 20) omega homega.le hw hh hstep hstep
  rw [licensedIndices_eq_univ] at htrim
  have haug := augmented_bankEnvelope_eq (Finset.univ : Finset ArchiveIndex) (e : ℝ)
  refine ⟨e, q, he, hecap, hq, hstep, hstepOmega, ?_⟩
  linarith

end
end ImbalancedChen.P1HistoricalFifthFullBankStripSchedule
