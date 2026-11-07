import ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
import ImbalancedChen.P1OriginalFifthUniformAdoptedBankError
import Mathlib

/-! SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
B13 is instantiated at the original full-table source indices. Row and
owner rejection stay explicit. The estimate does not identify the old
literal historical owner with a changed common-policy ancestor. -/
namespace ImbalancedChen.P1HistoricalFifthIndexedBankError
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthAdoptedOwnerBank
open P1OriginalFifthLiteralKernelModulus P1OriginalFifthJointMeshSchedule
open P1OriginalFifthMovingMeshFubiniBridge P1FifthUnitBoxGainDecomposition
open P1OriginalFifthActualB13IntegralError P1HistoricalFifthIndexedOwnerArchive

def indexedDomain (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) : Set (Fin 5 → ℝ) :=
  ownerUnion (archiveRow i) z chi (refinedMesh q) omega (licensedOwners i e q chi omega)

def indexedIntegral (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) : ℝ :=
  ∫ t in indexedDomain i e q chi omega z, positiveKernel (archiveRow i) (z : ℝ) t

def indexedOmitted (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : Set (Fin 5 → ℝ) :=
  fixedParent (archiveRow i) \ indexedDomain i e q chi omega 0

def indexedTrimMass (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∫ t in indexedOmitted i e q chi omega, positiveKernel (archiveRow i) 0 t

def indexedTrimCost (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound (archiveRow i) * (volume (indexedOmitted i e q chi omega)).toReal

theorem indexedDomain_subset_parent (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) :
    indexedDomain i e q chi omega z ⊆ fixedParent (archiveRow i) := by
  intro t ht
  obtain ⟨j, _hj, htj⟩ := mem_iUnion₂.mp ht
  exact ⟨htj.1, htj.2.2.1⟩

theorem indexedOmitted_measurable (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    MeasurableSet (indexedOmitted i e q chi omega) :=
  (fixedParent_measurable _).diff (ownerUnion_measurable _ _ _ _ _ _)

theorem indexedTrimMass_nonneg (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    0 ≤ indexedTrimMass i e q chi omega :=
  setIntegral_nonneg (indexedOmitted_measurable i e q chi omega) (fun _ _ => le_max_left _ _)

theorem indexed_parent_sub_baseline (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    parentIntegral (archiveRow i) - indexedIntegral i e q chi omega 0 =
      indexedTrimMass i e q chi omega := by
  have hg := licensedIndex_geometry i hi
  have h := setIntegral_sdiff (ownerUnion_measurable (archiveRow i) 0 chi (refinedMesh q) omega
      (licensedOwners i e q chi omega))
    (positiveKernel_integrableOn_of_subset (archiveRow i) 0 (fixedParent (archiveRow i))
      (fixedParent_subset_positiveCube _ hg.1 hg.2.2.1))
    (indexedDomain_subset_parent i e q chi omega 0)
  simpa only [parentIntegral, indexedIntegral, indexedDomain, indexedTrimMass,
    indexedOmitted, Rat.cast_zero] using h.symm

theorem indexedTrimMass_le_cost (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    indexedTrimMass i e q chi omega ≤ indexedTrimCost i e q chi omega := by
  have hg := licensedIndex_geometry i hi
  have hsub : indexedOmitted i e q chi omega ⊆ (archiveRow i).originalBox := fun _ ht => ht.1.1
  have hfinite : volume (indexedOmitted i e q chi omega) < ∞ :=
    (measure_mono hsub).trans_lt (by rw [rawBox_volume _ hg.1]; exact ENNReal.ofReal_lt_top)
  have hn := norm_setIntegral_le_of_norm_le_const hfinite (fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
    exact positive_kernel_le_rowMassBound (archiveRow i) 0 (by norm_num) t
      (fixedParent_subset_positiveCube _ hg.1 hg.2.2.1 ht.1))
  change ‖indexedTrimMass i e q chi omega‖ ≤ indexedTrimCost i e q chi omega at hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (indexedTrimMass_nonneg i e q chi omega)] using hn

theorem indexed_actual_B13 (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (q : ℕ) (hq : 0 < q) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    |indexedIntegral i e q chi omega e - indexedIntegral i e q chi omega 0| ≤
      rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e := by
  have hg := licensedIndex_geometry i hi
  simpa only [indexedIntegral, indexedDomain, rowEnvelope, Rat.cast_zero] using
    actual_selected_owner_B13 (archiveRow i) q hq hg.1 hg.2.2.1 hg.2.2.2
      e he hemax chi chi omega omega hchi hstep (licensedOwners i e q chi omega)
      (licensedOwner_selected_zero i e q chi omega)
      (licensedOwner_selected_buffer i e q chi omega)
      (licensedOwner_firstStop_zero i e q chi omega)
      (licensedOwner_firstStop_buffer i e q chi omega)

theorem indexed_parent_error (i : ArchiveIndex) (hi : i ∈ licensedIndices)
    (q : ℕ) (hq : 0 < q) (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    |indexedIntegral i e q chi omega e - parentIntegral (archiveRow i)| ≤
      rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e + indexedTrimCost i e q chi omega := by
  have hmove := indexed_actual_B13 i hi q hq e he hemax chi omega hchi hstep
  have hid := indexed_parent_sub_baseline i hi e q chi omega
  have htrim : |indexedIntegral i e q chi omega 0 - parentIntegral (archiveRow i)| =
      indexedTrimMass i e q chi omega := by
    rw [abs_sub_comm, hid, abs_of_nonneg (indexedTrimMass_nonneg i e q chi omega)]
  calc
    |indexedIntegral i e q chi omega e - parentIntegral (archiveRow i)| ≤
        |indexedIntegral i e q chi omega e - indexedIntegral i e q chi omega 0| +
          |indexedIntegral i e q chi omega 0 - parentIntegral (archiveRow i)| := abs_sub_le _ _ _
    _ ≤ rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e + indexedTrimMass i e q chi omega := by
      rw [htrim]
      exact add_le_add_right hmove _
    _ ≤ rowEnvelope (fun k => rowModulus (archiveRow k))
        (fun k => rowMassBound (archiveRow k)) i e + indexedTrimCost i e q chi omega :=
      add_le_add_left (indexedTrimMass_le_cost i hi e q chi omega) _

/-- Source INDEX sums preserve every original multiplicity. The unlicensed
source indices and missingOwners remain separately defined, not asserted
empty or supplied with an unproved finite/small mass. -/
def licensedBankError (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ licensedIndices,
    (indexedIntegral i e q chi omega e - parentIntegral (archiveRow i))

def licensedTrimCost (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ licensedIndices, indexedTrimCost i e q chi omega

theorem exists_actual_indexed_error_schedule (eta omega : ℝ) (heta : 0 < eta) (homega : 0 < omega) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      |licensedBankError e q ((e : ℝ) / 20) omega| <
        eta / 2 + licensedTrimCost e q ((e : ℝ) / 20) omega ∧
      (licensedTrimCost e q ((e : ℝ) / 20) omega ≤ eta / 2 →
        |licensedBankError e q ((e : ℝ) / 20) omega| < eta) := by
  obtain ⟨e, q, he, hecap, hq, _hchi, hchi10, hstep, hstepOmega, hbudget, _hcover⟩ :=
    exists_joint_buffer_mesh_complete_cover licensedIndices
      (fun i => rowModulus (archiveRow i)) (fun i => rowMassBound (archiveRow i))
      (fun i _ => (rowModulus_continuous (archiveRow i)).continuousAt)
      (fun i _ => rowModulus_zero (archiveRow i)) (eta / 2) omega (by positivity) homega
  have heQ : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  have hemaxQ : e ≤ (3 / 51200 : ℚ) := by exact_mod_cast hecap.le
  have hsum : |licensedBankError e q ((e : ℝ) / 20) omega| ≤
      bankEnvelope licensedIndices (fun i => rowModulus (archiveRow i))
        (fun i => rowMassBound (archiveRow i)) e + licensedTrimCost e q ((e : ℝ) / 20) omega := by
    calc
      |licensedBankError e q ((e : ℝ) / 20) omega| ≤
          ∑ i ∈ licensedIndices,
            |indexedIntegral i e q ((e : ℝ) / 20) omega e - parentIntegral (archiveRow i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ licensedIndices,
          (rowEnvelope (fun k => rowModulus (archiveRow k))
            (fun k => rowMassBound (archiveRow k)) i e + indexedTrimCost i e q ((e : ℝ) / 20) omega) :=
        Finset.sum_le_sum (fun i hi => indexed_parent_error i hi q hq e heQ hemaxQ
          ((e : ℝ) / 20) omega hchi10.le hstep)
      _ = bankEnvelope licensedIndices (fun i => rowModulus (archiveRow i))
          (fun i => rowMassBound (archiveRow i)) e + licensedTrimCost e q ((e : ℝ) / 20) omega :=
        Finset.sum_add_distrib
  have hstrict := hsum.trans_lt (add_lt_add_right hbudget _)
  refine ⟨e, q, he, hecap, hq, hstep, hstepOmega, hstrict, ?_⟩
  intro htrim
  linarith

end
end ImbalancedChen.P1HistoricalFifthIndexedBankError
