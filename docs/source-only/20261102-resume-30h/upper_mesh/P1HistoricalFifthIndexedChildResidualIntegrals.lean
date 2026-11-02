import ImbalancedChen.P1HistoricalFifthOriginalIndexedChildren
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact integral additivity on the independently defined original indexed
adopted bank and its actual omitted regions. The original mixed-radix
64-child partition cuts each source domain; no child floor, child admission,
or gain-density identification is assumed. The kernel in this file is the
original B13 positive literal kernel, not a renamed common physical rho.
The separate physical-charge consumer is in IndexedChildPhysicalAttachment.
-/
namespace ImbalancedChen.P1HistoricalFifthIndexedChildResidualIntegrals
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1FifthGrid400UnitBoxPartition P1OriginalFifthJointMeshSchedule
open P1OriginalFifthMovingMeshFubiniBridge
open P1OriginalFifthActualB13IntegralError P1OriginalFifthAdoptedOwnerBank
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedKeyPartition
open P1HistoricalFifthOriginalBlockContributions
open P1HistoricalFifthOriginalIndexedChildren P5OldFifthExact64ChildTiling

/-- A measurable subset of the true source parent has exactly the same
64 cuts as that parent. In particular the subset need not be a union of
whole children: partially retained and partially omitted children survive. -/
theorem source_subset_eq_union_child_inter (i : ArchiveIndex)
    (S : Set (Fin 5 → ℝ)) (hS : S ⊆ (archiveRow i).originalBox) :
    S = ⋃ c : ChildIndex, archiveChildBox (i, c) ∩ S := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc⟩ := parent_covered_by_child (archiveRow i) (archiveRow_grid i) t (hS ht)
    exact mem_iUnion.mpr ⟨c, hc, ht⟩
  · intro ht
    obtain ⟨c, hc⟩ := mem_iUnion.mp ht
    exact hc.2

theorem source_child_cuts_pairwise_disjoint (i : ArchiveIndex) (S : Set (Fin 5 → ℝ)) :
    Pairwise (fun c d : ChildIndex =>
      Disjoint (archiveChildBox (i, c) ∩ S) (archiveChildBox (i, d) ∩ S)) := by
  intro c d hne
  exact Set.disjoint_left.mpr (fun t hc hd =>
    hne (common_child_point_eq (archiveRow i) c d t hc.1 hd.1))

/-- The finite typed base-geometry source supplies integrability; it is
not a hypothesis asking for the desired integral identity. -/
theorem positiveKernel_integrableOn_source_subset (i : ArchiveIndex) (z : ℝ)
    (S : Set (Fin 5 → ℝ)) (hS : S ⊆ (archiveRow i).originalBox) :
    IntegrableOn (positiveKernel (archiveRow i) z) S := by
  apply positiveKernel_integrableOn_of_subset
  intro t ht
  apply fixedParent_subset_positiveCube (archiveRow i) (archiveRow_grid i)
    (archiveRow_baseGeometry i).2.2.1
  rw [archive_fixedParent_eq_originalBox]
  exact hS ht

/-- Analytic additivity for the actual old-literal kernel on any true
source subset. This reuses the exact original half-open child geometry. -/
theorem positiveKernel_integral_eq_actual_64_children (i : ArchiveIndex) (z : ℝ)
    (S : Set (Fin 5 → ℝ)) (hS : S ⊆ (archiveRow i).originalBox)
    (hSm : MeasurableSet S) :
    (∫ t in S, positiveKernel (archiveRow i) z t) =
      ∑ c : ChildIndex, ∫ t in archiveChildBox (i, c) ∩ S,
        positiveKernel (archiveRow i) z t := by
  have hi := positiveKernel_integrableOn_source_subset i z S hS
  calc
    _ = ∫ t in ⋃ c : ChildIndex, archiveChildBox (i, c) ∩ S,
        positiveKernel (archiveRow i) z t := by
      rw [← source_subset_eq_union_child_inter i S hS]
    _ = _ := integral_iUnion_fintype
      (fun c => (archiveChildBox_measurable (i, c)).inter hSm)
      (source_child_cuts_pairwise_disjoint i S)
      (fun _ => hi.mono_set inter_subset_right)

/-- The actual strict retained owner integral, with its original buffer
and kernel, is split on every child, including partially retained ones. -/
theorem indexedIntegral_eq_actual_64_children (i : ArchiveIndex)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) :
    indexedIntegral i e q chi omega z =
      ∑ c : ChildIndex, ∫ t in indexedChildRetained (i, c) e q chi omega z,
        positiveKernel (archiveRow i) (z : ℝ) t := by
  exact positiveKernel_integral_eq_actual_64_children i (z : ℝ)
    (indexedDomain i e q chi omega z)
    (fun _ ht => (indexedDomain_subset_parent i e q chi omega z ht).1)
    (ownerUnion_measurable _ _ _ _ _ _)

/-- In particular the true omitted mass is exactly a sum of 64 actual
omitted integrals, rather than a count of missing owner labels. -/
theorem indexedTrimMass_eq_actual_64_children (i : ArchiveIndex)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    indexedTrimMass i e q chi omega =
      ∑ c : ChildIndex, ∫ t in indexedChildOmitted (i, c) e q chi omega,
        positiveKernel (archiveRow i) 0 t := by
  exact positiveKernel_integral_eq_actual_64_children i 0
    (indexedOmitted i e q chi omega) (fun _ ht => ht.1.1)
    (indexedOmitted_measurable i e q chi omega)

theorem parentIntegral_eq_actual_64_children (i : ArchiveIndex) :
    parentIntegral (archiveRow i) =
      ∑ c : ChildIndex, ∫ t in archiveChildBox (i, c), positiveKernel (archiveRow i) 0 t := by
  rw [parentIntegral, archive_fixedParent_eq_originalBox]
  have h := positiveKernel_integral_eq_actual_64_children i 0
    (archiveRow i).originalBox Subset.rfl (measurableSet_originalBox _)
  have hcut (c : ChildIndex) : archiveChildBox (i, c) ∩ (archiveRow i).originalBox =
      archiveChildBox (i, c) := inter_eq_left.mpr (archiveChildBox_subset_original_parent (i, c))
  simpa only [hcut] using h

theorem indexedChildRetained_measurable (s : ArchiveChild)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) :
    MeasurableSet (indexedChildRetained s e q chi omega z) :=
  (archiveChildBox_measurable s).inter (ownerUnion_measurable _ _ _ _ _ _)

theorem indexedChildOmitted_measurable (s : ArchiveChild)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    MeasurableSet (indexedChildOmitted s e q chi omega) :=
  (archiveChildBox_measurable s).inter (indexedOmitted_measurable s.1 e q chi omega)

/-- The two real parts inside each original child are disjoint on every
face. Membership in another source cannot manufacture a second payment. -/
theorem indexedChild_retained_omitted_disjoint (s : ArchiveChild)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Disjoint (indexedChildRetained s e q chi omega 0)
      (indexedChildOmitted s e q chi omega) :=
  Set.disjoint_left.mpr (fun _ hr ho => ho.2.2 hr.2)

/-- One child's parent mass is paid once, by its genuine retained and
omitted masses. This has no finite/Rosser sign-monotonicity premise. -/
theorem actual_child_parent_mass_eq_retained_add_omitted (s : ArchiveChild)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (∫ t in archiveChildBox s, positiveKernel (archiveRow s.1) 0 t) =
      (∫ t in indexedChildRetained s e q chi omega 0, positiveKernel (archiveRow s.1) 0 t) +
      ∫ t in indexedChildOmitted s e q chi omega, positiveKernel (archiveRow s.1) 0 t := by
  have hi := positiveKernel_integrableOn_source_subset s.1 0 (archiveChildBox s)
    (archiveChildBox_subset_original_parent s)
  calc
    _ = ∫ t in indexedChildRetained s e q chi omega 0 ∪ indexedChildOmitted s e q chi omega,
        positiveKernel (archiveRow s.1) 0 t := by
      rw [← indexed_child_retained_omitted_partition s e q chi omega]
    _ = _ := setIntegral_union (indexedChild_retained_omitted_disjoint s e q chi omega)
      (indexedChildOmitted_measurable s e q chi omega)
      (hi.mono_set inter_subset_left) (hi.mono_set inter_subset_left)

/-- All 292633 source positions, each with all 64 original children.
The remaining omitted mass is visible in the exact adopted-bank ledger. -/
theorem full_original_parent_mass_eq_retained_add_omitted_children
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (∑ i : ArchiveIndex, parentIntegral (archiveRow i)) =
      (∑ s : ArchiveChild, ∫ t in indexedChildRetained s e q chi omega 0,
        positiveKernel (archiveRow s.1) 0 t) +
      ∑ s : ArchiveChild, ∫ t in indexedChildOmitted s e q chi omega,
        positiveKernel (archiveRow s.1) 0 t := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [parentIntegral_eq_actual_64_children i, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ =>
    actual_child_parent_mass_eq_retained_add_omitted (i, c) e q chi omega)

/-- The exact residual equals the original adopted-bank baseline loss;
there is no multiplication by the number of children or by an owner count. -/
theorem full_original_baseline_loss_eq_omitted_children
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (∑ i : ArchiveIndex,
      (parentIntegral (archiveRow i) - indexedIntegral i e q chi omega 0)) =
      ∑ s : ArchiveChild, ∫ t in indexedChildOmitted s e q chi omega,
        positiveKernel (archiveRow s.1) 0 t := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [indexed_parent_sub_baseline i (all_archive_indices_licensed i)]
  exact indexedTrimMass_eq_actual_64_children i e q chi omega

/-- This is the original ordered 143-block hub, not a synthetic named
bank or a Finset of row values. Source lookup preserves masks and keys. -/
theorem omitted_children_eq_original_143_block_residual
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (∑ s : ArchiveChild, ∫ t in indexedChildOmitted s e q chi omega,
      positiveKernel (archiveRow s.1) 0 t) =
      (Data.P1HistoricalFifthSavedTableData.blocks.toList.map (fun block =>
        (block.toList.map (fun raw => originalIndexContribution raw
          (fun i => indexedTrimMass i e q chi omega))).sum)).sum := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i : ArchiveIndex, indexedTrimMass i e q chi omega :=
      Finset.sum_congr rfl (fun i _ => (indexedTrimMass_eq_actual_64_children i e q chi omega).symm)
    _ = _ := indexed_sum_eq_original_143_blocks _

end
end ImbalancedChen.P1HistoricalFifthIndexedChildResidualIntegrals
