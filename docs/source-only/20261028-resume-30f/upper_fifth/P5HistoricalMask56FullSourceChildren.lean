import ImbalancedChen.P5OriginalGenericWireFloorReceiver
import ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
import ImbalancedChen.P5OriginalLicensedTrimResidual

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The source family is the FULL original indexed typed archive filtered by
exact ORIGINAL mask5/mask6 whole-raw third-plus-pair licences. It is not
two named parents, not BASE geometry, and not a new small row model.
Source order/multiplicity and all ten parent fields remain attached to i.

Each actual parent has64 children. The old128 count belonged only to the
two named examples and is NOT duplicated here. The full finite wire facts
are CLOSED DECISION SOURCE awaiting execution; no checker/Lean run or
proof acceptance is claimed. The full archive byte-authenticity problem,
unlicensed rows, strict owner rejects and changed-common-parent residuals
are explicitly NOT removed by the finite source proposal.
-/
namespace ImbalancedChen.P5HistoricalMask56FullSourceChildren

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1HistoricalFifthIndexedOwnerArchive
open P5OriginalLicensedTrimResidual
open P5OriginalGenericWireFloorReceiver
open P5OriginalChildIntegerWireBinding
open P5OldFifthExact64ChildTiling

/-- Exactly the original two nonleading-pair history licences, not the
independent fifth raw.mask value and not a proxy numerical-floor flag. -/
def mask56Indices : Finset ArchiveIndex :=
  Finset.univ.filter (fun i => ownerLicenseCheck (archiveRow i) = true)

def unlicensedMaskIndices : Finset ArchiveIndex := Finset.univ \ mask56Indices

theorem mask56Index_iff (i : ArchiveIndex) :
    i ∈ mask56Indices ↔ ownerLicenseCheck (archiveRow i) = true := by
  simp [mask56Indices]

/-- Full original finite family, not a smaller chosen sample. This is
unexecuted theorem source; blockwise execution/proof acceptance is pending.
The checks are finite rational field identities, domains and vertex values;
no desired real integral/mean/upper/PP conclusion occurs in their statement. -/
theorem proposed_full_mask56_source_child_facts :
    ∀ i : ArchiveIndex, ownerLicenseCheck (archiveRow i) = true →
      ∀ c : ChildIndex, SourceChildFacts (archiveRow i) c := by
  decide

noncomputable section
open Set MeasureTheory
open scoped Classical
open P1OriginalVariableFifthContinuation P1OriginalCoarseFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthUnitBoxGainDecomposition P1FifthUnitBoxLiteralGainLower
open P1FifthPositivePartActualOwner
open P5ChildSelectedOwnerJensenReserve

/-- The actual source licence supplies BASE geometry; the converse is
never asserted. No BASE-only row is silently promoted to a licensed one. -/
theorem mask56Index_is_base (i : ArchiveIndex) (hi : i ∈ mask56Indices) :
    i ∈ P1HistoricalFifthIndexedOwnerArchive.licensedIndices := by
  have hg := licensed_primitive_key_bounds (archiveRow i) ((mask56Index_iff i).mp hi)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩

theorem mask56_index_geometry (i : ArchiveIndex) (hi : i ∈ mask56Indices) :
    (archiveRow i).grid = 400 ∧ 0 ≤ (archiveRow i).mask ∧
      (∀ k : Fin 5, 1 ≤ (archiveRow i).lo k) ∧ (archiveRow i).lo 0 ≤ 77 :=
  licensed_primitive_key_bounds (archiveRow i) ((mask56Index_iff i).mp hi)

/-- Rejection is exactly the remaining original source positions. No
multiplicity is lost by converting row VALUES into a Finset. -/
theorem unlicensed_mask_index_exact (i : ArchiveIndex) :
    i ∈ unlicensedMaskIndices ↔
      P1FifthMask5RawOwnerLicence.mask5WholeRawCheck (archiveRow i) = false ∧
      P1FifthMask6RawOwnerLicence.mask6WholeRawCheck (archiveRow i) = false := by
  simp [unlicensedMaskIndices, mask56Indices, ownerLicenseCheck]

theorem full_mask_source_partition : mask56Indices ∪ unlicensedMaskIndices = Finset.univ := by
  ext i
  simp [unlicensedMaskIndices]

theorem full_mask_source_partition_disjoint : Disjoint mask56Indices unlicensedMaskIndices := by
  apply Finset.disjoint_left.mpr
  intro i hi hr
  exact (Finset.mem_sdiff.mp hr).2 hi

/-- The same ten signed parent fields are kept, including their ORIGINAL
parent d/A/B. Recomputed child d/A/B never overwrite those stored fields. -/
theorem original_parent_fields_unchanged (i : ArchiveIndex) :
    P1HistoricalFifthTypedArchiveShape.namedRow (archiveRow i) =
      [("n", (archiveRow i).grid), ("l1", (archiveRow i).lo 0),
       ("l2", (archiveRow i).lo 1), ("l3", (archiveRow i).lo 2),
       ("l4", (archiveRow i).lo 3), ("l5", (archiveRow i).lo 4),
       ("mask", (archiveRow i).mask), ("vertex_gap_sum", (archiveRow i).vertexGapSum),
       ("A", (archiveRow i).ratioA), ("B", (archiveRow i).ratioB)] :=
  archiveRow_ten_columns i

/-- Exact strict owner set from the independent full indexed archive,
with BOTH original0/e selected/firstStop and BOTH full/selected-square gates. -/
theorem selected_strict_owners_eq (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    selectedFifthCells e chi (refinedMesh q) omega (licensedOwners i e q chi omega) =
      licensedOwners i e q chi omega := by
  ext j
  constructor
  · intro hj
    exact ((mem_selectedFifthCells e chi (refinedMesh q) omega _ j).mp hj).1
  · exact licensedOwner_selected_buffer i e q chi omega j

def indexedWireFloor64 (i : ArchiveIndex) : ℚ :=
  ∑ c : ChildIndex, rowFloorQ (archiveRow i) c

def indexedActualReserve64 (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ c : ChildIndex, childOwnerReserve (archiveRow i) c e chi (refinedMesh q) omega
    (licensedOwners i e q chi omega)

/-- A full-family per-parent soundness statement. Its sole data use is the
closed finite theorem source above; no per-parent hJensen/hFloor premise.
The TRUE selected-owner reserve remains on the left, including all strict
fifth-gate rejects. No arbitrary-small reserve is inferred here. -/
theorem each_licensed_parent64_source_floor_minus_actual_reserve
    (i : ArchiveIndex) (hi : i ∈ mask56Indices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (indexedWireFloor64 i : ℝ) - indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        literalPositiveRawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j := by
  have hg := mask56_index_geometry i hi
  have hf := proposed_full_mask56_source_child_facts i ((mask56Index_iff i).mp hi)
  have hs := original_parent64_wire_floor_sub_reserve (archiveRow i) hg.1 hg.2.2.1 hf
    e chi (refinedMesh q) omega (licensedOwners i e q chi omega)
  rw [selected_strict_owners_eq] at hs
  simpa [indexedWireFloor64, indexedActualReserve64] using hs

/-- Exact64-child original signed-kernel identity for the SAME actual
owner j, retaining its original firstStop/current parent and strict cubes. -/
theorem each_licensed_parent_same_owner_signed64
    (i : ArchiveIndex) (hi : i ∈ mask56Indices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (j : Label5 (refinedMesh q)) :
    literalRawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j =
      ∑ c : ChildIndex,
        ∫ t in childOwnerDomain (archiveRow i) c e chi (refinedMesh q) omega j,
          literalRawKernel (e : ℝ) (archiveRow i) t := by
  have hg := mask56_index_geometry i hi
  exact literalRawOwnerIntegral_eq_sum_64_children (archiveRow i) hg.1 hg.2.2.1
    e chi (refinedMesh q) omega j

/-- Exact same-owner signed saving sum BEFORE any cross-parent
aggregation. This avoids any unproved archive key-injectivity assumption. -/
theorem each_licensed_parent_strict_owner_signed_sum
    (i : ArchiveIndex) (hi : i ∈ mask56Indices)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (∑ j ∈ licensedOwners i e q chi omega,
      literalRawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j) =
      ∑ c : ChildIndex, ∑ j ∈ licensedOwners i e q chi omega,
        ∫ t in childOwnerDomain (archiveRow i) c e chi (refinedMesh q) omega j,
          literalRawKernel (e : ℝ) (archiveRow i) t := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact each_licensed_parent_same_owner_signed64 i hi e q chi omega j

/-- The complete SOURCE-index sum is partitioned without declaring the
unlicensed remainder zero and without evaluating either numerical total. -/
theorem source_index_sum_partition (f : ArchiveIndex → ℝ) :
    (∑ i : ArchiveIndex, f i) =
      (∑ i ∈ mask56Indices, f i) + (∑ i ∈ unlicensedMaskIndices, f i) := by
  rw [← Finset.sum_union full_mask_source_partition_disjoint, full_mask_source_partition]

end
end ImbalancedChen.P5HistoricalMask56FullSourceChildren
