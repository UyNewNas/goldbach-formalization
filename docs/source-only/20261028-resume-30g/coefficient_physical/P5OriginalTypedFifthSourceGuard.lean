import ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Unlike the F licensed-filter theorem, this binds EVERY index of the
independent typed original table to the real lower-key source theorem.
The imported closed finite decisions are source proposals and were not
executed here. No hash, filename, saved statistic or arbitrary guard field
is treated as a proof of the coordinate bound or of an owner licence.
-/
namespace ImbalancedChen.P5OriginalTypedFifthSourceGuard
noncomputable section
open scoped Classical
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSeedHull
open P5OriginalFifthArchiveFallbackSeparation
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P1OriginalPrefixRowDecodeSoundness

theorem actual_typed_source_first_lt_mu (i : ArchiveIndex) (t : Fin 5 → ℝ)
    (ht : t ∈ (archiveRow i).originalBox) : t 0 < VariableEnvelope.mu := by
  have hg := archiveRow_baseGeometry i
  exact original_box_first_lt_mu (archiveRow i) hg.1 hg.2.2.2 t ht

/-- Every source index, including any unlicensed owner of that record,
has this geometric guard. No owner gateCheck is inferred from it. -/
theorem actual_record_fallback_nontrigger (i : ArchiveIndex) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox) :
    ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard N (rosserAncestor 4 pre) ∧
      ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard N (rosserAncestor 4 pre) :=
  ancestor_fallback_guards_false N pre hlen (actual_typed_source_first_lt_mu i _ ht).le

theorem actual_record_current_parent_identity (d : OriginalData) (i : ArchiveIndex)
    (N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox) :
    commonInherited d N pre = oldInherited d N pre ∧
      exponent5 d N pre = oldFifth d N pre :=
  ⟨inherited_eq_old_below_mu d N pre hlen (actual_typed_source_first_lt_mu i _ ht).le,
    fifth_eq_old_below_mu d N pre hlen (actual_typed_source_first_lt_mu i _ ht).le⟩

theorem actual_changed_parent_disjoint_all_records (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hp : pre ∈ changedParents d N) :
    ∀ i : ArchiveIndex, primeHistoryLogCoordinates N 5 pre ∉ (archiveRow i).originalBox := by
  intro i ht
  exact hp.2 (actual_record_current_parent_identity d i N pre hp.1 ht).1

/-- The old maximum is restored only on the actual source point, keeping
the original decoded mask and cell membership intact. -/
theorem actual_decoded_record_parent_identity (d : OriginalData) (i : ArchiveIndex)
    (m : ℕ) (r : P1OriginalVariableFifthContinuation.FifthRow m)
    (hr : r ∈ decodeFifthRows (archiveRow i) m) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    r.selected = maskSlots 5 (archiveRow i).mask.toNat ∧
      commonInherited d N pre = oldInherited d N pre ∧ exponent5 d N pre = oldFifth d N pre := by
  have hs := decodeFifthRows_source_geometry (archiveRow i) m r hr _ ht
  exact ⟨hs.2.2.1, actual_record_current_parent_identity d i N pre hlen hs.2.2.2⟩

end
end ImbalancedChen.P5OriginalTypedFifthSourceGuard
