import ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
import ImbalancedChen.P5HistoricalChangedParentCapControl

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original full archive is strictly below mu. Consequently neither of
the independently defined above-mu fallback branches changes its actual
fourth seed. This pays the changed-parent term on this original source by
an exact zero, for every schedule, without a gain or cap-comparison premise.
The separate canonicalHistoryBankCost is NOT paid by this theorem.
-/
namespace ImbalancedChen.P5HistoricalBelowMuCommonParent
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthAdoptedOwnerBank
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P1HistoricalFifthCommonPolicyInputs P1HistoricalFifthCommonAncestorExcess
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5HistoricalChangedParentCapControl

/-- The two actual fallback guards read the same first ancestral
coordinate. No primality or floating logarithmic approximation is used. -/
theorem fallback_guards_false_below_mu (N : ℝ) (pre : List ℕ)
    (hdepth : 3 ≤ pre.length)
    (hfirst : primeHistoryLogCoordinates N pre.length pre
      ⟨0, by omega⟩ ≤ VariableEnvelope.mu) :
    ¬ secondGuard N pre ∧ ¬ thirdGuard N pre := by
  have h2 := primeHistoryLogCoordinates_ancestor N
    (history := pre) rfl (by omega : 2 ≤ pre.length) (0 : Fin 2)
  have h3 := primeHistoryLogCoordinates_ancestor N
    (history := pre) rfl hdepth (0 : Fin 3)
  have h2first : primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 0 ≤
      VariableEnvelope.mu := by
    simpa only [h2] using hfirst
  have h3first : primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0 ≤
      VariableEnvelope.mu := by
    simpa only [h3] using hfirst
  constructor
  · intro hg
    exact (not_lt_of_ge h2first) hg.1
  · intro hg
    exact (not_lt_of_ge h3first) hg.1

theorem common_third_seed_eq_original_below_mu
    (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hdepth : 3 ≤ pre.length)
    (hfirst : primeHistoryLogCoordinates N pre.length pre
      ⟨0, by omega⟩ ≤ VariableEnvelope.mu) :
    lambda3 d N pre = originalSeed d N pre := by
  obtain ⟨hs, ht⟩ := fallback_guards_false_below_mu N pre hdepth hfirst
  simp only [lambda3, fallbackSeed, if_neg ht, if_neg hs, max_self]

/-- A source position is retained, including repeated records. The bound
comes from the existing full typed base geometry, not a new row sample. -/
theorem archive_first_coordinate_lt_mu (i : ArchiveIndex)
    (t : Fin 5 → ℝ) (ht : t ∈ (archiveRow i).originalBox) :
    t 0 < VariableEnvelope.mu := by
  have hkey : ((archiveRow i).lo 0 : ℝ) ≤ 77 := by
    exact_mod_cast (archiveRow_baseGeometry i).2.2.2
  have hhi := (ht 0).2
  simp only [FifthWireRow.upper, archiveRow_grid] at hhi
  push_cast at hhi
  dsimp only [VariableEnvelope.mu]
  linarith

theorem archive_parentExcess_zero
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5) (i : ArchiveIndex)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox) :
    parentExcess rows4 licensed4 e q chi omega N pre = 0 := by
  have hfirst := (archive_first_coordinate_lt_mu i _ ht).le
  have hpre : primeHistoryLogCoordinates N pre.length pre
      ⟨0, by omega⟩ ≤ VariableEnvelope.mu := by
    simpa only [hlen] using hfirst
  have hseed := common_third_seed_eq_original_below_mu
    (sourceData rows4 licensed4 e q chi omega) N pre (by omega) hpre
  have hseed4 : lambda3 (sourceData rows4 licensed4 e q chi omega) N
      (rosserAncestor 4 pre) =
      P1OriginalVariableFourthContinuation.seedExponent
        (e : ℝ) chi (refinedMesh q) omega N (rosserAncestor 4 pre) := by
    rw [lambda3_ancestor _ N 4 (by omega) pre, hseed]
    simp only [originalSeed, sourceData,
      P1OriginalVariableFourthContinuation.seedExponent_ancestor_four]
  have hparent : P5OriginalCommonRefinedConstructor.exponent4
      (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre) =
      inherited4 e chi (refinedMesh q) omega N rows4 licensed4 pre := by
    simp only [P5OriginalCommonRefinedConstructor.exponent4, inherited4,
      P1OriginalVariableFourthContinuation.exponent4,
      P1OriginalVariableFourthContinuation.profile4, sourceData] at hseed4 ⊢
    rw [hseed4]
  exact sub_eq_zero.mpr hparent

theorem archive_common_fifth_eq_original
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5) (i : ArchiveIndex)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox) :
    P5OriginalCommonRefinedConstructor.exponent5
      (sourceData rows4 licensed4 e q chi omega) N pre =
      P1OriginalVariableFifthContinuation.exponent5 e chi (refinedMesh q)
        omega N rows4 licensed4 (globalOwners e q chi omega)
          (licensedRows e q chi omega) pre :=
  zero_excess_common_fifth_eq_old rows4 licensed4 e q chi omega N pre hlen
    (archive_parentExcess_zero rows4 licensed4 e q chi omega N pre hlen i ht)

/-- Attachment to the independent common constructor: recover the
original archive position from an actual bank row, then use its box. -/
theorem actual_common_bank_parentExcess_zero
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5) (r : FifthRow (refinedMesh q))
    (hr : r ∈ (sourceData rows4 licensed4 e q chi omega).rows5)
    (ht : primeHistoryLogCoordinates N 5 pre ∈
      logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    parentExcess rows4 licensed4 e q chi omega N pre = 0 := by
  obtain ⟨i, _hi, _hj, _heq, hdecode⟩ :=
    full_archive_licensed_rows_source rows4 licensed4 e q chi omega r hr
  exact archive_parentExcess_zero rows4 licensed4 e q chi omega N pre hlen i
    (decodeFifthRows_source_geometry (archiveRow i) (refinedMesh q) r hdecode _ ht).2.2.2

theorem archive_prefix_not_changed_parent
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 5) (i : ArchiveIndex)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox) :
    pre ∉ changedParentPrefixes rows4 licensed4 e q chi omega N := by
  intro hchanged
  have hp := (changedParent_iff_positive_excess rows4 licensed4
    e q chi omega N pre hlen).mp hchanged
  rw [archive_parentExcess_zero rows4 licensed4 e q chi omega N pre hlen i ht] at hp
  exact (lt_irrefl 0) hp

/-- Direct consumer: the actual added LOG own-cube-query region defined
before this module is disjoint from every original archive source box. -/
theorem actual_changed_queries_disjoint_archive_source
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (i : ArchiveIndex) :
    Disjoint (actualChangedFifthCubeQueries rows4 licensed4 e q chi omega N)
      {pre | pre.length = 5 ∧
        primeHistoryLogCoordinates N 5 pre ∈ (archiveRow i).originalBox} := by
  apply Set.disjoint_left.mpr
  intro pre hquery hsource
  exact archive_prefix_not_changed_parent rows4 licensed4 e q chi omega
    N pre hsource.1 i hsource.2
    (actual_changed_cube_query_has_changed_parent rows4 licensed4
      e q chi omega N pre hquery)

end
end ImbalancedChen.P5HistoricalBelowMuCommonParent
