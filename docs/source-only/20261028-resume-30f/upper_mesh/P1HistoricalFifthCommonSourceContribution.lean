import ImbalancedChen.P1HistoricalFifthTypedKeyPartition
import ImbalancedChen.P1HistoricalFifthCommonAncestorExcess
import ImbalancedChen.P1FifthUnitBoxGainDecomposition
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The original full typed archive is an actual finite source partition for
the SAME independent common-refined exponent5/policy8. Its raw gain uses
the NEW common fourth ancestor, not the historical old-fourth kernel.
The identity below is a pointwise source/count identity. It is not a
continuous-density approximation or an old saved-gain preservation claim.
-/
namespace ImbalancedChen.P1HistoricalFifthCommonSourceContribution
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthRawBoxSelectorEquivalence
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P1HistoricalFifthTypedKeyPartition P1HistoricalFifthCommonPolicyInputs
open P1FifthUnitBoxGainDecomposition

/-- Actual candidate eligibility source: the retained original owner
cell, with both0/e selected/firstStop/full/complement checks already held
by licensedOwners. This is not the old fullCell integration domain. -/
def sourceCellDomain (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Set (Fin 5 → ℝ) :=
  ⋃ j ∈ licensedOwners i e q chi omega,
    logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j

theorem sourceCellDomain_subset_raw (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    sourceCellDomain i e q chi omega ⊆ (archiveRow i).originalBox := by
  intro t ht
  obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp ht
  exact (decodeFifthRows_source_geometry (archiveRow i) (refinedMesh q)
    (sourceOwnerRow i q j) (licensedOwner_decoded i e q chi omega j hj) t htj).2.2.2

theorem sourceCellDomain_unique (i k : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (t : Fin 5 → ℝ) (hi : t ∈ sourceCellDomain i e q chi omega)
    (hk : t ∈ sourceCellDomain k e q chi omega) : i = k :=
  common_raw_point_index_unique i k t
    (sourceCellDomain_subset_raw i e q chi omega hi)
    (sourceCellDomain_subset_raw k e q chi omega hk)

theorem sourceCellDomains_pairwise_disjoint (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Set.PairwiseDisjoint (Set.univ : Set ArchiveIndex)
      (fun i => sourceCellDomain i e q chi omega) := by
  intro i _hi k _hk hne
  exact (indexed_raw_boxes_disjoint i k hne).mono
    (sourceCellDomain_subset_raw i e q chi omega)
    (sourceCellDomain_subset_raw k e q chi omega)

/-- Membership in the actual common finite row maximum has its original
source-index witness. A repeated mask/cell cannot create a second source. -/
theorem eligible_row_has_active_source (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (r : FifthRow (refinedMesh q)) (hr : r ∈ licensedRows e q chi omega)
    (t : Fin 5 → ℝ) (hel : eligible e chi (refinedMesh q) omega
      (globalOwners e q chi omega) r t) :
    ∃ i : ArchiveIndex, t ∈ sourceCellDomain i e q chi omega ∧
      r ∈ decodeFifthRows (archiveRow i) (refinedMesh q) := by
  obtain ⟨i, _hi, hj, _heq, hdec⟩ := licensedRows_source_index e q chi omega r hr
  exact ⟨i, mem_iUnion₂.mpr ⟨r.cell, hj, hel.2.2⟩, hdec⟩

/-- The NEW common fourth ancestor is retained literally as the seed. -/
theorem common_exponent5_eq_unique_source
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (i : ArchiveIndex)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ sourceCellDomain i e q chi omega) :
    P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre =
      max (P5OriginalCommonRefinedConstructor.exponent4
        (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre))
        (rawCandidate (e : ℝ) (archiveRow i) (primeHistoryLogCoordinates N 5 pre)) := by
  let t := primeHistoryLogCoordinates N 5 pre
  let seed := P5OriginalCommonRefinedConstructor.exponent4
    (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre)
  have hmax : finiteMax (licensedRows e q chi omega)
      (fun r => eligible e chi (refinedMesh q) omega (globalOwners e q chi omega) r t)
      (fun r => candidate (e : ℝ) r.selected t) seed =
        max seed (rawCandidate (e : ℝ) (archiveRow i) t) := by
    apply le_antisymm
    · apply finiteMax_le _ _ _ _ _ (le_max_left _ _)
      intro r hr hel
      obtain ⟨k, hk, hdec⟩ := eligible_row_has_active_source e q chi omega r hr t hel
      have hki : k = i := sourceCellDomain_unique k i e q chi omega t hk ht
      subst k
      have hs := decodeFifthRows_selected_eq (archiveRow i) (refinedMesh q) r hdec
      rw [hs, ← rawCandidate_eq_candidate]
      exact le_max_right _ _
    · obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp ht
      apply max_le (finiteMax_seed_le _ _ _ _)
      have hr : sourceOwnerRow i q j ∈ licensedRows e q chi omega :=
        Finset.mem_biUnion.mpr ⟨i, all_archive_indices_licensed i,
          Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
      have hel := archive_candidate_eligible rows4 licensed4 i (all_archive_indices_licensed i)
        e q chi omega j hj t htj
      have hb := finiteMax_row_le (licensedRows e q chi omega)
        (fun r => eligible e chi (refinedMesh q) omega (globalOwners e q chi omega) r t)
        (fun r => candidate (e : ℝ) r.selected t) seed (sourceOwnerRow i q j) hr hel
      simpa only [sourceOwnerRow, rawCandidate_eq_candidate] using hb
  simpa only [P5OriginalCommonRefinedConstructor.exponent5, if_pos hlen, sourceData,
    t, seed] using hmax

theorem common_exponent5_eq_seed_off_sources
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (hout : ∀ i : ArchiveIndex,
      primeHistoryLogCoordinates N 5 pre ∉ sourceCellDomain i e q chi omega) :
    P5OriginalCommonRefinedConstructor.exponent5 (sourceData rows4 licensed4 e q chi omega) N pre =
      P5OriginalCommonRefinedConstructor.exponent4
        (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre) := by
  simp only [P5OriginalCommonRefinedConstructor.exponent5, if_pos hlen, sourceData]
  apply le_antisymm
  · apply finiteMax_le _ _ _ _ _ le_rfl
    intro r hr hel
    obtain ⟨i, hi, _hdec⟩ := eligible_row_has_active_source e q chi omega r hr _ hel
    exact (hout i hi).elim
  · exact finiteMax_seed_le _ _ _ _

/-- The SAME policy8 rank-five query now has its exact original source
formula, including the actual newly shared ancestor and original mask. -/
theorem policy8_fifth_test_on_source
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (i : ArchiveIndex)
    (ht : primeHistoryLogCoordinates N 5 pre ∈ sourceCellDomain i e q chi omega) :
    P5OriginalCommonRefinedConstructor.policy8 (sourceData rows4 licensed4 e q chi omega) N false pre =
      decide (ordinaryRosserPrefixAdmissible false
        (N ^ max (P5OriginalCommonRefinedConstructor.exponent4
          (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre))
          (rawCandidate (e : ℝ) (archiveRow i) (primeHistoryLogCoordinates N 5 pre))) pre) := by
  rw [actual_archive_common_fifth_test rows4 licensed4 e q chi omega N pre hlen,
    common_exponent5_eq_unique_source rows4 licensed4 e q chi omega N pre hlen i ht]

def commonFifthGain (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 5 pre
  (primeOwnCubeGatedProfile (P5OriginalCommonRefinedConstructor.exponent5
      (sourceData rows4 licensed4 e q chi omega) N pre) t -
    primeOwnCubeGatedProfile (P5OriginalCommonRefinedConstructor.exponent4
      (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre)) t) * ∏ k, 1 / t k

def indexedCommonGain (i : ArchiveIndex) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates N 5 pre
  if t ∈ sourceCellDomain i e q chi omega then
    rawGainKernel (e : ℝ) (fun _ => P5OriginalCommonRefinedConstructor.exponent4
      (sourceData rows4 licensed4 e q chi omega) N (rosserAncestor 4 pre)) (archiveRow i) t
  else 0

/-- True original strict own-cube gates are retained on both terms.
The old literal kernel and saved Q80 output do not occur in this identity. -/
theorem commonFifthGain_eq_indexed_source_sum
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (pre : List ℕ) (hlen : pre.length = 5) :
    commonFifthGain rows4 licensed4 e q chi omega N pre =
      ∑ i : ArchiveIndex, indexedCommonGain i rows4 licensed4 e q chi omega N pre := by
  by_cases hex : ∃ i : ArchiveIndex,
      primeHistoryLogCoordinates N 5 pre ∈ sourceCellDomain i e q chi omega
  · obtain ⟨i, hi⟩ := hex
    have hmax := common_exponent5_eq_unique_source rows4 licensed4 e q chi omega N pre hlen i hi
    have hsingle : (∑ k : ArchiveIndex, indexedCommonGain k rows4 licensed4 e q chi omega N pre) =
        indexedCommonGain i rows4 licensed4 e q chi omega N pre := by
      apply Finset.sum_eq_single i
      · intro k _hk hki
        have hnot : primeHistoryLogCoordinates N 5 pre ∉ sourceCellDomain k e q chi omega := by
          intro hk
          exact hki (sourceCellDomain_unique k i e q chi omega _ hk hi)
        simp only [indexedCommonGain, if_neg hnot]
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    rw [hsingle]
    simp only [indexedCommonGain, if_pos hi, commonFifthGain, rawGainKernel, hmax]
  · have hout : ∀ i : ArchiveIndex,
        primeHistoryLogCoordinates N 5 pre ∉ sourceCellDomain i e q chi omega := by
      intro i hi
      exact hex ⟨i, hi⟩
    have hseed := common_exponent5_eq_seed_off_sources rows4 licensed4 e q chi omega N pre hlen hout
    have hzero : commonFifthGain rows4 licensed4 e q chi omega N pre = 0 := by
      simp only [commonFifthGain, hseed, sub_self, zero_mul]
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro i _hi
    simp only [indexedCommonGain, if_neg (hout i)]

/-- Exact finite physical-prefix contribution, with the same original
index/mask and common policy on BOTH sides. No distribution estimate,
density convergence or total gain is assumed. -/
theorem finite_common_contribution_eq_source_sum
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega N : ℝ) (prefixes : Finset (List ℕ))
    (hlen : ∀ pre ∈ prefixes, pre.length = 5) (weight : List ℕ → ℝ) :
    (∑ pre ∈ prefixes, weight pre * commonFifthGain rows4 licensed4 e q chi omega N pre) =
      ∑ i : ArchiveIndex, ∑ pre ∈ prefixes,
        weight pre * indexedCommonGain i rows4 licensed4 e q chi omega N pre := by
  calc
    _ = ∑ pre ∈ prefixes, ∑ i : ArchiveIndex,
        weight pre * indexedCommonGain i rows4 licensed4 e q chi omega N pre := by
      apply Finset.sum_congr rfl
      intro pre hp
      rw [commonFifthGain_eq_indexed_source_sum rows4 licensed4 e q chi omega N pre (hlen pre hp),
        Finset.mul_sum]
    _ = _ := Finset.sum_comm

end
end ImbalancedChen.P1HistoricalFifthCommonSourceContribution
