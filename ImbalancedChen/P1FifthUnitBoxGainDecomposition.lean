import ImbalancedChen.P1FifthGrid400UnitBoxPartition
import ImbalancedChen.P1ActualVariableFifthUntruncatedDomination

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual original variable fifth kernel is decomposed over genuine saved
unit boxes. A key-Nodup family has at most one raw candidate at each point,
so its whole maximum is max(actual old4,M_I), including losing candidates.
The original selected-owner/joint history and decoded gate licences remain
explicit. Existing actual full-cell integrability is consumed directly.

The exact finite union integral and the whole selected fifth integral are
therefore sums of actual raw-row integrals, with both strict own-cube gates
kept. No statistic A/B is a gain; no actual payload passing flag is asserted.
-/
namespace ImbalancedChen.P1FifthUnitBoxGainDecomposition

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthGrid400UnitBoxPartition
open P1OriginalVariableFourthContinuation P1OriginalVariableFifthContinuation
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1ActualVariableFifthProfiles
open P1ActualVariableFifthUntruncatedDomination

abbrev Point := Fin 5 → ℝ

/-- Unique geometric ownership identifies the actual maximum, not just
an upper or lower bound. Masks/statistics never enter the ownership key. -/
theorem rawBoxMaximum_eq_unique_row
    (records : Finset FifthWireRow)
    (hgrid : ∀ row ∈ records, row.grid = 400) (hkey : KeyInjective records)
    (e seed : ℝ) (raw : FifthWireRow) (hr : raw ∈ records)
    (t : Point) (ht : t ∈ raw.originalBox) :
    rawBoxMaximum e records seed t = max seed (rawCandidate e raw t) := by
  unfold rawBoxMaximum
  apply le_antisymm
  · apply finiteMax_le _ _ _ _ _ (le_max_left _ _)
    intro row hrow htrow
    have heq := records_common_point_eq records hgrid hkey row raw hrow hr t htrow ht
    subst row
    exact le_max_right _ _
  · exact max_le (finiteMax_seed_le _ _ _ _)
      (finiteMax_row_le _ _ _ _ raw hr ht)

theorem rawBoxMaximum_eq_seed_outside (records : Finset FifthWireRow)
    (e seed : ℝ) (t : Point) (ht : ∀ raw ∈ records, t ∉ raw.originalBox) :
    rawBoxMaximum e records seed t = seed := by
  unfold rawBoxMaximum
  apply le_antisymm
  · apply finiteMax_le _ _ _ _ _ le_rfl
    intro row hrow hpoint
    exact (ht row hrow hpoint).elim
  · exact finiteMax_seed_le _ _ _ _

/-- The new level remains max(old4,M_I). An MI below the actual parent
produces zero gain rather than a fictitious positive saved statistic. -/
def rawGainKernel (e : ℝ) (old4 : Point → ℝ) (raw : FifthWireRow) (t : Point) : ℝ :=
  (primeOwnCubeGatedProfile (max (old4 t) (rawCandidate e raw t)) t -
    primeOwnCubeGatedProfile (old4 t) t) * ∏ i, 1 / t i

theorem rawGainKernel_two_strict_gates (e : ℝ) (old4 : Point → ℝ)
    (raw : FifthWireRow) (t : Point) :
    rawGainKernel e old4 raw t =
      ((if primeTupleOwnCubeForm t < max (old4 t) (rawCandidate e raw t)
        then primeTupleMinusProfile (max (old4 t) (rawCandidate e raw t)) t else 0) -
       (if primeTupleOwnCubeForm t < old4 t
        then primeTupleMinusProfile (old4 t) t else 0)) * ∏ i, 1 / t i := rfl

theorem rawGainKernel_nonneg (e : ℝ) (old4 : Point → ℝ) (raw : FifthWireRow)
    (t : Point) (ht : ∀ i, 0 < t i) : 0 ≤ rawGainKernel e old4 raw t := by
  apply mul_nonneg
  · exact sub_nonneg.mpr (p1PrimeOwnCubeGatedProfile_mono t
      (ht (Fin.last 4)) (le_max_left _ _))
  · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le)

def rawOwnerDomain (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (j : Fin 5 → Fin (m + 1)) : Set Point :=
  raw.originalBox ∩ P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j

def rawOwnerKernel (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Fin 5 → Fin (m + 1)) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (raw : FifthWireRow) : Point → ℝ :=
  rawGainKernel (e : ℝ) (originalVariableFourthProfile e chi omega m j rows4 licensed4) raw

def rawOwnerIntegral (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (j : Fin 5 → Fin (m + 1)) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) : ℝ :=
  ∫ t in rawOwnerDomain raw e chi m omega j,
    rawOwnerKernel e chi m omega j rows4 licensed4 raw t

theorem rawOwnerDomain_measurable (raw : FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (j : Fin 5 → Fin (m + 1)) :
    MeasurableSet (rawOwnerDomain raw e chi m omega j) :=
  (measurableSet_originalBox raw).inter
    (P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j)

section SameOriginalOwner

variable (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
  (hgrid : ∀ raw ∈ records, raw.grid = 400)
  (hmask : ∀ raw ∈ records, 0 ≤ raw.mask) (hkey : KeyInjective records)
  (e : ℚ) (chi omega : ℝ) (rows4 : Finset ProducerRow)
  (licensed4 : ProducerRow → Prop)
  (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true)

/-- The whole-family selector is the original actual next5 selector at
this same mesh owner, before it is identified with its unique raw row. -/
theorem actualNext5_eq_raw_row
    (j : RefinedCell q) (raw : FifthWireRow) (hr : raw ∈ records) (t : Point)
    (htRaw : t ∈ raw.originalBox)
    (htCell : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    actualNext5 e chi (refinedMesh q) omega j rows4 licensed4 (decodedFamily records q) t =
      max (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t)
        (rawCandidate (e : ℝ) raw t) := by
  have hs := rawBoxMaximum_eq_actualNext5 records q hq hgrid hmask e chi omega
    rows4 licensed4 j t htCell hgate
  exact hs.symm.trans (rawBoxMaximum_eq_unique_row records hgrid hkey _ _ raw hr t htRaw)

theorem actualKernel_eq_rawOwnerKernel
    (j : RefinedCell q) (raw : FifthWireRow) (hr : raw ∈ records) (t : Point)
    (ht : t ∈ rawOwnerDomain raw e chi (refinedMesh q) omega j) :
    actualKernel e chi (refinedMesh q) omega j rows4 licensed4 (decodedFamily records q) t =
      rawOwnerKernel e chi (refinedMesh q) omega j rows4 licensed4 raw t := by
  have hnext := actualNext5_eq_raw_row records q hq hgrid hmask hkey e chi omega
    rows4 licensed4 hgate j raw hr t ht.1 ht.2.2.2.1
  change (primeOwnCubeGatedProfile
    (actualNext5 e chi (refinedMesh q) omega j rows4 licensed4 (decodedFamily records q) t) t -
      primeOwnCubeGatedProfile
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t) t) *
      (∏ i, 1 / t i) = _
  rw [hnext]
  rfl

theorem actualKernel_zero_outside_raw_union
    (j : RefinedCell q) (t : Point)
    (ht : t ∈ P1OriginalFifthUntruncatedIntegral.fullCell e chi (refinedMesh q) omega j)
    (hout : ∀ raw ∈ records, t ∉ raw.originalBox) :
    actualKernel e chi (refinedMesh q) omega j rows4 licensed4 (decodedFamily records q) t = 0 := by
  have hs := rawBoxMaximum_eq_actualNext5 records q hq hgrid hmask e chi omega
    rows4 licensed4 j t ht.2.2.1 hgate
  rw [rawBoxMaximum_eq_seed_outside records _ _ t hout] at hs
  change (primeOwnCubeGatedProfile
    (actualNext5 e chi (refinedMesh q) omega j rows4 licensed4 (decodedFamily records q) t) t -
      primeOwnCubeGatedProfile
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t) t) *
      (∏ i, 1 / t i) = 0
  rw [← hs, sub_self, zero_mul]

/-- Finite union additivity uses true key disjointness. Integrability is
supplied by the actual original-variable full-cell theorem, not assumed. -/
theorem owner_integral_over_raw_union_eq_sum
    (he : 0 ≤ e) (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (RefinedCell q)) (j : RefinedCell q)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5) :
    (∫ t in ⋃ raw ∈ records, rawOwnerDomain raw e chi (refinedMesh q) omega j,
      actualKernel e chi (refinedMesh q) omega j rows4 licensed4 (decodedFamily records q) t) =
      ∑ raw ∈ records, rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
  have hi := integrableOn_actualKernel_fullCell e he chi (refinedMesh q) omega
    homega homegaRho J5 j hj rows4 licensed4 (decodedFamily records q)
  rw [integral_biUnion_finset records
    (fun raw _ => rawOwnerDomain_measurable raw e chi (refinedMesh q) omega j)
    (clipped_records_pairwise_disjoint records hgrid hkey
      (P1OriginalFifthUntruncatedIntegral.fullCell e chi (refinedMesh q) omega j))
    (fun raw _ => hi.mono_set inter_subset_right)]
  apply Finset.sum_congr rfl
  intro raw hr
  apply setIntegral_congr_fun (rawOwnerDomain_measurable raw e chi (refinedMesh q) omega j)
  intro t ht
  exact actualKernel_eq_rawOwnerKernel records q hq hgrid hmask hkey e chi omega
    rows4 licensed4 hgate j raw hr t ht

/-- The actual kernel is zero off the raw-box union, so the decomposition
accounts for the complete original selected owner, not just a partial box. -/
theorem full_owner_integral_eq_sum_raw
    (he : 0 ≤ e) (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (RefinedCell q)) (j : RefinedCell q)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5) :
    fullCellIntegral e chi (refinedMesh q) omega rows4 licensed4 (decodedFamily records q) j =
      ∑ raw ∈ records, rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
  have hsubset : (⋃ raw ∈ records, rawOwnerDomain raw e chi (refinedMesh q) omega j) ⊆
      P1OriginalFifthUntruncatedIntegral.fullCell e chi (refinedMesh q) omega j := by
    intro t ht
    obtain ⟨raw, _hr, htRaw⟩ := mem_iUnion₂.mp ht
    exact htRaw.2
  have heq := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := actualKernel e chi (refinedMesh q) omega j rows4 licensed4 (decodedFamily records q))
    (P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi (refinedMesh q) omega j) hsubset
    (fun t ht => actualKernel_zero_outside_raw_union records q hq hgrid hmask
      e chi omega rows4 licensed4 hgate j t ht.1 (by
        intro raw hr hraw
        exact ht.2 (mem_iUnion₂.mpr ⟨raw, hr, hraw, ht.1⟩)))
  exact heq.trans (owner_integral_over_raw_union_eq_sum records q hq hgrid hmask hkey
    e chi omega rows4 licensed4 hgate he homega homegaRho J5 j hj)

/-- Whole actual retained variable-fifth integral, summed once per genuine
raw geometry key and once per original selected owner. -/
theorem fullSelectedIntegral_eq_sum_raw_owner_integrals
    (he : 0 ≤ e) (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (RefinedCell q)) :
    fullSelectedIntegral e chi (refinedMesh q) omega rows4 licensed4 J5 (decodedFamily records q) =
      ∑ raw ∈ records, ∑ j ∈
        P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
        rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
  unfold fullSelectedIntegral
  calc
    _ = ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
        ∑ raw ∈ records, rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact full_owner_integral_eq_sum_raw records q hq hgrid hmask hkey e chi omega
        rows4 licensed4 hgate he homega homegaRho J5 j hj
    _ = _ := Finset.sum_comm

end SameOriginalOwner

/-- A passing LO-key check, unlike raw record Finset deduplication, also
justifies retaining the original loaded list's sum with its exact order. -/
theorem sum_loaded_records_eq_finset (raw : Array FifthWireRow)
    (hc : unitKeyCheck raw = true) (f : FifthWireRow → ℝ) :
    (raw.toList.map f).sum = ∑ row ∈ raw.toList.toFinset, f row := by
  symm
  exact List.sum_toFinset f (loaded_rows_nodup raw hc)

/-- Checker-to-whole-gain soundness. This theorem does not execute any
historical table and supplies no actual key/gate passing witness. -/
theorem checked_loaded_fullSelectedIntegral_eq_raw_list_sum
    (raw : Array FifthWireRow) (hpartition : unitFamilyPartitionCheck raw = true)
    (q : ℕ) (hq : 0 < q)
    (hmask : ∀ row ∈ raw.toList, 0 ≤ row.mask)
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (RefinedCell q))
    (hgate : ∀ r ∈ decodedFamily raw.toList.toFinset q,
      gateCheck e (refinedMesh q) r = true) :
    fullSelectedIntegral e chi (refinedMesh q) omega rows4 licensed4 J5
        (decodedFamily raw.toList.toFinset q) =
      (raw.toList.map (fun row => ∑ j ∈
        P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
        rawOwnerIntegral row e chi (refinedMesh q) omega j rows4 licensed4)).sum := by
  have hp := unitFamilyPartitionCheck_sound raw hpartition
  have hk := loaded_key_injective_finset raw (Bool.and_eq_true.mp hpartition).2
  rw [fullSelectedIntegral_eq_sum_raw_owner_integrals raw.toList.toFinset q hq
    (fun row hr => hp.1 row (List.mem_toFinset.mp hr))
    (fun row hr => hmask row (List.mem_toFinset.mp hr)) hk
    e chi omega rows4 licensed4 hgate he homega homegaRho J5]
  exact (sum_loaded_records_eq_finset raw (Bool.and_eq_true.mp hpartition).2 _).symm

end
end ImbalancedChen.P1FifthUnitBoxGainDecomposition
