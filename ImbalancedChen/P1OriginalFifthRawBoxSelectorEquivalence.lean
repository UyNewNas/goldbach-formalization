import ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover
import ImbalancedChen.P1ActualVariableFifthProfiles

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The maximum over an entire finite family of saved grid400 boxes equals the
maximum over their complete refined lawful cell family. All overlapping
records participate. The inherited seed is explicit. No gate truth,
selected-owner licence, dynamic parent, or history is decoded from raw
payload statistics. The final two connections require those actual finite
gate/owner inputs separately and use the existing original ancestor dictionary.
No decoded cell family or concrete full-table witness is executed here.
-/

namespace ImbalancedChen.P1OriginalFifthRawBoxSelectorEquivalence
noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary
open P1CorrectedFifthCausalTupleDictionary

/-- Mathematical union only; duplicate decoded rows carry no extra maximum
weight, while distinct masks on overlapping boxes are all retained. -/
def decodedFamily (records : Finset FifthWireRow) (q : ℕ) :
    Finset (FifthRow (refinedMesh q)) :=
  records.biUnion (fun raw => decodeFifthRows raw (refinedMesh q))

theorem mem_decodedFamily (records : Finset FifthWireRow) (q : ℕ)
    (r : FifthRow (refinedMesh q)) :
    r ∈ decodedFamily records q ↔
      ∃ raw ∈ records, r ∈ decodeFifthRows raw (refinedMesh q) := by
  simp only [decodedFamily, Finset.mem_biUnion]

/-- Literal variable M_I after buffer loss, with the saved original slot order. -/
def rawCandidate (e : ℝ) (raw : FifthWireRow) (t : Fin 5 → ℝ) : ℝ :=
  VariableEnvelope.v (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) - 2 * e

theorem rawCandidate_eq_candidate (e : ℝ) (raw : FifthWireRow) (t : Fin 5 → ℝ) :
    rawCandidate e raw t = candidate e (maskSlots 5 raw.mask.toNat) t := by
  rw [candidate, envelope_eq_v]
  rfl

def rawBoxMaximum (e : ℝ) (records : Finset FifthWireRow)
    (seed : ℝ) (t : Fin 5 → ℝ) : ℝ :=
  finiteMax records (fun raw => t ∈ raw.originalBox)
    (fun raw => rawCandidate e raw t) seed

def decodedBoxMaximum (e : ℝ) (records : Finset FifthWireRow) (q : ℕ)
    (seed : ℝ) (t : Fin 5 → ℝ) : ℝ :=
  finiteMax (decodedFamily records q)
    (fun r => t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell)
    (fun r => candidate e r.selected t) seed

/-- Exact whole-family selector equivalence, with no gateCheck premise.
Both directions compare the inherited seed and every eligible row. -/
theorem rawBoxMaximum_eq_decodedBoxMaximum
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask)
    (e seed : ℝ) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))) :
    rawBoxMaximum e records seed t = decodedBoxMaximum e records q seed t := by
  unfold rawBoxMaximum decodedBoxMaximum
  apply le_antisymm
  · apply finiteMax_le _ _ _ _ _ (finiteMax_seed_le _ _ _ _)
    intro raw hraw htRaw
    have hpoint : t ∈ raw.originalBox ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := ⟨htRaw, ht⟩
    rw [refined_originalBox_inter_ambient_eq_decode_union q hq raw
      (hgrid raw hraw) (hmask raw hraw)] at hpoint
    obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp hpoint
    have hfamily : r ∈ decodedFamily records q :=
      (mem_decodedFamily records q r).mpr ⟨raw, hraw, hr⟩
    rw [rawCandidate_eq_candidate, ← decodeFifthRows_selected_eq raw _ r hr]
    exact finiteMax_row_le _ _ _ _ r hfamily htr
  · apply finiteMax_le _ _ _ _ _ (finiteMax_seed_le _ _ _ _)
    intro r hr htr
    obtain ⟨raw, hraw, hdecode⟩ := (mem_decodedFamily records q r).mp hr
    have hsource := decodeFifthRows_source_geometry raw (refinedMesh q) r hdecode t htr
    have hrow := finiteMax_row_le records (fun raw => t ∈ raw.originalBox)
      (fun raw => rawCandidate e raw t) seed raw hraw hsource.2.2.2
    rw [rawCandidate_eq_candidate, ← decodeFifthRows_selected_eq raw _ r hdecode] at hrow
    exact hrow

/-- Eligibility need only agree on the actual finite row family. -/
theorem finiteMax_eq_of_eligibility_on {ι : Type*} (rows : Finset ι)
    (P Q : ι → Prop) (value : ι → ℝ) (seed : ℝ)
    (h : ∀ r ∈ rows, P r ↔ Q r) :
    finiteMax rows P value seed = finiteMax rows Q value seed := by
  apply le_antisymm
  · exact finiteMax_le rows P value seed _ (finiteMax_seed_le _ _ _ _)
      (fun r hr hp => finiteMax_row_le rows Q value seed r hr ((h r hr).mp hp))
  · exact finiteMax_le rows Q value seed _ (finiteMax_seed_le _ _ _ _)
      (fun r hr hq => finiteMax_row_le rows P value seed r hr ((h r hr).mpr hq))

/-- The unchecked cell-membership selector becomes the actual gated owner
profile only after a separate true gateCheck is supplied for each row. -/
theorem decodedBoxMaximum_eq_actualNext5
    (records : Finset FifthWireRow) (q : ℕ) (e : ℚ) (chi omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (j : RefinedCell q) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j)
    (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true) :
    decodedBoxMaximum (e : ℝ) records q
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t) t =
      P1ActualVariableFifthProfiles.actualNext5 e chi (refinedMesh q) omega j
        rows4 licensed4 (decodedFamily records q) t := by
  unfold decodedBoxMaximum P1ActualVariableFifthProfiles.actualNext5
  apply finiteMax_eq_of_eligibility_on
  intro r hr
  constructor
  · intro htr
    exact ⟨logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) htr ht,
      hgate r hr⟩
  · rintro ⟨hcell, _hcheck⟩
    exact hcell.symm ▸ ht

theorem rawBoxMaximum_eq_actualNext5
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask)
    (e : ℚ) (chi omega : ℝ) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (j : RefinedCell q) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j)
    (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true) :
    rawBoxMaximum (e : ℝ) records
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t) t =
      P1ActualVariableFifthProfiles.actualNext5 e chi (refinedMesh q) omega j
        rows4 licensed4 (decodedFamily records q) t := by
  rw [rawBoxMaximum_eq_decodedBoxMaximum records q hq hgrid hmask _ _ _
    (logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96) (refinedMesh q) j ht)]
  exact decodedBoxMaximum_eq_actualNext5 records q e chi omega rows4 licensed4 j t ht hgate

/-- On an actually selected original owner, the existing firstStop/rawQ3
ancestor dictionary identifies the same maximum with the original exponent5.
The finite gate and selected-owner witnesses are explicit, not payload fields. -/
theorem rawBoxMaximum_eq_original_exponent5
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask)
    (e : ℚ) (chi omega : ℝ) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (J5 : Finset (RefinedCell q))
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : RefinedCell q)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j)
    (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true) :
    rawBoxMaximum (e : ℝ) records
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4
          (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p) =
      exponent5 e chi (refinedMesh q) omega (N : ℝ) rows4 licensed4 J5
        (decodedFamily records q) (tupleHistory p) := by
  rw [rawBoxMaximum_eq_actualNext5 records q hq hgrid hmask e chi omega
    rows4 licensed4 j _ ht hgate]
  exact (P1ActualVariableFifthProfiles.exponent5_on_selected_owner e chi (refinedMesh q)
    omega rows4 licensed4 J5 (decodedFamily records q) N hN p hp j hj ht).symm

end
end ImbalancedChen.P1OriginalFifthRawBoxSelectorEquivalence
