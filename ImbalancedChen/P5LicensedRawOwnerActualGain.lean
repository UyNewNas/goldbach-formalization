import ImbalancedChen.P5HistoricalMask56FullSourceChildren

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_CREDIT.
The positive surrogate is integrated against the SAME original variable
fourth ancestor and actual strict owner. A singleton eligible fifth row
provides integrability without assuming that all decoded rows pass gates.
This is not a transfer to a changed common fourth ancestor.
-/
namespace ImbalancedChen.P5LicensedRawOwnerActualGain
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalVariableFourthContinuation P2OriginalFourthCapProducerInterface
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthUnitBoxGainDecomposition P1FifthUnitBoxLiteralGainLower
open P1FifthPositivePartActualOwner P1ActualVariableFifthProfiles
open P1ActualVariableFifthUntruncatedDomination
open P1HistoricalFifthIndexedOwnerArchive
open P5HistoricalMask56FullSourceChildren

/-- This row keeps the original mask and this exact owner label. -/
theorem singleton_actualNext5 (i : ArchiveIndex) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i e q chi omega)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (t : Fin 5 → ℝ) :
    actualNext5 e chi (refinedMesh q) omega j rows4 licensed4
      {sourceOwnerRow i q j} t =
      max (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t)
        (rawCandidate (e : ℝ) (archiveRow i) t) := by
  have hg := licensedOwner_gate_buffer i e q chi omega j hj
  have he : ownerEligible e (refinedMesh q) j (sourceOwnerRow i q j) := ⟨rfl, hg⟩
  have hc : candidate (e : ℝ) (sourceOwnerRow i q j).selected t =
      rawCandidate (e : ℝ) (archiveRow i) t :=
    (rawCandidate_eq_candidate (e : ℝ) (archiveRow i) t).symm
  unfold actualNext5
  apply le_antisymm
  · apply finiteMax_le _ _ _ _ _ (le_max_left _ _)
    intro r hr _
    have hrj := Finset.mem_singleton.mp hr
    subst r
    rw [hc]
    exact le_max_right _ _
  · apply max_le (finiteMax_seed_le _ _ _ _)
    rw [← hc]
    exact finiteMax_row_le _ _ _ _ _ (Finset.mem_singleton_self _) he

theorem singleton_actualKernel_eq (i : ArchiveIndex) (e : ℚ) (q : ℕ)
    (chi omega : ℝ) (j : Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i e q chi omega)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (t : Fin 5 → ℝ) :
    actualKernel e chi (refinedMesh q) omega j rows4 licensed4
      {sourceOwnerRow i q j} t =
      rawOwnerKernel e chi (refinedMesh q) omega j rows4 licensed4 (archiveRow i) t := by
  change (_ - _) * (∏ k, 1 / t k) = (_ - _) * (∏ k, 1 / t k)
  rw [singleton_actualNext5 i e q chi omega j hj rows4 licensed4 t]

/-- True rawOwnerKernel integrability, with no decoded-family gate premise. -/
theorem integrableOn_licensed_rawOwner (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e)
    (q : ℕ) (chi omega : ℝ) (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) :
    IntegrableOn (rawOwnerKernel e chi (refinedMesh q) omega j rows4 licensed4 (archiveRow i))
      (rawOwnerDomain (archiveRow i) e chi (refinedMesh q) omega j) := by
  have hs := licensedOwner_selected_buffer i e q chi omega j hj
  have hI := (integrableOn_actualKernel_fullCell e he chi (refinedMesh q) omega hw hwr
    (licensedOwners i e q chi omega) j hs rows4 licensed4 {sourceOwnerRow i q j}).mono_set
      (s := rawOwnerDomain (archiveRow i) e chi (refinedMesh q) omega j) inter_subset_right
  exact hI.congr_fun (fun t _ => singleton_actualKernel_eq i e q chi omega j hj rows4 licensed4 t)
    (rawOwnerDomain_measurable (archiveRow i) e chi (refinedMesh q) omega j)

theorem licensed_positive_surrogate_le_same_actual_owner
    (i : ArchiveIndex) (hi : i ∈ mask56Indices) (e : ℚ) (he : 0 ≤ e)
    (q : ℕ) (chi omega : ℝ) (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    literalPositiveRawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j ≤
      rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4 := by
  have hg := mask56_index_geometry i hi
  apply setIntegral_mono_on
    (integrableOn_literalPositiveRawKernel_rawOwner (archiveRow i) hg.1 hg.2.2.1
      e chi (refinedMesh q) omega j)
    (integrableOn_licensed_rawOwner i e he q chi omega hw hwr j hj rows4 licensed4)
    (rawOwnerDomain_measurable (archiveRow i) e chi (refinedMesh q) omega j)
  intro t ht
  exact literalPositiveRawKernel_le_rawOwnerKernel e (by exact_mod_cast he)
    chi (refinedMesh q) omega rows4 licensed4 hgeometry
    (licensedOwners i e q chi omega) j
    (licensedOwner_selected_buffer i e q chi omega j hj) (archiveRow i) t ht

/-- All original64 child floors feed this parent's same actual ancestor.
The strict-owner reserve is retained, not made arbitrarily small here. -/
theorem each_parent64_wire_minus_reserve_le_actual
    (i : ArchiveIndex) (hi : i ∈ mask56Indices) (e : ℚ) (he : 0 ≤ e)
    (q : ℕ) (chi omega : ℝ) (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    (indexedWireFloor64 i : ℝ) - indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4 := by
  exact (each_licensed_parent64_source_floor_minus_actual_reserve i hi e q chi omega).trans
    (Finset.sum_le_sum (fun j hj => licensed_positive_surrogate_le_same_actual_owner
      i hi e he q chi omega hw hwr j hj rows4 licensed4 hgeometry))

end
end ImbalancedChen.P5LicensedRawOwnerActualGain
