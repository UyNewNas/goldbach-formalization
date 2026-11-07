import ImbalancedChen.P1OriginalFifthCorrelatedDecodedGates

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
One aligned refinement of an ENTIRE finite grid400 raw family meets an
arbitrary positive omega mesh condition, covers every complete saved box,
and passes every contained decoded-cell gate. The finite correlated raw
checks are explicit UNEXECUTED inputs, not historical facts. No cell list
is enumerated. Original selected-owner licensing and the actual inherited
fourth seed remain explicit in the resulting exact selector dictionary.
-/

namespace ImbalancedChen.P1OriginalFifthFiniteTableRefinementConstructor
noncomputable section
open Set
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1OriginalFifthCorrelatedRawBoxGates
open P1OriginalFifthCorrelatedDecodedGates
open P1OriginalFifthQuantitativeGateRefinement
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary
open P1CorrectedFifthCausalTupleDictionary

/-- This witness certifies only geometry and the actual variable-row
square gates. It contains no fabricated owner, history, or numerical gain. -/
structure CheckedCompleteRefinement (e : ℚ) (omega : ℝ)
    (records : Finset FifthWireRow) (q : ℕ) : Prop where
  positive : 0 < q
  meshSmall : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2
  grid400 : ∀ raw ∈ records, raw.grid = 400
  nonnegativeMask : ∀ raw ∈ records, 0 ≤ raw.mask
  fullBoxCover : ∀ raw ∈ records,
    raw.originalBox ∩ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
        logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell
  allGates : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true

/-- A single q works for every raw record and every decoded row. The
positive rational gate budget is supplied by the quantitative companion;
the independent omega budget is combined with it BEFORE choosing q. -/
theorem exists_checked_complete_refinement (e : ℚ) (omega : ℝ) (homega : 0 < omega)
    (records : Finset FifthWireRow) (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hcheck : ∀ raw ∈ records, correlatedRawBoxGateCheck e raw = true) :
    ∃ q : ℕ, CheckedCompleteRefinement e omega records q := by
  obtain ⟨budget, hbudget, hgateBudget⟩ := exists_family_mesh_budget e records hcheck
  have hbR : (0 : ℝ) < budget := Rat.cast_pos.mpr hbudget
  have hmin : (0 : ℝ) < min omega (budget : ℝ) := lt_min homega hbR
  obtain ⟨q, hq, hsmall⟩ := exists_refinement_step_le_half (min omega (budget : ℝ)) hmin
  have hstepOmega : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 := by
    linarith [min_le_left omega (budget : ℝ)]
  have hstepBudgetR : (meshStepQ (refinedMesh q) : ℝ) < (budget : ℝ) := by
    rw [cast_meshStepQ]
    linarith [min_le_right omega (budget : ℝ)]
  have hstepBudget : meshStepQ (refinedMesh q) < budget := by exact_mod_cast hstepBudgetR
  have hmask : ∀ raw ∈ records, 0 ≤ raw.mask :=
    fun raw hraw => (correlatedRawBoxGateCheck_sound e raw (hcheck raw hraw)).2.1
  refine ⟨q, ⟨hq, hstepOmega, hgrid, hmask, ?_, ?_⟩⟩
  · intro raw hraw
    exact refined_originalBox_inter_ambient_eq_decode_union q hq raw
      (hgrid raw hraw) (hmask raw hraw)
  · intro r hr
    obtain ⟨raw, hraw, hdecode⟩ := (mem_decodedFamily records q r).mp hr
    exact hgateBudget (refinedMesh q) hstepBudget raw hraw r hdecode

/-- Ico face ownership is preserved for the constructed COMPLETE cover. -/
theorem CheckedCompleteRefinement.unique_owner
    {e : ℚ} {omega : ℝ} {records : Finset FifthWireRow} {q : ℕ}
    (h : CheckedCompleteRefinement e omega records q) (raw : FifthWireRow) (hr : raw ∈ records)
    (t : Fin 5 → ℝ) (ht : t ∈ raw.originalBox ∩
      logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))) :
    ∃! r : FifthRow (refinedMesh q), r ∈ decodeFifthRows raw (refinedMesh q) ∧
      t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell :=
  refined_unique_decoded_owner q h.positive raw (h.grid400 raw hr) (h.nonnegativeMask raw hr) t ht

/-- The constructed gates turn the whole raw-box variable maximum into
the actual owner profile over its explicitly supplied actual fourth seed. -/
theorem CheckedCompleteRefinement.rawBoxMaximum_eq_actualNext5
    {e : ℚ} {omega : ℝ} {records : Finset FifthWireRow} {q : ℕ}
    (h : CheckedCompleteRefinement e omega records q)
    (chi : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (j : RefinedCell q) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    rawBoxMaximum (e : ℝ) records
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t) t =
      P1ActualVariableFifthProfiles.actualNext5 e chi (refinedMesh q) omega j
        rows4 licensed4 (decodedFamily records q) t :=
  P1OriginalFifthRawBoxSelectorEquivalence.rawBoxMaximum_eq_actualNext5 records q h.positive
    h.grid400 h.nonnegativeMask e chi omega rows4 licensed4 j t ht h.allGates

/-- The original selected-owner and firstStop/rawQ3 ancestor dictionary
are kept explicit. They are not inferred from grid/mask or check values. -/
theorem CheckedCompleteRefinement.rawBoxMaximum_eq_original_exponent5
    {e : ℚ} {omega : ℝ} {records : Finset FifthWireRow} {q : ℕ}
    (h : CheckedCompleteRefinement e omega records q)
    (chi : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (RefinedCell q)) (N : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i) (j : RefinedCell q)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    rawBoxMaximum (e : ℝ) records
        (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4
          (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p) =
      exponent5 e chi (refinedMesh q) omega (N : ℝ) rows4 licensed4 J5
        (decodedFamily records q) (tupleHistory p) :=
  P1OriginalFifthRawBoxSelectorEquivalence.rawBoxMaximum_eq_original_exponent5 records q h.positive
    h.grid400 h.nonnegativeMask e chi omega rows4 licensed4 J5 N hN p hp j hj ht h.allGates

/-- Existence includes the exact source profile identity as an output,
uniformly for every supplied actual fourth seed and every owner point. -/
theorem exists_checked_refinement_with_actual_dictionary
    (e : ℚ) (omega : ℝ) (homega : 0 < omega) (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hcheck : ∀ raw ∈ records, correlatedRawBoxGateCheck e raw = true) :
    ∃ q : ℕ, CheckedCompleteRefinement e omega records q ∧
      ∀ (chi : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
        (j : RefinedCell q) (t : Fin 5 → ℝ),
        t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j →
          rawBoxMaximum (e : ℝ) records
              (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4 t) t =
            P1ActualVariableFifthProfiles.actualNext5 e chi (refinedMesh q) omega j
              rows4 licensed4 (decodedFamily records q) t := by
  obtain ⟨q, hq⟩ := exists_checked_complete_refinement e omega homega records hgrid hcheck
  exact ⟨q, hq, fun chi rows4 licensed4 j t ht =>
    hq.rawBoxMaximum_eq_actualNext5 chi rows4 licensed4 j t ht⟩

/-- The same existential refinement also exports the literal original
history exponent identity, conditional only on its separately supplied
actual selected owner and existing fourth ancestor data. -/
theorem exists_checked_refinement_with_original_dictionary
    (e : ℚ) (omega : ℝ) (homega : 0 < omega) (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hcheck : ∀ raw ∈ records, correlatedRawBoxGateCheck e raw = true) :
    ∃ q : ℕ, CheckedCompleteRefinement e omega records q ∧
      ∀ (chi : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
        (J5 : Finset (RefinedCell q)) (N : ℕ) (_hN : 1 < N)
        (p : Fin 5 → ℕ) (_hp : ∀ i, 0 < p i) (j : RefinedCell q),
        j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5 →
        actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j →
          rawBoxMaximum (e : ℝ) records
              (originalVariableFourthProfile e chi omega (refinedMesh q) j rows4 licensed4
                (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p) =
            exponent5 e chi (refinedMesh q) omega (N : ℝ) rows4 licensed4 J5
              (decodedFamily records q) (tupleHistory p) := by
  obtain ⟨q, hq⟩ := exists_checked_complete_refinement e omega homega records hgrid hcheck
  exact ⟨q, hq, fun chi rows4 licensed4 J5 N hN p hp j hj ht =>
    hq.rawBoxMaximum_eq_original_exponent5 chi rows4 licensed4 J5 N hN p hp j hj ht⟩

end
end ImbalancedChen.P1OriginalFifthFiniteTableRefinementConstructor
