import ImbalancedChen.P1FifthUnitBoxLiteralGainLower
import ImbalancedChen.P1OriginalFifthFiniteTableRefinementConstructor

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A finite checker-soundness endpoint for the entire loaded unit-row family.
The primitive checks concern grid400, LO-key Nodup before deduplication,
positive lower endpoints, and correlated rational support gates. They do
not encode a desired mean, gain, dynamic parent or numerical endpoint.

One complete aligned refinement is chosen before every actual fourth-row
family, original selected-owner set and inherited fourth profile. Its true
variable-fifth integral equals the original loaded list's raw-owner gain
sum and bounds the corresponding literal MI-minus-old15 lower sum.

No historical flag is evaluated. In particular the actual292633-row
passing witness remains UNEXECUTED / ready=false.
-/
namespace ImbalancedChen.P1FifthCheckedUnitBoxWholeGain

open P1OriginalPrefixRowDecodeSoundness
open P1FifthGrid400UnitBoxPartition P1FifthUnitBoxLiteralGainLower
open P1OriginalFifthCorrelatedRawBoxGates

/-- Finite raw-row checks only, with no decoded-cell enumeration. -/
def loadedCorrelatedGateCheck (e : ℚ) (raw : Array FifthWireRow) : Bool :=
  raw.toList.all (fun row => correlatedRawBoxGateCheck e row)

def loadedUnitGainCheck (e : ℚ) (raw : Array FifthWireRow) : Bool :=
  unitFamilyPartitionCheck raw && (positiveUnitKeyCheck raw && loadedCorrelatedGateCheck e raw)

noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthUnitBoxGainDecomposition
open P1OriginalFifthFiniteTableRefinementConstructor
open P2OriginalFourthCapProducerInterface
open P1ActualVariableFifthUntruncatedDomination

theorem loadedCorrelatedGateCheck_sound (e : ℚ) (raw : Array FifthWireRow)
    (hc : loadedCorrelatedGateCheck e raw = true) :
    ∀ row ∈ raw.toList, correlatedRawBoxGateCheck e row = true := by
  simpa only [loadedCorrelatedGateCheck, List.all_eq_true] using hc

theorem loadedUnitGainCheck_sound (e : ℚ) (raw : Array FifthWireRow)
    (hc : loadedUnitGainCheck e raw = true) :
    unitFamilyPartitionCheck raw = true ∧ positiveUnitKeyCheck raw = true ∧
      ∀ row ∈ raw.toList, correlatedRawBoxGateCheck e row = true := by
  have hs : unitFamilyPartitionCheck raw = true ∧
      (positiveUnitKeyCheck raw = true ∧ loadedCorrelatedGateCheck e raw = true) := by
    simpa only [loadedUnitGainCheck, Bool.and_eq_true] using hc
  exact ⟨hs.1, hs.2.1, loadedCorrelatedGateCheck_sound e raw hs.2.2⟩

def actualRawOwnerSum (row : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Fin 5 → Fin (m + 1))) : ℝ :=
  ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
    rawOwnerIntegral row e chi m omega j rows4 licensed4

def literalRawOwnerSum (row : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J5 : Finset (Fin 5 → Fin (m + 1))) : ℝ :=
  ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
    literalRawOwnerIntegral row e chi m omega j

/-- All actual history/profile inputs are selected AFTER the common q.
The sum retains the loaded list's order and multiplicities, and its proof
pays key-Nodup explicitly rather than silently deleting records. -/
theorem exists_checked_complete_refinement_with_whole_gain
    (e : ℚ) (he : 0 ≤ e) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (raw : Array FifthWireRow) (hc : loadedUnitGainCheck e raw = true) :
    ∃ q : ℕ, CheckedCompleteRefinement e omega raw.toList.toFinset q ∧
      ∀ (chi : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
        (J5 : Finset (RefinedCell q)),
      fullSelectedIntegral e chi (refinedMesh q) omega rows4 licensed4 J5
          (decodedFamily raw.toList.toFinset q) =
        (raw.toList.map (fun row =>
          actualRawOwnerSum row e chi (refinedMesh q) omega rows4 licensed4 J5)).sum ∧
      ((∀ r ∈ rows4, licensed4 r → r.Geometry) →
        (raw.toList.map (fun row =>
          literalRawOwnerSum row e chi (refinedMesh q) omega J5)).sum ≤
        fullSelectedIntegral e chi (refinedMesh q) omega rows4 licensed4 J5
          (decodedFamily raw.toList.toFinset q)) := by
  have hs := loadedUnitGainCheck_sound e raw hc
  have hp := unitFamilyPartitionCheck_sound raw hs.1
  have hgrid : ∀ row ∈ raw.toList.toFinset, row.grid = 400 :=
    fun row hr => hp.1 row (List.mem_toFinset.mp hr)
  have hchecks : ∀ row ∈ raw.toList.toFinset, correlatedRawBoxGateCheck e row = true :=
    fun row hr => hs.2.2 row (List.mem_toFinset.mp hr)
  obtain ⟨q, hq⟩ := exists_checked_complete_refinement e omega homega
    raw.toList.toFinset hgrid hchecks
  refine ⟨q, hq, ?_⟩
  intro chi rows4 licensed4 J5
  constructor
  · exact checked_loaded_fullSelectedIntegral_eq_raw_list_sum raw hs.1 q hq.positive
      (fun row hr => hq.nonnegativeMask row (List.mem_toFinset.mpr hr))
      e he chi omega homega homegaRho rows4 licensed4 J5 hq.allGates
  · intro hgeometry
    have hpositive : ∀ row ∈ raw.toList.toFinset, ∀ i, 1 ≤ row.lo i :=
      fun row hr => positiveUnitKeyCheck_sound raw hs.2.1 row (List.mem_toFinset.mp hr)
    have hkey := loaded_key_injective_finset raw (Bool.and_eq_true.mp hs.1).2
    have hl := sum_literalRawOwnerIntegrals_le_fullSelectedIntegral raw.toList.toFinset
      q hq.positive hq.grid400 hq.nonnegativeMask hkey hpositive
      e he chi omega homega homegaRho rows4 licensed4 hgeometry J5 hq.allGates
    have hsum := sum_loaded_records_eq_finset raw (Bool.and_eq_true.mp hs.1).2
      (fun row => literalRawOwnerSum row e chi (refinedMesh q) omega J5)
    change (∑ row ∈ raw.toList.toFinset,
      literalRawOwnerSum row e chi (refinedMesh q) omega J5) ≤ _ at hl
    rw [← hsum] at hl
    exact hl

end
end ImbalancedChen.P1FifthCheckedUnitBoxWholeGain
