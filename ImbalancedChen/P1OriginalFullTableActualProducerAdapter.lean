import ImbalancedChen.P1OriginalFourthPackedTableDecoder
import ImbalancedChen.P1OriginalPrefixRowDecodeSoundness
import ImbalancedChen.P1OriginalPrefixRowFiniteCheckSoundness
import ImbalancedChen.P1HistoricalFifthTableParser
import ImbalancedChen.P1ActualVariableFifthFullMean

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Complete raw input is kept as ordered typed records. Its policy image is a
finite set, so repeated identical policy rows collapse only at this explicit
image boundary. Fourth coordinates/masks have their original meaning.
Fifth records decode conservatively into contained cells of a specified
mesh; no whole-box cover or historical dynamic-parent identity is asserted.
The complete archived binary-to-record parse and full passing checks have
not been executed in Lean and are NOT asserted here. Opaque saved statistics
are not invented licences or constant caps. No giant payload is imported.
-/

namespace ImbalancedChen.P1OriginalFullTableActualProducerAdapter
noncomputable section
open scoped Classical BigOperators
open Filter Topology
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFifthContinuation
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthMovingScaleLimit

/-- Explicit bridge between the byte decoder ABI and the shared row ABI. -/
def fourthFromPacked (r : P1OriginalFourthPackedTable.FourthWireRow) : FourthWireRow :=
  ⟨r.lo, r.hi, r.mask⟩

theorem fourthFromPacked_exact (r : P1OriginalFourthPackedTable.FourthWireRow) :
    (fourthFromPacked r).toProducerRow = r.toProducerRow := rfl

def fourthFamily (records : List FourthWireRow) : Finset ProducerRow :=
  (records.map FourthWireRow.toProducerRow).toFinset

theorem mem_fourthFamily_iff (records : List FourthWireRow) (r : ProducerRow) :
    r ∈ fourthFamily records ↔ ∃ raw ∈ records, raw.toProducerRow = r := by
  simp [fourthFamily]

theorem fourthFamily_eq_finite_decoder (records : List FourthWireRow) :
    fourthFamily records =
      P1OriginalPrefixRowFiniteCheckSoundness.decodedFourthFamily records.toFinset := by
  ext r
  simp [fourthFamily, P1OriginalPrefixRowFiniteCheckSoundness.decodedFourthFamily]

/-- An eventual whole-table pass witness has precisely this explicit
meaning. No such witness is supplied for the archived payload. -/
theorem fourthFamily_geometry (records : List FourthWireRow)
    (hchecks : ∀ raw ∈ records,
      P1OriginalPrefixRowFiniteCheckSoundness.fourthGeometryCheck raw = true)
    (r : ProducerRow) (hr : r ∈ fourthFamily records) : r.Geometry := by
  rw [fourthFamily_eq_finite_decoder] at hr
  exact P1OriginalPrefixRowFiniteCheckSoundness.decodedFourthFamily_geometry records.toFinset
    (fun raw hraw => hchecks raw (List.mem_toFinset.mp hraw)) r hr

/-- This is a licensed subfamily even without a whole-payload pass claim.
Filtering is not asserted to preserve the saved numerical total. -/
def checkedFourthRows (records : List FourthWireRow) : Finset ProducerRow :=
  P1OriginalPrefixRowFiniteCheckSoundness.checkedFourthFamily records.toFinset

theorem checkedFourthRows_geometry (records : List FourthWireRow)
    (r : ProducerRow) (hr : r ∈ checkedFourthRows records) : r.Geometry :=
  P1OriginalPrefixRowFiniteCheckSoundness.checkedFourthFamily_geometry records.toFinset r hr

def packedFourthFamily (bytes : List ℕ) : Option (Finset ProducerRow) := do
  let records ← P1OriginalFourthPackedTable.decodeWireRows bytes
  pure (fourthFamily (records.map fourthFromPacked))

theorem packedFourthFamily_of_decode (bytes : List ℕ)
    (records : List P1OriginalFourthPackedTable.FourthWireRow)
    (hparse : P1OriginalFourthPackedTable.decodeWireRows bytes = some records) :
    packedFourthFamily bytes = some (fourthFamily (records.map fourthFromPacked)) := by
  simp [packedFourthFamily, hparse]

def fifthFamily (records : List FifthWireRow) (m : ℕ) : Finset (FifthRow m) :=
  records.toFinset.biUnion (fun raw => decodeFifthRows raw m)

theorem mem_fifthFamily_iff (records : List FifthWireRow) (m : ℕ) (r : FifthRow m) :
    r ∈ fifthFamily records m ↔ ∃ raw ∈ records, r ∈ decodeFifthRows raw m := by
  simp [fifthFamily]

theorem fifthFamily_eq_array_parser (records : Array FifthWireRow) (m : ℕ) :
    fifthFamily records.toList m = P1HistoricalFifthTableParser.decodeTableAt records m := rfl

/-- Every output row carries an authentic input-record witness. Containment
and processing-slot mask semantics come from the actual decoder proof. -/
theorem fifthFamily_source_geometry (records : List FifthWireRow) (m : ℕ)
    (r : FifthRow m) (hr : r ∈ fifthFamily records m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    ∃ raw ∈ records, 0 < raw.grid ∧ 0 ≤ raw.mask ∧
      r.selected = maskSlots 5 raw.mask.toNat ∧ t ∈ raw.originalBox := by
  obtain ⟨raw, hraw, hd⟩ := (mem_fifthFamily_iff records m r).mp hr
  exact ⟨raw, hraw, decodeFifthRows_source_geometry raw m r hd t ht⟩

def checkedFifthFamily (records : List FifthWireRow) (m : ℕ) (e : ℚ) :
    Finset (FifthRow m) :=
  records.toFinset.biUnion (fun raw => checkedFifthRows raw m e)

theorem checkedFifthFamily_eq_array_parser (records : Array FifthWireRow) (m : ℕ) (e : ℚ) :
    checkedFifthFamily records.toList m e = P1HistoricalFifthTableParser.checkedTableAt records m e := rfl

theorem checkedFifthFamily_sound (records : List FifthWireRow) (m : ℕ) (e : ℚ)
    (r : FifthRow m) (hr : r ∈ checkedFifthFamily records m e)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    ∃ raw ∈ records, t ∈ raw.originalBox ∧ r.selected = maskSlots 5 raw.mask.toNat ∧
      (1 / 2 : ℝ) < candidate (e : ℝ) r.selected t ∧
      (∀ k, prefixSquareExpr t k < candidate (e : ℝ) r.selected t) ∧
      (∀ k ∉ r.selected, selectedSquareExpr r.selected t k < candidate (e : ℝ) r.selected t) := by
  obtain ⟨raw, hraw, hrow⟩ := Finset.mem_biUnion.mp hr
  exact ⟨raw, List.mem_toFinset.mp hraw, checkedFifthRows_sound raw m e r hrow t ht⟩

/-- Passing rational row gates do not silently supply the original ancestor
licence: actual selected-owner membership remains explicit. -/
theorem checkedFifthFamily_original_eligible
    (records : List FifthWireRow) (m : ℕ) (e : ℚ) (chi omega : ℝ)
    (J5 : Finset (Label5 m)) (r : FifthRow m)
    (hr : r ∈ checkedFifthFamily records m e)
    (howner : r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    eligible e chi m omega J5 r t := by
  obtain ⟨raw, _hraw, hrow⟩ := Finset.mem_biUnion.mp hr
  exact checkedFifthRows_original_eligible raw m e chi omega J5 r hrow howner t ht

/-- Ordered raw records now enter the actual finite producer, not an
unrelated ordinary parent. This analytic theorem needs no claimed full
table parse/check success; it applies to the explicit decoded row families.
Which decoded rows reproduce the historical dynamic selection remains a
separate original-data obligation. -/
theorem decodedFamilies_actualFourthFifth_mean
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (licensed4 : ProducerRow → Prop) (J5 : Finset (Label5 m)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (P1OriginalFourthFifthTotalTupleSource.originalThirdRetained
          e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) -
        P1CorrectedFifthDensityDictionary.variableFifthRetained
          e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
          (fourthFamily records4) licensed4 J5 (fifthFamily records5 m)) *
        Real.log (N : ℝ) / singularSeries N)
      evenTargets
      (𝓝 (P1OriginalVariableFourthFullActiveIntegral.fullActiveIntegral
        e chi m omega (fourthFamily records4) licensed4 +
        P1ActualVariableFifthUntruncatedDomination.fullSelectedIntegral
          e chi m omega (fourthFamily records4) licensed4 J5 (fifthFamily records5 m))) :=
  P1ActualVariableFifthFullMean.tendsto_originalThird_sub_variableFifth_totalIntegral
    e he chi m omega homega homegaRho hmesh
    (fourthFamily records4) licensed4 J5 (fifthFamily records5 m) cap hcap

end
end ImbalancedChen.P1OriginalFullTableActualProducerAdapter
