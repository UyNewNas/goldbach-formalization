import ImbalancedChen.P1OriginalPrefixRowDecodeSoundness
import ImbalancedChen.P1CorrectedFifthStoredH45Check

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Rational endpoint-check soundness for decoded original rows. No whole
payload checker is executed or claimed true. The raw wire carries no
original history/owner licence or constant cap5; these remain explicitly
separate data in the original H34/H45 interfaces.
-/

namespace ImbalancedChen.P1OriginalPrefixRowFiniteCheckSoundness
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P2OriginalFourthCapProducerInterface

/-- A finite rational reformulation of the producer Geometry conditions.
The correlated min/max endpoint rows are preserved; no midpoint is used. -/
def fourthGeometryRowsQ (raw : FourthWireRow) : Prop :=
  let r := raw.toProducerRow
  let lo := r.lower
  let hi := r.upper
  9 ≤ r.mask ∧ r.mask ≤ 15 ∧
  (∀ i, r.lo i < r.hi i) ∧
  (∀ i : Fin 3, r.hi i.succ ≤ r.lo i.castSucc) ∧
  (3 / 200 : ℚ) ≤ lo 3 ∧ hi 0 ≤ (39 / 200 : ℚ) ∧
  (∀ j : Fin 6, ∀ side : Bool, (0 : ℚ) <
    max (((tentPlane r.selected side).sub (oldPiece j false)).lower lo hi)
      (((tentPlane r.selected side).sub (oldPiece j true)).lower lo hi)) ∧
  (∃ j : Fin 6, (0 : ℚ) <
    min (((oldPiece j false).sub oldCube).lower lo hi)
      (((oldPiece j true).sub oldCube).lower lo hi)) ∧
  ((∀ side : Bool, (0 : ℚ) < ((tentPlane r.selected side).sub halfGate).lower lo hi) ∧
    (∀ side : Bool, ∀ j : Fin 4, (0 : ℚ) < ((tentPlane r.selected side).sub (fullGate j)).lower lo hi) ∧
    (∀ side : Bool, ∀ j : Fin 4, j ∉ r.selected →
      (0 : ℚ) < ((tentPlane r.selected side).sub (selectedGate r.selected j)).lower lo hi)) ∧
  (∃ j : Fin 6, (0 : ℚ) <
    min (((oldPiece j false).sub sumAffine).upper lo hi)
      (((oldPiece j true).sub sumAffine).upper lo hi)) ∧
  (∀ j : Fin 6,
    min (((oldPiece j false).sub sumAffine).upper lo hi)
      (((oldPiece j true).sub sumAffine).upper lo hi) < 5 * lo 3) ∧
  min (((tentPlane r.selected false).sub sumAffine).upper lo hi)
    (((tentPlane r.selected true).sub sumAffine).upper lo hi) < 5 * lo 3

/-- Rational finite program only; its decidability is constructed before
opening Classical and uses only finite indices and rational comparisons. -/
def fourthGeometryCheck (raw : FourthWireRow) : Bool :=
  @decide (fourthGeometryRowsQ raw) (by
    unfold fourthGeometryRowsQ
    infer_instance)

noncomputable section
open scoped Classical
open Set VariableEnvelope

theorem fourthGeometryCheck_iff (raw : FourthWireRow) :
    fourthGeometryCheck raw = true ↔ fourthGeometryRowsQ raw := by
  simp only [fourthGeometryCheck, decide_eq_true_eq]

/-- The rational row tests supply the actual producer Geometry predicate.
Every witness and every full/selected square test is retained. -/
theorem fourthGeometryCheck_sound (raw : FourthWireRow)
    (hc : fourthGeometryCheck raw = true) : raw.toProducerRow.Geometry := by
  have hq := (fourthGeometryCheck_iff raw).mp hc
  rcases hq with ⟨hmasklo, hmaskhi, hwidth, horder, hcut, htop,
    hgap, hcube, hgates, hR0, hOldUpper, hNewUpper⟩
  refine ⟨hmasklo, hmaskhi, hwidth, horder, hcut, htop, ?_, ?_, ?_, ?_, ?_⟩
  · unfold gapLower
    apply (Finset.lt_inf'_iff _).mpr
    intro j _hj
    apply lt_min
    · change (0 : ℝ) < max _ _
      exact_mod_cast hgap j false
    · change (0 : ℝ) < max _ _
      exact_mod_cast hgap j true
  · unfold oldCubeLower
    apply (Finset.lt_sup'_iff _).mpr
    obtain ⟨j, hj⟩ := hcube
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact_mod_cast hj
  · refine ⟨?_, ?_, ?_⟩
    · intro side
      exact_mod_cast hgates.1 side
    · intro side j
      exact_mod_cast hgates.2.1 side j
    · intro side j hj
      exact_mod_cast hgates.2.2 side j hj
  · unfold oldResidualUpper
    apply (Finset.lt_sup'_iff _).mpr
    obtain ⟨j, hj⟩ := hR0
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact_mod_cast hj
  · unfold newResidualUpper
    apply max_lt
    · unfold oldResidualUpper
      apply (Finset.sup'_lt_iff _).mpr
      intro j _hj
      exact_mod_cast hOldUpper j
    · exact_mod_cast hNewUpper

/-- Source geometry soundness for an actual raw decoded fourth row. -/
theorem decodedFourth_geometry_sound (raw : FourthWireRow)
    (hc : fourthGeometryCheck raw = true) (t : Point)
    (ht : t ∈ raw.toProducerRow.box) :
    oldCube.eval t < oldCap t ∧ oldCap t < raw.toProducerRow.candidate t ∧
      (1 / 2 : ℝ) < raw.toProducerRow.candidate t ∧
      (∀ j, prefixSquareExpr t j < raw.toProducerRow.candidate t) ∧
      (∀ j ∉ raw.toProducerRow.selected,
        selectedSquareExpr raw.toProducerRow.selected t j < raw.toProducerRow.candidate t) :=
  raw.toProducerRow.geometry_sound (fourthGeometryCheck_sound raw hc) t ht

/-- The inherited old cap is the genuine original coarse third cell.
The raw payload does not supply this owner membership: it is explicit. -/
theorem decodedFourth_original_selectedPrefixLicense
    (raw : FourthWireRow) (hc : fourthGeometryCheck raw = true)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ)
    (j : P1OriginalCoarseContinuation.FourthCell m) (t : Point)
    (ht : t ∈ raw.toProducerRow.box)
    (hcoarse : (HistoricalThirdCoarse.box m
      (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox (t 0) (t 1) (t 2)) :
    SelectedPrefixLicense raw.toProducerRow.selected
      (P1OriginalCoarseContinuation.thirdCellExponent e m j) (299 / 500) t :=
  producer_selectedPrefixLicense raw.toProducerRow (fourthGeometryCheck_sound raw hc)
    e he m j t ht hcoarse

/-- A real compact patch supplies a constructive refined constant-cap
radius through the original third owner. A broad saved box is not silently
assigned one constant cap. Finite H34 checks can consume this refinement. -/
theorem decodedFourth_original_refinement_radius
    (raw : FourthWireRow) (hc : fourthGeometryCheck raw = true)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ)
    (j : P1OriginalCoarseContinuation.FourthCell m)
    (K : Set Point) (hK : IsCompact K) (hKbox : K ⊆ raw.toProducerRow.box)
    (hcoarse : ∀ t ∈ K, (HistoricalThirdCoarse.box m
      (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox (t 0) (t 1) (t 2)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ K, ∀ l u : QEndpoint,
      dist (fun i => (l i : ℝ)) t < delta → dist (fun i => (u i : ℝ)) t < delta →
      selectedBoxCapCheck raw.toProducerRow.selected
        (P1OriginalCoarseContinuation.thirdCellExponent e m j) (299 / 500) l u = true :=
  producer_compact_refinement_radius raw.toProducerRow (fourthGeometryCheck_sound raw hc)
    e he m j K hK hKbox hcoarse

/-- Actual finite producer family obtained by decoding the raw records.
This mapping does not interpret a numeric gain as an owner or licence. -/
def decodedFourthFamily (raw : Finset FourthWireRow) : Finset ProducerRow :=
  raw.image FourthWireRow.toProducerRow

theorem mem_decodedFourthFamily (raw : Finset FourthWireRow) (r : ProducerRow) :
    r ∈ decodedFourthFamily raw ↔ ∃ record ∈ raw, record.toProducerRow = r := by
  simp only [decodedFourthFamily, Finset.mem_image]

theorem decodedFourthFamily_geometry (raw : Finset FourthWireRow)
    (hchecks : ∀ record ∈ raw, fourthGeometryCheck record = true)
    (r : ProducerRow) (hr : r ∈ decodedFourthFamily raw) : r.Geometry := by
  obtain ⟨record, hrecord, rfl⟩ := (mem_decodedFourthFamily raw r).mp hr
  exact fourthGeometryCheck_sound record (hchecks record hrecord)

/-- Filtering makes a genuinely licensed finite subfamily even when no
whole-payload all-pass witness has been checked. Dropping failing records
is not asserted to preserve a saved numerical gain. -/
def checkedFourthFamily (raw : Finset FourthWireRow) : Finset ProducerRow :=
  decodedFourthFamily (raw.filter (fun record => fourthGeometryCheck record = true))

theorem checkedFourthFamily_geometry (raw : Finset FourthWireRow)
    (r : ProducerRow) (hr : r ∈ checkedFourthFamily raw) : r.Geometry := by
  obtain ⟨record, hrecord, rfl⟩ := (mem_decodedFourthFamily _ r).mp hr
  exact fourthGeometryCheck_sound record (Finset.mem_filter.mp hrecord).2

/-- Signed raw masks are preserved exactly whenever the lawful decoder
accepts a row; toNat is never silently applied to a negative mask. -/
theorem decodedFifth_mask_roundtrip (raw : FifthWireRow) (m : ℕ)
    (r : P1OriginalVariableFifthContinuation.FifthRow m)
    (hr : r ∈ decodeFifthRows raw m) : (raw.mask.toNat : ℤ) = raw.mask :=
  Int.toNat_of_nonneg ((mem_decodeFifthRows_iff raw m r).mp hr).2.1

theorem decodedFifth_mem_original_slot (raw : FifthWireRow) (m : ℕ)
    (r : P1OriginalVariableFifthContinuation.FifthRow m)
    (hr : r ∈ decodeFifthRows raw m) (i : Fin 5) :
    i ∈ r.selected ↔ Nat.testBit raw.mask.toNat i.val = true := by
  rw [decodeFifthRows_selected_eq raw m r hr]
  exact mem_maskSlots i

/-- Jensen statistics remain opaque to the geometric decoder. In
particular they do not supply a dynamic parent, owner licence or cap5. -/
theorem decodeFifthRows_ignores_statistics (grid : ℤ) (lo : Fin 5 → ℤ) (mask : ℤ)
    (gap1 A1 B1 gap2 A2 B2 : ℤ) (m : ℕ) :
    decodeFifthRows ⟨grid, lo, mask, gap1, A1, B1⟩ m =
      decodeFifthRows ⟨grid, lo, mask, gap2, A2, B2⟩ m := rfl
/-- Once an actual original owner assignment has been supplied, the
finite refined endpoint checks produce the literal original H34 check.
The wire itself contains neither that assignment nor a stored cap table. -/
theorem decodedFourth_refined_h34Check
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (owners : P1OriginalCoarseContinuation.FourthCell m → FourthWireRow)
    (hchecks : ∀ j ∈ P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4,
      selectedBoxCapCheck (owners j).toProducerRow.selected
        (P1OriginalCoarseContinuation.thirdCellExponent e m j) (299 / 500)
        (qLogPrimeMeshLo 0 (19 / 96) m j) (qLogPrimeMeshHi 0 (19 / 96) m j) = true) :
    P1OriginalCoarseContinuation.h34Check e chi m omega J4
      (refinedCap e m (fun j => (owners j).toProducerRow.selected)) = true :=
  refined_h34Check e chi m omega J4 (fun j => (owners j).toProducerRow.selected) hchecks
/-- A supplied CONSTANT-cap table has a separate actual finite H45 check.
Raw fifth masks/Jensen statistics cannot manufacture D.cap5 or howned. -/
theorem decodedFamily_storedH45_sound
    (D : HistoricalPrefixCapData) (J : Finset (Fin 5 → Fin (D.m + 1)))
    (e : ℚ) (chi omega : ℝ) (raw : Finset FourthWireRow)
    (licensed4 : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : P1CorrectedFifthStoredH45Check.storedH45Check D J e (decodedFourthFamily raw) = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5 ∩ J)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) D.m j) :
    P1CorrectedFifthDensityDictionary.originalVariableFourthProfile
      e chi omega D.m j (decodedFourthFamily raw) licensed4 t ≤ (D.cap5 j : ℝ) :=
  P1CorrectedFifthStoredH45Check.originalVariableFourthProfile_le_storedCap
    D J e chi omega (decodedFourthFamily raw) licensed4 howned hcheck j hj t ht

end
end ImbalancedChen.P1OriginalPrefixRowFiniteCheckSoundness