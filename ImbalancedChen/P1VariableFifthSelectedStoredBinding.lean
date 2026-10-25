import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P4AOriginalHistoricalFifthSelectedSlotBridge

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Compose the original variable fifth profile with the *stored* selected
historical fifth caps.  A checked stored cap below M_I(t) need not be below
M_I(t)-2e: the missing buffer is a separate finite rational endpoint check.
This module records that check on every selected original row and proves the
pointwise comparison on its half-open owner.  It also binds those rows to the
variable fifth finite maximum on the original coarse third/rough selection.

The generic `HistoricalPrefixCapData` has independent third/fourth fields;
its third policy cannot be identified with the original coarse policy from
the existing type alone.  Both constructions retain their own exact third
parent and first-stop frontier.  A cross-parent data identification remains
a separate source obligation, not an assumed target bound or saving.
-/

namespace ImbalancedChen.P1VariableFifthSelectedStoredBinding

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

abbrev Label5 (D : HistoricalPrefixCapData) := Fin 5 → Fin (D.m + 1)

def row (D : HistoricalPrefixCapData) (I : Label5 D → Finset (Fin 5))
    (j : Label5 D) : P1OriginalVariableFifthContinuation.FifthRow D.m :=
  ⟨j, I j⟩

theorem same_literal_original_envelope (I : Finset (Fin 5)) (t : Fin 5 → ℝ) :
    P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.originalEnvelope I t =
      P1OriginalVariableFifthContinuation.envelope I t := rfl

/-- Exactly the selected stored family, with its literal per-cell mask.
The row table is finite before any target or history is introduced. -/
def rows (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (I : Label5 D → Finset (Fin 5)) : Finset (P1OriginalVariableFifthContinuation.FifthRow D.m) :=
  (D.cells5 ∩ J).image (row D I)

theorem row_mem (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (I : Label5 D → Finset (Fin 5)) (j : Label5 D)
    (hj : j ∈ D.cells5 ∩ J) : row D I j ∈ rows D J I := by
  exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

/-- Finite source-geometry binding: the historical mesh is the original
0..19/96 mesh, and every selected stored owner passes the original coarse
third-cell and whole-cell rough tests. -/
def OriginalOwnedRows (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (e : ℚ) (chi omega : ℝ) : Prop :=
  D.a = 0 ∧ D.b = 19 / 96 ∧
    ∀ j ∈ D.cells5 ∩ J,
      historicalPrefixProject (by omega : 3 ≤ 5) j ∈
          HistoricalThirdCoarse.cells (e : ℝ) chi D.m ∧
        omega ≤ (qLogPrimeMeshLo 0 (19 / 96) D.m
          (historicalPrefixProject (by omega : 3 ≤ 5) j) 2 : ℝ)

/-- The extra `2e` headroom is checked against the exact lower interval
bound for M_I.  `gateCheck` separately licenses the pointwise variable cap's
full and selected square gates.  Neither is a target-dependent inequality. -/
def BufferedStoredRows (D : HistoricalPrefixCapData)
    (J : Finset (Label5 D)) (I : Label5 D → Finset (Fin 5))
    (e : ℚ) : Prop :=
  ∀ j ∈ D.cells5 ∩ J,
    D.cap5 j + 2 * e ≤
      qVLo
        (∑ i ∈ I j, qLogPrimeMeshLo D.a D.b D.m j i)
        (∑ i ∈ I j, qLogPrimeMeshHi D.a D.b D.m j i) ∧
      P1OriginalVariableFifthContinuation.gateCheck e D.m (row D I j) = true

theorem stored_parent_and_fourth_gates_unchanged
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (N : ℝ) (j : Label5 D) :
    (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).upperThirdPolicy N =
        D.upperThirdPolicy N ∧
      (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).upperFourthPolicy N =
        D.upperFourthPolicy N ∧
      (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).fifthParentGateBounds j =
        D.fifthParentGateBounds j := by
  exact ⟨(P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.stored_same_historical_parent
    D J N).1,
    (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.stored_same_historical_parent
      D J N).2.1, rfl⟩

theorem stored_firstStop_carrier_unchanged
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (N : ℝ) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4
        ((P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).upperThirdPolicy N)
        h pre positive mass carrier =
      firstExitDepthFrontier 4 (D.upperThirdPolicy N)
        h pre positive mass carrier := by
  rw [(P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.stored_same_historical_parent
    D J N).1]

/-- The variable continuation keeps the original coarse third first-stop
frontier on every supplied carrier.  The two retained-parent identities are
separate because `D` itself has no original-coarse source identification. -/
theorem variable_firstStop_original_carrier
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m))
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4
        (P1OriginalVariableFifthContinuation.policy5 e chi m omega N
          rows4 licensed4 J5 rows5) h pre positive mass carrier =
      firstExitDepthFrontier 4
        (P1OriginalVariableFourthContinuation.producerPolicy4
          (e : ℝ) chi m omega N rows4 licensed4)
        h pre positive mass carrier := by
  exact P1OriginalVariableFifthContinuation.same_rank_four_frontier
    e chi m omega N rows4 licensed4 J5 rows5 h pre carrier positive mass

/-- A cross-parent T3 equality has exactly these two source identities.
They are equations of the original base and Q3 functions, not a target
inequality, and are not supplied by a generic `HistoricalPrefixCapData`. -/
theorem exact_same_T3_of_source_identification
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (hbase : ordinaryParityRosserPolicy false (N ^ (D.old : ℝ)) =
      HistoricalThirdCoarse.initialPolicy (e : ℝ) D.m N)
    (hQ3 : D.level3 N =
      HistoricalThirdCoarse.rawLevel (e : ℝ) chi D.m omega N) :
    (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).upperThirdPolicy N =
      HistoricalThirdCoarse.policy (e : ℝ) chi D.m omega N := by
  rw [(P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.stored_same_historical_parent
    D J N).1]
  simp only [HistoricalPrefixCapData.upperThirdPolicy, HistoricalThirdCoarse.policy]
  rw [hbase, hQ3]

/-- The literal stored cap, including its actual inherited `D.old5`, is
below the continuous buffered original fifth cap at every point of the
selected half-open owner.  This implication needs the rational buffer test;
the stored whole-box permit alone only gives cap5 < M_I. -/
theorem stored_cap_le_variable_candidate
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (I : Label5 D → Finset (Fin 5)) (nu : Label5 D → ℚ)
    (e : ℚ) (hpermit : P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.storedFifthPermit D J I nu)
    (hbuffer : BufferedStoredRows D J I e)
    (j : Label5 D) (hj : j ∈ D.cells5 ∩ J)
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.old5 j : ℝ) < (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).cap5 j ∧
      ((P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).cap5 j : ℝ) ≤
        P1OriginalVariableFifthContinuation.candidate (e : ℝ) (I j) t ∧
      (∀ k, prefixSquareExpr t k < (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).cap5 j) ∧
      (∀ k ∉ I j,
        selectedSquareExpr (I j) t k < (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).cap5 j) := by
  have hstored := P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.stored_cell_license D J I nu hpermit j hj t ht
  have hlo (i : Fin 5) :
      (qLogPrimeMeshLo D.a D.b D.m j i : ℝ) ≤ t i := by
    rw [congrFun (cast_qLogPrimeMeshLo D.a D.b D.m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  have hhi (i : Fin 5) :
      t i ≤ (qLogPrimeMeshHi D.a D.b D.m j i : ℝ) := by
    rw [congrFun (cast_qLogPrimeMeshHi D.a D.b D.m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).2.le
  have hslo :
      ((∑ i ∈ I j, qLogPrimeMeshLo D.a D.b D.m j i : ℚ) : ℝ) ≤
        ∑ i ∈ I j, t i := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => hlo i)
  have hshi :
      (∑ i ∈ I j, t i) ≤
        ((∑ i ∈ I j, qLogPrimeMeshHi D.a D.b D.m j i : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => hhi i)
  have hv := qVLo_le_v hslo hshi
  have hq := (hbuffer j hj).1
  have hr : (D.cap5 j : ℝ) + 2 * (e : ℝ) ≤
      v (∑ i ∈ I j, t i) := by
    have hcast :
        ((D.cap5 j + 2 * e : ℚ) : ℝ) ≤
          (qVLo
            (∑ i ∈ I j, qLogPrimeMeshLo D.a D.b D.m j i)
            (∑ i ∈ I j, qLogPrimeMeshHi D.a D.b D.m j i) : ℝ) :=
      Rat.cast_le.mpr hq
    push_cast at hcast
    exact hcast.trans hv
  have hcap : (D.cap5 j : ℝ) ≤ P1OriginalVariableFifthContinuation.candidate (e : ℝ) (I j) t := by
    rw [P1OriginalVariableFifthContinuation.candidate, P1OriginalVariableFifthContinuation.envelope_eq_v]
    linarith
  simp only [P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.stored_cap_unchanged] at hstored ⊢
  exact ⟨hstored.1, hcap, hstored.2.2.1, hstored.2.2.2⟩

/-- Every checked stored owner enters the variable fifth maximum with the
same mask and original rough/third-cell gate.  The resulting comparison
uses the actual fourth producer seed, even when other fifth rows overlap. -/
theorem stored_cap_le_variable_fifth_exponent
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (I : Label5 D → Finset (Fin 5)) (nu : Label5 D → ℚ)
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : OriginalOwnedRows D J e chi omega)
    (hpermit : P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.storedFifthPermit D J I nu)
    (hbuffer : BufferedStoredRows D J I e)
    (hN : 1 ≤ N)
    (pre : List ℕ) (hlen : pre.length = 5)
    (j : Label5 D) (hj : j ∈ D.cells5 ∩ J)
    (ht : P1OriginalVariableFifthContinuation.Point5)
    (hcoord : ht = primeHistoryLogCoordinates N 5 pre)
    (hcell : ht ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    (D.old5 j : ℝ) < (P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).cap5 j ∧
      ((P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.bindStoredFifth D J).cap5 j : ℝ) ≤
        P1OriginalVariableFifthContinuation.exponent5 e chi D.m omega N rows4 licensed4
          (D.cells5 ∩ J) (rows D J I) pre ∧
      P1OriginalVariableFourthContinuation.producerLevel4 (e : ℝ) chi D.m omega N rows4 licensed4
          (rosserAncestor 4 pre) ≤
        P1OriginalVariableFifthContinuation.level5 e chi D.m omega N rows4 licensed4
          (D.cells5 ∩ J) (rows D J I) pre := by
  have hbound := stored_cap_le_variable_candidate
    D J I nu e hpermit hbuffer j hj ht hcell
  have hselected : j ∈
      P1OriginalCoarseFifthContinuation.selectedFifthCells
        e chi D.m omega (D.cells5 ∩ J) := by
    apply (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells
      e chi D.m omega (D.cells5 ∩ J) j).mpr
    exact ⟨hj, (howned.2.2 j hj).1, (howned.2.2 j hj).2⟩
  have hcell' : primeHistoryLogCoordinates N 5 pre ∈
      logPrimeMeshCell 0 (19 / 96) D.m j := by
    rw [← hcoord]
    simpa only [howned.1, howned.2.1, Rat.cast_zero, Rat.cast_div,
      Rat.cast_ofNat] using hcell
  have he : P1OriginalVariableFifthContinuation.eligible e chi D.m omega (D.cells5 ∩ J)
      (row D I j) (primeHistoryLogCoordinates N 5 pre) := by
    exact ⟨hselected, (hbuffer j hj).2, hcell'⟩
  have hr : P1OriginalVariableFifthContinuation.candidate (e : ℝ) (I j) (primeHistoryLogCoordinates N 5 pre) ≤
      P1OriginalVariableFifthContinuation.exponent5 e chi D.m omega N rows4 licensed4
        (D.cells5 ∩ J) (rows D J I) pre := by
    simpa [row] using
      P1OriginalVariableFifthContinuation.fifth_row_le_exponent5 e chi D.m omega N rows4 licensed4
        (D.cells5 ∩ J) (rows D J I) pre hlen (row D I j)
        (row_mem D J I j hj) he
  have hlevel := P1OriginalVariableFifthContinuation.fourthLevel_le_fifthLevel e chi D.m omega N
    rows4 licensed4 (D.cells5 ∩ J) (rows D J I) hN pre
  refine ⟨hbound.1, ?_, hlevel⟩
  rw [hcoord] at hbound
  exact hbound.2.1.trans hr

end
end ImbalancedChen.P1VariableFifthSelectedStoredBinding
