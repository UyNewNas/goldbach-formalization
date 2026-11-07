import ImbalancedChen.P1OriginalVariableFourthContinuation
import ImbalancedChen.P2OriginalFourthCapProducerInterface

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Literal canonical saved fourth row: representative_boxes[0] in
../goldbach-research/certify_fourth_prefix_stronger.json
SHA256 a8ddd29369e6193017790c8479ea68826b17680975f2e8abfdd75a08bc8fbfa7.
The same JSON pins NPZ dc004c1bc500101ed2d38c71f186cd6b9e1d4d90824e85cc1dddb7e843c3eb2b
and producer 25069573985d30beae59a1a2a89ddeb79e56f696e78a5fae5153de0bb8bd378a.
The published numerical-source manifest independently pins these bytes.

The saved row has mask 9, coordinates on lattice 204800, lower endpoints
[20480,20224,20096,18688], upper [20736,20352,20224,18944]. No row gain,
derivative table, numerical quadrature or certificate replay is used.

The payload does not fix a numerical buffer. We preserve the original
symbolic candidate v(t0+t3)-2e, and prove its gates for 0<=e<3/25600.
No convenient replacement row, midpoint cap, or invented fixed buffer is
substituted. Mean/cost evaluation and full adopted coverage remain OPEN.
-/

namespace ImbalancedChen.P1HistoricalFourthMask9Row

noncomputable section
open Set VariableEnvelope P2OriginalFourthCapProducerInterface
open scoped Classical BigOperators

def savedRow : ProducerRow :=
  ⟨![20480, 20224, 20096, 18688], ![20736, 20352, 20224, 18944], 9⟩

theorem savedRow_selected : savedRow.selected = ({0, 3} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> decide

/-- A strict correlated margin, proved from the literal endpoint record. -/
theorem savedRow_gap_lower : (1 / 3200 : ℝ) ≤
    gapLower savedRow.selected savedRow.lower savedRow.upper := by
  unfold gapLower
  apply Finset.le_inf'
  intro j _hj
  fin_cases j <;>
    norm_num [gapPiece, savedRow_selected, savedRow, ProducerRow.lower, ProducerRow.upper,
      tentPlane, oldPiece, oldMask, Affine.sub, Affine.lower, Fin.sum_univ_succ]

theorem savedRow_oldCube_lower : (1 / 25 : ℝ) ≤
    oldCubeLower savedRow.lower savedRow.upper := by
  calc
    _ ≤ min (((oldPiece 0 false).sub oldCube).lower savedRow.lower savedRow.upper : ℝ)
        (((oldPiece 0 true).sub oldCube).lower savedRow.lower savedRow.upper : ℝ) := by
      norm_num [savedRow, ProducerRow.lower, ProducerRow.upper, oldPiece, oldMask,
        tentPlane, oldCube, Affine.sub, Affine.lower, Fin.sum_univ_succ]
    _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ (0 : Fin 6))

/-- The complete full and selected-complement square tests are retained.
These are rational affine endpoint calculations, not a top-slot surrogate. -/
theorem savedRow_gate_margins :
    (∀ side, (9 / 100 : ℝ) ≤
      (((tentPlane savedRow.selected side).sub halfGate).lower savedRow.lower savedRow.upper : ℝ)) ∧
    (∀ side j, (9 / 100 : ℝ) ≤
      (((tentPlane savedRow.selected side).sub (fullGate j)).lower savedRow.lower savedRow.upper : ℝ)) ∧
    (∀ side j, j ∉ savedRow.selected → (9 / 100 : ℝ) ≤
      (((tentPlane savedRow.selected side).sub (selectedGate savedRow.selected j)).lower
        savedRow.lower savedRow.upper : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro side
    cases side <;>
      norm_num [savedRow_selected, savedRow, ProducerRow.lower, ProducerRow.upper,
        tentPlane, halfGate, Affine.sub, Affine.lower, Fin.sum_univ_succ]
  · intro side j
    cases side <;> fin_cases j <;>
      norm_num [savedRow_selected, savedRow, ProducerRow.lower, ProducerRow.upper,
        tentPlane, fullGate, Affine.sub, Affine.lower, Fin.sum_univ_succ]
  · intro side j hj
    cases side <;> fin_cases j <;>
      norm_num [savedRow_selected, savedRow, ProducerRow.lower, ProducerRow.upper,
        tentPlane, selectedGate, Affine.sub, Affine.lower, Fin.sum_univ_succ] at hj ⊢

theorem savedRow_oldResidual_lower : (1 / 10 : ℝ) ≤
    oldResidualUpper savedRow.lower savedRow.upper := by
  calc
    _ ≤ min (((oldPiece 0 false).sub sumAffine).upper savedRow.lower savedRow.upper : ℝ)
        (((oldPiece 0 true).sub sumAffine).upper savedRow.lower savedRow.upper : ℝ) := by
      norm_num [savedRow, ProducerRow.lower, ProducerRow.upper, oldPiece, oldMask,
        tentPlane, sumAffine, Affine.sub, Affine.upper, Affine.neg, Affine.lower,
        Fin.sum_univ_succ]
    _ ≤ _ := Finset.le_sup' _ (Finset.mem_univ (0 : Fin 6))

theorem savedRow_oldResidual_upper : oldResidualUpper savedRow.lower savedRow.upper ≤
    (1 / 4 : ℝ) := by
  unfold oldResidualUpper
  apply Finset.sup'_le
  intro j _hj
  fin_cases j <;>
    norm_num [savedRow, ProducerRow.lower, ProducerRow.upper, oldPiece, oldMask,
      tentPlane, sumAffine, Affine.sub, Affine.upper, Affine.neg, Affine.lower,
      Fin.sum_univ_succ]

theorem savedRow_newResidual_upper :
    newResidualUpper savedRow.selected savedRow.lower savedRow.upper ≤ (1 / 4 : ℝ) := by
  unfold newResidualUpper
  apply max_le savedRow_oldResidual_upper
  norm_num [savedRow_selected, savedRow, ProducerRow.lower, ProducerRow.upper,
    tentPlane, sumAffine, Affine.sub, Affine.upper, Affine.neg, Affine.lower,
    Fin.sum_univ_succ]

/-- A concrete saved original producer row, with no geometry hypothesis. -/
theorem savedRow_geometry : savedRow.Geometry := by
  refine ⟨by norm_num [savedRow], by norm_num [savedRow], ?_, ?_,
    by norm_num [savedRow, ProducerRow.lower], by norm_num [savedRow, ProducerRow.upper],
    (by norm_num : (0 : ℝ) < 1 / 3200).trans_le savedRow_gap_lower,
    (by norm_num : (0 : ℝ) < 1 / 25).trans_le savedRow_oldCube_lower, ?_,
    (by norm_num : (0 : ℝ) < 1 / 10).trans_le savedRow_oldResidual_lower, ?_⟩
  · intro i
    fin_cases i <;> norm_num [savedRow]
  · intro i
    fin_cases i <;> norm_num [savedRow]
  · exact ⟨fun side => (by norm_num : (0 : ℝ) < 9 / 100).trans_le
        (savedRow_gate_margins.1 side),
      fun side j => (by norm_num : (0 : ℝ) < 9 / 100).trans_le
        (savedRow_gate_margins.2.1 side j),
      fun side j hj => (by norm_num : (0 : ℝ) < 9 / 100).trans_le
        (savedRow_gate_margins.2.2 side j hj)⟩
  · exact savedRow_newResidual_upper.trans_lt
      (by norm_num [savedRow, ProducerRow.lower])

theorem savedRow_literal_endpoint (t : Point) :
    savedRow.candidate t = v (t 0 + t 3) ∧
      ∀ e : ℝ, savedRow.bufferedCandidate e t = v (t 0 + t 3) - 2 * e := by
  constructor
  · rw [ProducerRow.candidate_eq, savedRow_selected]
    simp
  · intro e
    rw [ProducerRow.bufferedCandidate_eq, savedRow_selected]
    simp

private theorem gate_margin_pointwise (g : Affine) (t : Point) (ht : t ∈ savedRow.box)
    (h : ∀ side, (9 / 100 : ℝ) ≤
      (((tentPlane savedRow.selected side).sub g).lower savedRow.lower savedRow.upper : ℝ)) :
    g.eval t + 9 / 100 ≤ savedRow.candidate t := by
  have h0 := ((tentPlane savedRow.selected false).sub g).lower_le_eval
    savedRow.lower savedRow.upper t ht.1 ht.2
  have h1 := ((tentPlane savedRow.selected true).sub g).lower_le_eval
    savedRow.lower savedRow.upper t ht.1 ht.2
  rw [Affine.eval_sub] at h0 h1
  change _ ≤ min ((tentPlane savedRow.selected false).eval t)
    ((tentPlane savedRow.selected true).eval t)
  exact le_min (by linarith [h false]) (by linarith [h true])

/-- The historical source does not store a numerical epsilon. The literal
symbolic loss 2e is retained, with an explicit original small-e range. -/
theorem savedRow_buffered_square_license (e : ℝ) (he : e < 3 / 25600)
    (t : Point) (ht : t ∈ savedRow.box) :
    (1 / 2 : ℝ) < savedRow.bufferedCandidate e t ∧
      (∀ j, prefixSquareExpr t j < savedRow.bufferedCandidate e t) ∧
      (∀ j ∉ savedRow.selected,
        selectedSquareExpr savedRow.selected t j < savedRow.bufferedCandidate e t) := by
  have hbuf : 2 * e < (9 / 100 : ℝ) := by linarith
  have hhalf := gate_margin_pointwise halfGate t ht savedRow_gate_margins.1
  rw [halfGate_eval] at hhalf
  refine ⟨?_, ?_, ?_⟩
  · unfold ProducerRow.bufferedCandidate
    linarith
  · intro j
    have hgate := gate_margin_pointwise (fullGate j) t ht
      (fun side => savedRow_gate_margins.2.1 side j)
    rw [fullGate_eval] at hgate
    unfold ProducerRow.bufferedCandidate
    linarith
  · intro j hj
    have hgate := gate_margin_pointwise (selectedGate savedRow.selected j) t ht
      (fun side => savedRow_gate_margins.2.2 side j hj)
    rw [selectedGate_eval] at hgate
    unfold ProducerRow.bufferedCandidate
    linarith

/-- The exact saved row is licensed above the ACTUAL original coarse
third exponent, with the original 2e loss still present. -/
theorem savedRow_buffered_original_endpoint_license
    (e : ℚ) (he : 0 ≤ e) (hesmall : (e : ℝ) < 3 / 25600)
    (m : ℕ) (j : P1OriginalCoarseContinuation.FourthCell m)
    (t : Point) (ht : t ∈ savedRow.box)
    (hbox : (HistoricalThirdCoarse.box m
      (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox (t 0) (t 1) (t 2)) :
    (P1OriginalCoarseContinuation.thirdCellExponent e m j : ℝ) <
        savedRow.bufferedCandidate (e : ℝ) t ∧
      (1 / 2 : ℝ) < savedRow.bufferedCandidate (e : ℝ) t ∧
      (∀ k, prefixSquareExpr t k < savedRow.bufferedCandidate (e : ℝ) t) ∧
      (∀ k ∉ savedRow.selected,
        selectedSquareExpr savedRow.selected t k < savedRow.bufferedCandidate (e : ℝ) t) := by
  have hold := original_third_exponent_le_oldCap e he m j t hbox
    (savedRow.ordered savedRow_geometry t ht).1
  have hgap := savedRow_gap_lower.trans
    (gapLower_le_actual_gap savedRow.selected savedRow.lower savedRow.upper t ht.1 ht.2)
  have hbuf : 2 * (e : ℝ) < (1 / 3200 : ℝ) := by linarith
  have hlic := savedRow_buffered_square_license (e : ℝ) hesmall t ht
  refine ⟨?_, hlic⟩
  unfold ProducerRow.bufferedCandidate
  change _ < savedRow.candidate t - 2 * (e : ℝ)
  linarith

def savedRows : Finset ProducerRow := {savedRow}
def savedLicensed (r : ProducerRow) : Prop := r = savedRow

/-- Concrete row membership in the actual original variable maximum.
The inherited floor remains its literal firstStop/raw-Q3 ancestor. -/
theorem savedRow_le_actual_fourth_exponent
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ)
    (hlen : history.length = 4)
    (ht : primeHistoryLogCoordinates N 4 history ∈ savedRow.box) :
    savedRow.bufferedCandidate e (primeHistoryLogCoordinates N 4 history) ≤
      P1OriginalVariableFourthContinuation.exponent4 e chi m omega N savedRows
        (P1OriginalVariableFourthContinuation.producerEligible savedLicensed)
        (fun r => r.bufferedCandidate e) history := by
  rw [P1OriginalVariableFourthContinuation.exponent4, if_pos hlen]
  apply P1OriginalVariableFourthContinuation.profile4_row_le
  · simp [savedRows]
  · exact ⟨rfl, ht⟩

/-- Binding to the literal original rough-activated raw-Q3 ancestor of
an actual history. The coarse and whole-cell rough tests stay explicit. -/
theorem savedRow_actual_rawQ3_lt_buffered_level
    (e : ℚ) (he : 0 ≤ e) (hesmall : (e : ℝ) < 3 / 25600)
    (chi : ℝ) (m : ℕ) (omega N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 4)
    (hpos : ∀ p ∈ history, 0 < p)
    (j : P1OriginalCoarseContinuation.FourthCell m)
    (hcoarse : historicalPrefixProject (by omega : 3 ≤ 4) j ∈
      HistoricalThirdCoarse.cells (e : ℝ) chi m)
    (hrough : omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
      (historicalPrefixProject (by omega : 3 ≤ 4) j) 2 : ℝ))
    (htmesh : primeHistoryLogCoordinates N 4 history ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (htrow : primeHistoryLogCoordinates N 4 history ∈ savedRow.box) :
    HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega N (rosserAncestor 3 history) <
      N ^ savedRow.bufferedCandidate (e : ℝ) (primeHistoryLogCoordinates N 4 history) := by
  have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) htmesh
  have hbox : (HistoricalThirdCoarse.box m
      (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox
      (primeHistoryLogCoordinates N 4 history 0)
      (primeHistoryLogCoordinates N 4 history 1)
      (primeHistoryLogCoordinates N 4 history 2) := by
    simpa only [historicalPrefixProject] using HistoricalThirdCoarse.inBox_of_cell ht3
  have hlic := savedRow_buffered_original_endpoint_license e he hesmall m j
    (primeHistoryLogCoordinates N 4 history) htrow hbox
  rw [P1OriginalCoarseContinuation.rawLevel_eq_rpow_effectiveExponent3Q,
    P1OriginalCoarseContinuation.effectiveExponent3Q_ancestor_on_wholeActive_cell
      e chi m omega N history hN hlen hpos j hcoarse hrough htmesh]
  exact (Real.rpow_lt_rpow_left_iff hN).mpr hlic.1

theorem savedRows_keep_original_firstStop
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (positive : Bool)
    (history : List ℕ) (hlen : history.length ≤ 4) :
    P1OriginalVariableFourthContinuation.producerPolicy4 e chi m omega N
        savedRows savedLicensed positive history =
      HistoricalThirdCoarse.policy e chi m omega N positive history := by
  exact P1OriginalVariableFourthContinuation.policy4_through_four e chi m omega N
    savedRows (P1OriginalVariableFourthContinuation.producerEligible savedLicensed)
    (fun r => r.bufferedCandidate e) positive history hlen

end
end ImbalancedChen.P1HistoricalFourthMask9Row
