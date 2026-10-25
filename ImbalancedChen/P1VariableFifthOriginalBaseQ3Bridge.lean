import ImbalancedChen.P1VariableFifthSelectedStoredBinding

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The base and Q3 equalities proposed for a generic historical stored-cap
table are not consequences of that table.  The original base includes the
first-label `firstStop`; the ordinary base does not.  The original Q3 uses
the rough-activated Gamma lookup and returns Theta-2e when inactive;
`D.level3` is a target-independent mesh lookup with no activation test.

The corrected bridge below uses the original initial policy and raw Q3
definitionally.  Its fifth level takes the real variable fourth producer
exponent on the exact fourth ancestor as fallback, and inserts the literal
stored rational fifth cap only on selected fifth cells.  The half-open
lookup and original rank-four first-stop carrier are preserved.  This does
not identify the corrected first-exit density with the old generic D ledger.
-/

namespace ImbalancedChen.P1VariableFifthOriginalBaseQ3Bridge

noncomputable section
open scoped Classical BigOperators

/-- Rank one exposes the exact extra first-label stop in the original base. -/
theorem ordinary_base_rank_one (e : ℝ) (N : ℝ) (p : ℕ) :
    ordinaryParityRosserPolicy false (N ^ HistoricalThirdCoarse.initial e) false [p] =
      decide (ordinaryRosserPrefixAdmissible false (N ^ HistoricalThirdCoarse.initial e) [p]) := by
  simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]

theorem original_base_rank_one (e : ℝ) (m : ℕ) (N : ℝ) (p : ℕ) :
    HistoricalThirdCoarse.initialPolicy e m N false [p] =
      decide (ordinaryRosserPrefixAdmissible false (N ^ HistoricalThirdCoarse.initial e) [p] ∧
        HistoricalThirdCoarse.firstStop e m N [p]) := by
  simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]

/-- If an ordinary singleton passes but its original first label is not
stopped, the base policies differ even when their numeric level agrees. -/
theorem base_mismatch_of_missing_firstStop
    (e : ℝ) (m : ℕ) (N : ℝ) (p : ℕ)
    (hordinary : ordinaryRosserPrefixAdmissible false (N ^ HistoricalThirdCoarse.initial e) [p])
    (hstop : ¬ HistoricalThirdCoarse.firstStop e m N [p]) :
    ordinaryParityRosserPolicy false (N ^ HistoricalThirdCoarse.initial e) ≠
      HistoricalThirdCoarse.initialPolicy e m N := by
  intro heq
  have hp := congrFun (congrFun heq false) [p]
  rw [ordinary_base_rank_one e N p, original_base_rank_one e m N p] at hp
  simp [hordinary, hstop] at hp

/-- On the one-cell mesh, a positive buffer excludes the entire first
label: its upper endpoint is exactly 19/96, above the buffered stop. -/
theorem no_firstStop_on_zero_mesh (e : ℝ) (he : 0 < e)
    (N : ℝ) (p : ℕ) :
    ¬ HistoricalThirdCoarse.firstStop e 0 N [p] := by
  rintro ⟨i, _hlo, _hhi, hbound⟩
  have hi : i = 0 := Fin.eq_zero i
  subst i
  norm_num [logPrimeMeshPoint, logPrimeMeshStep,
    VariableEnvelope.extendedFirstStop] at hbound
  linarith

theorem base_mismatch_on_zero_mesh
    (e : ℝ) (he : 0 < e) (N : ℝ) (p : ℕ)
    (hordinary : ordinaryRosserPrefixAdmissible false
      (N ^ HistoricalThirdCoarse.initial e) [p]) :
    ordinaryParityRosserPolicy false (N ^ HistoricalThirdCoarse.initial e) ≠
      HistoricalThirdCoarse.initialPolicy e 0 N := by
  exact base_mismatch_of_missing_firstStop e 0 N p hordinary
    (no_firstStop_on_zero_mesh e he N p)

/-- Thus setting `D.old` to the exact original Theta fallback still does
not discharge the generic stored table's required base identity. -/
theorem stored_base_mismatch_of_missing_firstStop
    (D : HistoricalPrefixCapData) (e : ℝ) (N : ℝ) (p : ℕ)
    (hold : (D.old : ℝ) = HistoricalThirdCoarse.initial e)
    (hordinary : ordinaryRosserPrefixAdmissible false (N ^ HistoricalThirdCoarse.initial e) [p])
    (hstop : ¬ HistoricalThirdCoarse.firstStop e D.m N [p]) :
    ordinaryParityRosserPolicy false (N ^ (D.old : ℝ)) ≠
      HistoricalThirdCoarse.initialPolicy e D.m N := by
  rw [hold]
  exact base_mismatch_of_missing_firstStop e D.m N p hordinary hstop

/-- An inactive history is outside the original rough support.  A stored
third cell can nevertheless be selected there because D's lookup has no
rough test.  This is the second exact obstruction, before exponentiation. -/
theorem third_exponent_mismatch_on_inactive_stored_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (e chi : ℝ) (omega N : ℝ) (history : List ℕ)
    (hinactive : ¬ HistoricalThirdCoarse.active omega N history)
    (j : Fin 3 → Fin (D.m + 1)) (hj : j ∈ D.cells3)
    (ht : primeHistoryLogCoordinates N 3 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (hne : (D.cap3 j : ℝ) ≠ HistoricalThirdCoarse.initial e) :
    (D.exponent3 (primeHistoryLogCoordinates N 3 history) : ℝ) ≠
      P1CoarseFirstCubeFallbackMargin.effectiveExponent e chi D.m omega N history := by
  have hD := D.exponent3_on_cell hab _ j ht
  simp only [HistoricalPrefixCapData.cell3, if_pos hj] at hD
  have hs : ¬ P1ThirdFallbackSupport.supported e chi D.m omega N history := by
    intro hs
    exact hinactive hs.1
  simp only [P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_neg hs]
  rw [hD]
  exact hne

abbrev Label5 (D : HistoricalPrefixCapData) := Fin 5 → Fin (D.m + 1)

/-- Corrected fifth exponent: the stored selected cap is a real-valued
lookup on top of the original variable fourth exponent, not `D.level4`.
Unselected cells, outside points and non-fifth histories retain that exact
fourth ancestor, including its original raw-Q3 fallback. -/
def correctedStoredExponent5
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (pre : List ℕ) : ℝ :=
  let inherited := P1OriginalVariableFourthContinuation.exponent4 (e : ℝ) chi D.m omega N
    rows4 (P1OriginalVariableFourthContinuation.producerEligible licensed4)
    (fun r => r.bufferedCandidate (e : ℝ)) (rosserAncestor 4 pre)
  if pre.length = 5 then
    HistoricalThirdCoarse.P1OriginalFifthCells.fifthLookup D.m (D.cells5 ∩ J)
      (fun j => (D.cap5 j : ℝ)) inherited
      (primeHistoryLogCoordinates N 5 pre)
  else inherited

def correctedStoredLevel5
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (pre : List ℕ) : ℝ :=
  N ^ correctedStoredExponent5 D J e chi omega N rows4 licensed4 pre

/-- The corrected policy has the exact original firstStop and rough Q3,
before any fifth stored cap is inspected. -/
def correctedStoredPolicy5
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop) :
    Bool → List ℕ → Bool :=
  fifthCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) D.m N)
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi D.m omega N)
    (correctedStoredLevel5 D J e chi omega N rows4 licensed4)

theorem corrected_parent_is_exact_original_T3
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ) :
    thirdCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) m N)
      (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega N) =
        HistoricalThirdCoarse.policy (e : ℝ) chi m omega N := rfl

theorem corrected_stored_level_on_selected_cell
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (pre : List ℕ) (hlen : pre.length = 5)
    (j : Label5 D) (hj : j ∈ D.cells5 ∩ J)
    (ht : primeHistoryLogCoordinates N 5 pre ∈
      logPrimeMeshCell 0 (19 / 96) D.m j) :
    correctedStoredExponent5 D J e chi omega N rows4 licensed4 pre =
      (D.cap5 j : ℝ) := by
  unfold correctedStoredExponent5
  rw [if_pos hlen]
  exact HistoricalThirdCoarse.P1OriginalFifthCells.fifthLookup_on_cell D.m (D.cells5 ∩ J)
    (fun j => (D.cap5 j : ℝ)) _ _ j hj ht

theorem corrected_stored_exponent_outside
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (pre : List ℕ)
    (hout : ∀ j ∈ D.cells5 ∩ J,
      primeHistoryLogCoordinates N 5 pre ∉
        logPrimeMeshCell 0 (19 / 96) D.m j) :
    correctedStoredExponent5 D J e chi omega N rows4 licensed4 pre =
      P1OriginalVariableFourthContinuation.exponent4 (e : ℝ) chi D.m omega N
        rows4 (P1OriginalVariableFourthContinuation.producerEligible licensed4)
        (fun r => r.bufferedCandidate (e : ℝ))
        (rosserAncestor 4 pre) := by
  unfold correctedStoredExponent5
  split_ifs
  · exact HistoricalThirdCoarse.P1OriginalFifthCells.fifthLookup_outside D.m (D.cells5 ∩ J)
      (fun j => (D.cap5 j : ℝ)) _ _ hout
  · rfl

theorem corrected_stored_through_four
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    correctedStoredPolicy5 D J e chi omega N rows4 licensed4 positive pre =
      HistoricalThirdCoarse.policy (e : ℝ) chi D.m omega N positive pre := by
  simp only [correctedStoredPolicy5, fifthCappedUpperPolicy,
    firstExitDepthSplicePolicy, if_pos hlen, HistoricalThirdCoarse.policy]

theorem corrected_and_variable_same_firstStop_carrier
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.m))
    (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4
        (correctedStoredPolicy5 D J e chi omega N rows4 licensed4)
        h pre positive mass carrier =
      firstExitDepthFrontier 4
        (P1OriginalVariableFifthContinuation.policy5 e chi D.m omega N rows4 licensed4 (D.cells5 ∩ J) rows5)
        h pre positive mass carrier := by
  calc
    _ = firstExitDepthFrontier 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi D.m omega N)
        h pre positive mass carrier := by
          exact fifthCappedUpperPolicy_frontier_four
            (HistoricalThirdCoarse.initialPolicy (e : ℝ) D.m N)
            (HistoricalThirdCoarse.rawLevel (e : ℝ) chi D.m omega N)
            (correctedStoredLevel5 D J e chi omega N rows4 licensed4)
            h pre carrier positive mass
    _ = _ := by
      exact (fifthCappedUpperPolicy_frontier_four
        (HistoricalThirdCoarse.initialPolicy (e : ℝ) D.m N)
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi D.m omega N)
        (P1OriginalVariableFifthContinuation.level5 e chi D.m omega N rows4 licensed4 (D.cells5 ∩ J) rows5)
        h pre carrier positive mass).symm

/-- With the explicit finite original-row and buffer checks, the literal
stored selected cap is bounded by the continuous variable fifth maximum.
Both sides now run on the SAME original T3 and target-deleted first-stop
carrier.  This is local to an owned selected fifth cell; no gross saving or
integral bound is inferred. -/
theorem corrected_stored_le_variable_on_selected_cell
    (D : HistoricalPrefixCapData) (J : Finset (Label5 D))
    (I : Label5 D → Finset (Fin 5)) (nu : Label5 D → ℚ)
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hpermit : P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.storedFifthPermit D J I nu)
    (hbuffer : P1VariableFifthSelectedStoredBinding.BufferedStoredRows D J I e)
    (hN : 1 ≤ N) (pre : List ℕ) (hlen : pre.length = 5)
    (j : Label5 D) (hj : j ∈ D.cells5 ∩ J)
    (ht : primeHistoryLogCoordinates N 5 pre ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    correctedStoredExponent5 D J e chi omega N rows4 licensed4 pre ≤
      P1OriginalVariableFifthContinuation.exponent5 e chi D.m omega N rows4 licensed4
        (D.cells5 ∩ J) (P1VariableFifthSelectedStoredBinding.rows D J I) pre := by
  have ht0 : primeHistoryLogCoordinates N 5 pre ∈
      logPrimeMeshCell 0 (19 / 96) D.m j := by
    simpa only [howned.1, howned.2.1, Rat.cast_zero, Rat.cast_div,
      Rat.cast_ofNat] using ht
  have hcompare := P1VariableFifthSelectedStoredBinding.stored_cap_le_variable_fifth_exponent
    D J I nu e chi omega N rows4 licensed4 howned hpermit hbuffer hN
    pre hlen j hj (primeHistoryLogCoordinates N 5 pre) rfl ht
  rw [corrected_stored_level_on_selected_cell D J e chi omega N
    rows4 licensed4 pre hlen j hj ht0]
  simpa only [P4AOriginalHistoricalFifthSelectedSlotBridgeSourceOnly.stored_cap_unchanged]
    using hcompare.2.1

end
end ImbalancedChen.P1VariableFifthOriginalBaseQ3Bridge
