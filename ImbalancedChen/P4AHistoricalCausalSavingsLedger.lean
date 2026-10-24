import ImbalancedChen.ActualHistoricalFifthSavingIntegral

/-!
# P4A: a finite causal ledger with disjoint fifth admission pieces

All quantities below are actual finite densities on one target-deleted
carrier.  The fourth and fifth policies share their third-capped parent.
The finite rational level check derives both order premises; it is not a
density, positivity, integral-value, or distribution assumption.

The fifth entry has the sign `new gated lower residual - old gated lower
residual`.  Its two pieces have disjoint arithmetic admission supports.
The endpoint identity subtracts this entry exactly once, after subtracting
the fourth entry.  No sign assertion for a finite lower Rosser density is
made: the word saving describes the direction of the identity.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

namespace HistoricalPrefixCapData

/-- Actual normalized density, using exactly the same finite prime carrier
for every policy in the ledger. -/
def p4aPolicyDensity (D : HistoricalPrefixCapData)
    (policy : Bool → List ℕ → Bool) (N cap : ℕ) (z : ℝ) : ℝ :=
  firstExitRetainedPolynomial policy (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap 0 z) * Real.log (N : ℝ) / singularSeries N

/-- The literal fourth entry, with the inherited third level retained. -/
def p4aFourthEntry (D : HistoricalPrefixCapData) (N cap : ℕ) (z : ℝ) : ℝ :=
  actualHistoricalFourthSaving
    (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
    (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z *
      Real.log (N : ℝ) / singularSeries N

/-- The finite checker and the actual frontier length supply admissibility
through the existing third-capped frontier theorem. -/
theorem p4a_third_sub_fourth_eq (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    D.p4aPolicyDensity (D.upperThirdPolicy (N : ℝ)) N cap z -
      D.p4aPolicyDensity (D.upperFourthPolicy (N : ℝ)) N cap z =
        D.p4aFourthEntry N cap z := by
  have hraw := actualHistoricalFourthSaving_eq
    (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
    (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z (by
      intro state hstate
      apply D.level3_ancestor_le_level4 hab hcheck (N : ℝ) hN
      exact firstExitDepthFrontier_selected_length 4 _ _ [] _ true 1
        (by simp) state hstate)
  dsimp [p4aPolicyDensity, p4aFourthEntry]
  rw [← hraw]
  ring

/-- The normalized final upper density has one fourth charge and one fifth
charge.  Both charges use the actual common third-capped parent. -/
theorem p4a_fifth_density_eq_causal_ledger (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    D.p4aPolicyDensity (D.upperFifthPolicy (N : ℝ)) N cap
        ((N : ℝ) ^ (D.b : ℝ)) =
      D.p4aPolicyDensity (D.upperThirdPolicy (N : ℝ)) N cap
          ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aFourthEntry N cap ((N : ℝ) ^ (D.b : ℝ)) -
          D.fifthPrimeCorrection N cap := by
  have h34 := D.p4a_third_sub_fourth_eq hab hcheck N cap hN
    ((N : ℝ) ^ (D.b : ℝ))
  have h45 := D.upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection
    hab hcheck N cap hN
  have h45' :
      D.p4aPolicyDensity (D.upperFourthPolicy (N : ℝ)) N cap
          ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aPolicyDensity (D.upperFifthPolicy (N : ℝ)) N cap
          ((N : ℝ) ^ (D.b : ℝ)) = D.fifthPrimeCorrection N cap := by
    dsimp [p4aPolicyDensity]
    rw [← h45]
    ring
  linarith

/-- Unique half-open cell ownership replaces the fifth entry by its finite
cell sum, without a second charge or a discarded boundary term. -/
theorem p4a_fifth_density_eq_causal_cell_ledger (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    D.p4aPolicyDensity (D.upperFifthPolicy (N : ℝ)) N cap
        ((N : ℝ) ^ (D.b : ℝ)) =
      D.p4aPolicyDensity (D.upperThirdPolicy (N : ℝ)) N cap
          ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aFourthEntry N cap ((N : ℝ) ^ (D.b : ℝ)) -
          ∑ j ∈ D.cells5, D.fifthCellPrimeCorrection N cap j := by
  rw [D.p4a_fifth_density_eq_causal_ledger hab hcheck N cap hN,
    D.fifthPrimeCorrection_eq_cells hab N cap]

/-- The residual before imposing its own cube.  This expression is used
only behind one of the actual strict arithmetic gates below. -/
def p4aUngatedTupleMinus (N cap : ℕ) (lambda : ℝ) (p : Fin 5 → ℕ) : ℝ :=
  actualSmallRosserMinusDensity N cap (p (Fin.last 4) : ℝ)
    ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) *
      Real.log (N : ℝ) / singularSeries N

def p4aFifthOldGate (D : HistoricalPrefixCapData) (N : ℕ) (p : Fin 5 → ℕ) : Prop :=
  (∏ i, p i : ℕ) * (p (Fin.last 4) : ℝ) ^ 2 <
    (N : ℝ) ^ (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5)
      (actualPrimeTupleLog N p)) : ℝ)

def p4aFifthNewGate (D : HistoricalPrefixCapData) (N : ℕ) (p : Fin 5 → ℕ) : Prop :=
  (∏ i, p i : ℕ) * (p (Fin.last 4) : ℝ) ^ 2 <
    (N : ℝ) ^ (D.exponent5 (actualPrimeTupleLog N p) : ℝ)

/-- The old own cube is contained in the new own cube.  This follows from
finite cap comparisons, even for tuples outside the actual parent. -/
theorem p4a_fifth_oldGate_imp_newGate (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N : ℕ) (hN : 1 < (N : ℝ)) (p : Fin 5 → ℕ)
    (hold : D.p4aFifthOldGate N p) : D.p4aFifthNewGate N p := by
  apply lt_of_lt_of_le hold
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  exact_mod_cast D.exponent4_le_exponent5 hab hcheck (actualPrimeTupleLog N p)

/-- Residual change on candidates already admitted by the old own cube. -/
def p4aFifthInheritedPiece (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  if D.p4aFifthOldGate N p then
    p4aUngatedTupleMinus N cap (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p -
      p4aUngatedTupleMinus N cap
        (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5)
          (actualPrimeTupleLog N p)) : ℝ) p
  else 0

/-- Restoration on new-only candidates.  The old residual is absent here. -/
def p4aFifthNewOnlyPiece (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  if D.p4aFifthNewGate N p ∧ ¬D.p4aFifthOldGate N p then
    p4aUngatedTupleMinus N cap (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p
  else 0

/-- No candidate can contribute to both admission pieces.  This support
statement is exact before normalization, summation, or passage to a limit. -/
theorem p4a_fifth_pieces_disjoint (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ) :
    D.p4aFifthInheritedPiece N cap p * D.p4aFifthNewOnlyPiece N cap p = 0 := by
  by_cases hold : D.p4aFifthOldGate N p <;>
    simp [p4aFifthInheritedPiece, p4aFifthNewOnlyPiece, hold]

/-- Exact disjoint admission decomposition.  A new-only candidate receives
the new residual once and no old fifth residual.  Neither piece is assumed
nonnegative, and no lower-density monotonicity is smuggled into the API. -/
theorem p4a_fifthTupleOwnCubeDifference_eq_disjoint_pieces
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ))
    (p : Fin 5 → ℕ) :
    D.fifthTupleOwnCubeDifference N cap p =
      D.p4aFifthInheritedPiece N cap p + D.p4aFifthNewOnlyPiece N cap p := by
  by_cases hold : D.p4aFifthOldGate N p
  · have hnew := D.p4a_fifth_oldGate_imp_newGate hab hcheck N hN p hold
    simp only [p4aFifthOldGate] at hold
    simp only [p4aFifthNewGate] at hnew
    simp [fifthTupleOwnCubeDifference, actualPrimeTupleOwnCubeMinus,
      p4aFifthInheritedPiece, p4aFifthNewOnlyPiece, p4aUngatedTupleMinus,
      p4aFifthOldGate, p4aFifthNewGate, hold, hnew]
  · by_cases hnew : D.p4aFifthNewGate N p <;>
      simp only [p4aFifthOldGate] at hold <;>
      simp only [p4aFifthNewGate] at hnew <;>
      simp [fifthTupleOwnCubeDifference, actualPrimeTupleOwnCubeMinus,
        p4aFifthInheritedPiece, p4aFifthNewOnlyPiece, p4aUngatedTupleMinus,
        p4aFifthOldGate, p4aFifthNewGate, hold, hnew]

/-- The literal finite tuple correction is the sum of the two disjoint
pieces over the same complete parent tuple carrier, including old rejects. -/
theorem p4a_fifthPrimeCorrection_eq_disjoint_sums
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) :
    D.fifthPrimeCorrection N cap =
      (∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
        (∏ i, 1 / ((p i : ℝ) - 1)) * D.p4aFifthInheritedPiece N cap p) +
      ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
          (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
        (∏ i, 1 / ((p i : ℝ) - 1)) * D.p4aFifthNewOnlyPiece N cap p := by
  unfold fifthPrimeCorrection
  simp_rw [D.p4a_fifthTupleOwnCubeDifference_eq_disjoint_pieces hab hcheck N cap hN,
    mul_add]
  rw [Finset.sum_add_distrib]

end HistoricalPrefixCapData

end

end ImbalancedChen
