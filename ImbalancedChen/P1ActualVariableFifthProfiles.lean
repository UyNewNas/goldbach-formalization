import ImbalancedChen.P1ActualVariableFourthFifthCellTestLimit
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import ImbalancedChen.P1VariableOwnCubeResidualUniformity

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual VARIABLE fifth finite maximum on the original T3 firstStop/raw-Q3
carrier. Every fifth row with this exact owner and a true gateCheck enters
the maximum over the ACTUAL original variable-fourth floor. No stored cap,
all15 surrogate, requested mean, or chosen winner is used.
-/

namespace ImbalancedChen.P1ActualVariableFifthProfiles

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface P1OriginalVariableFourthContinuation
open P1CorrectedFifthDensityDictionary P1CorrectedFifthCausalTupleDictionary
open P1OriginalVariableFifthContinuation

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

def ownerEligible (e : ℚ) (m : ℕ) (j : Label5 m) (r : FifthRow m) : Prop :=
  r.cell = j ∧ gateCheck e m r = true

def actualNext5 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (t : Point5) : ℝ :=
  finiteMax rows5 (ownerEligible e m j) (fun r => candidate (e : ℝ) r.selected t)
    (originalVariableFourthProfile e chi omega m j rows4 licensed4 t)

theorem old4_le_actualNext5 (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (t : Point5) :
    originalVariableFourthProfile e chi omega m j rows4 licensed4 t ≤
      actualNext5 e chi m omega j rows4 licensed4 rows5 t := finiteMax_seed_le _ _ _ _

theorem eligible_iff_ownerEligible (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (t : Point5) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) (r : FifthRow m) :
    eligible e chi m omega J5 r t ↔ ownerEligible e m j r := by
  constructor
  · intro hr
    exact ⟨logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hr.2.2 ht,
      hr.2.1⟩
  · rintro ⟨hcell, hgate⟩
    exact ⟨hcell.symm ▸ hj, hgate, hcell.symm ▸ ht⟩

/-- The same old ancestor dictionary, with a mesh parameter only. -/
theorem old4_exponent_on_fifth_cell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : Label5 m) (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    exponent4 (e : ℝ) chi m omega (N : ℝ) rows4 (producerEligible licensed4)
        (fun r => r.bufferedCandidate (e : ℝ)) (rosserAncestor 4 (tupleHistory p)) =
      originalVariableFourthProfile e chi omega m j rows4 licensed4 (actualPrimeTupleLog N p) := by
  have hancestor : rosserAncestor 3 (tupleHistory p) =
      HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdHistory p := by
    simp [tupleHistory, List.ofFn_succ, rosserAncestor,
      HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdHistory]
  have hraw := HistoricalThirdCoarse.P1OriginalCoarseFifth.rawLevel_on_fifth_cell
    (e : ℝ) chi m omega N hN p hp j ht
  rw [P1CoarseFirstCubeFallbackMargin.rawLevel_eq_rpow_effectiveExponent] at hraw
  have hpow : (N : ℝ) ^ seedExponent (e : ℝ) chi m omega (N : ℝ) (tupleHistory p) =
      (N : ℝ) ^ HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
        (e : ℝ) chi m omega j (actualPrimeTupleLog N p) := by
    simpa only [seedExponent, hancestor] using hraw
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hseed := le_antisymm ((Real.rpow_le_rpow_left_iff hNr).mp hpow.le)
    ((Real.rpow_le_rpow_left_iff hNr).mp hpow.ge)
  have hlen : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have hlen4 : (rosserAncestor 4 (tupleHistory p)).length = 4 := by
    rw [rosserAncestor_length, hlen]
    norm_num
  have hcoords := primeHistoryLogCoordinates_eq_historicalPrefixProject
    (N : ℝ) (by omega : 4 ≤ 5) hlen
  rw [tupleHistory_log] at hcoords
  rw [exponent4, if_pos hlen4, seedExponent_ancestor_four, hseed, hcoords]
  rfl

/-- Every eligible actual fifth row has exactly this owner. The inherited
fourth floor is identified before its finite fifth maximum is taken. -/
theorem exponent5_on_selected_owner
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    exponent5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 (tupleHistory p) =
      actualNext5 e chi m omega j rows4 licensed4 rows5 (actualPrimeTupleLog N p) := by
  have hpred : (fun r => eligible e chi m omega J5 r (actualPrimeTupleLog N p)) =
      ownerEligible e m j := by
    funext r
    exact propext (eligible_iff_ownerEligible e chi m omega J5 j hj _ ht r)
  unfold exponent5 inherited4
  rw [if_pos (show (tupleHistory p).length = 5 by simp [tupleHistory]), tupleHistory_log,
    old4_exponent_on_fifth_cell e chi m omega rows4 licensed4 N hN p hp j ht, hpred]
  rfl

def lowerLevel (e : ℚ) (chi : ℝ) (m : ℕ) (j : Label5 m) : ℝ :=
  min (HistoricalThirdCoarse.initial (e : ℝ))
    (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdCellExponent (e : ℝ) chi m j)

def upperLevel (e : ℚ) (chi : ℝ) (m : ℕ) (j : Label5 m) : ℝ :=
  max (max (HistoricalThirdCoarse.initial (e : ℝ))
    (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdCellExponent (e : ℝ) chi m j))
      (VariableEnvelope.cap - 2 * (e : ℝ))

theorem actualOld4_mem_interval
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) (t : Point5) :
    originalVariableFourthProfile e chi omega m j rows4 licensed4 t ∈
      Icc (lowerLevel e chi m j) (upperLevel e chi m j) := by
  let seed := HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent (e : ℝ) chi m omega j t
  have hseedlo : lowerLevel e chi m j ≤ seed := by
    dsimp [lowerLevel, seed, HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent]
    split_ifs
    · exact min_le_right _ _
    · exact min_le_left _ _
  have hseedhi : seed ≤ upperLevel e chi m j := by
    dsimp [upperLevel, seed, HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent]
    split_ifs
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_left _ _)
  constructor
  · exact hseedlo.trans (profile4_seed_le seed rows4 (producerEligible licensed4)
      (fun r => r.bufferedCandidate (e : ℝ)) _)
  · change finiteMax rows4 (fun r => producerEligible licensed4 r
      (historicalPrefixProject (by omega : 4 ≤ 5) t))
      (fun r => r.bufferedCandidate (e : ℝ)
        (historicalPrefixProject (by omega : 4 ≤ 5) t)) seed ≤ upperLevel e chi m j
    apply finiteMax_le _ _ _ _ _ hseedhi
    intro r _hr _he
    rw [r.bufferedCandidate_eq]
    exact (sub_le_sub_right (v_le_cap _) _).trans (le_max_right _ _)

theorem actualNext5_mem_interval
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (rows5 : Finset (FifthRow m)) (t : Point5) :
    actualNext5 e chi m omega j rows4 licensed4 rows5 t ∈
      Icc (lowerLevel e chi m j) (upperLevel e chi m j) := by
  have hold := actualOld4_mem_interval e chi m omega j rows4 licensed4 t
  constructor
  · exact hold.1.trans (old4_le_actualNext5 e chi m omega j rows4 licensed4 rows5 t)
  · apply finiteMax_le _ _ _ _ _ hold.2
    intro r _hr _he
    rw [candidate, envelope_eq_v]
    exact (sub_le_sub_right (v_le_cap _) _).trans (le_max_right _ _)

def literalTupleCharge (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  literalTupleDifference (originalQ4 e chi m omega N rows4 licensed4)
    (level5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) N cap p

theorem actualSaving_normalized_eq_literalTupleSum
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (N cap : ℕ) (z : ℝ) :
    actualFifthSaving e chi m omega rows4 licensed4 J5 rows5 N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitFrontierTuples 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 z), (∏ i, 1 / ((p i : ℝ) - 1)) *
          literalTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap p := by
  exact actualHistoricalFifthSaving_eq_literalTupleSum
    (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
    (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
    (level5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) N cap z

theorem literalTupleCharge_on_selected_owner
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    literalTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap p =
      actualPrimeTupleOwnCubeMinus N cap
        (actualNext5 e chi m omega j rows4 licensed4 rows5 (actualPrimeTupleLog N p)) p -
      actualPrimeTupleOwnCubeMinus N cap
        (originalVariableFourthProfile e chi omega m j rows4 licensed4 (actualPrimeTupleLog N p)) p := by
  have hlen : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have hnew := actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap
    (actualNext5 e chi m omega j rows4 licensed4 rows5 (actualPrimeTupleLog N p)) (k := 4) hlen
  have hold := actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap
    (originalVariableFourthProfile e chi omega m j rows4 licensed4 (actualPrimeTupleLog N p)) (k := 4) hlen
  rw [primeHistoryTuple_tupleHistory] at hnew hold
  have hnewLevel : level5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 (tupleHistory p) =
      (N : ℝ) ^ actualNext5 e chi m omega j rows4 licensed4 rows5 (actualPrimeTupleLog N p) :=
    congrArg (fun x : ℝ => (N : ℝ) ^ x)
      (exponent5_on_selected_owner e chi m omega rows4 licensed4 J5 rows5 N hN p hp j hj ht)
  have holdLevel : originalQ4 e chi m omega N rows4 licensed4 (rosserAncestor 4 (tupleHistory p)) =
      (N : ℝ) ^ originalVariableFourthProfile e chi omega m j rows4 licensed4 (actualPrimeTupleLog N p) :=
    congrArg (fun x : ℝ => (N : ℝ) ^ x)
      (old4_exponent_on_fifth_cell e chi m omega rows4 licensed4 N hN p hp j ht)
  rw [hnew, hold]
  simp only [literalTupleCharge, literalTupleDifference, actualOwnCubeGatedMinusDensity,
    hnewLevel, holdLevel]
  ring

theorem literalTupleCharge_outside
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (N cap : ℕ) (p : Fin 5 → ℕ)
    (hout : ∀ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
      actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) m j) :
    literalTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap p = 0 := by
  have hno : ∀ r ∈ rows5, ¬ eligible e chi m omega J5 r
      (primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p)) := by
    intro r _hr he
    exact hout r.cell he.1 (by simpa only [tupleHistory_log] using he.2.2)
  have hlevel : level5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 (tupleHistory p) =
      originalQ4 e chi m omega N rows4 licensed4 (rosserAncestor 4 (tupleHistory p)) := by
    rw [level5, exponent5_outside e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 _ hno]
    rfl
  simp only [literalTupleCharge, literalTupleDifference, actualOwnCubeGatedMinusDensity, hlevel,
    sub_self, zero_mul, zero_div]

def positiveCellCharge (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (a : ℝ)
    (N cap : ℕ) (j : Label5 m) : ℝ :=
  ∑ p ∈ (firstExitFrontierTuples 4 (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
      (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
    (∏ i, 1 / ((p i : ℝ) - 1)) * (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
      then literalTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap p else 0)

theorem positiveCellCharge_eq_residualSums
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5) :
    positiveCellCharge e chi m omega rows4 licensed4 J5 rows5 a N cap j =
      P1VariableOwnCubeResidualUniformity.actualPrimeBoxVariableOwnCubeMinusSum
        4 N cap a (19 / 96) (actualNext5 e chi m omega j rows4 licensed4 rows5)
        (P1OriginalFifthLimit.sourceRegion e chi m omega j) -
      P1VariableOwnCubeResidualUniformity.actualPrimeBoxVariableOwnCubeMinusSum
        4 N cap a (19 / 96) (originalVariableFourthProfile e chi omega m j rows4 licensed4)
        (P1OriginalFifthLimit.sourceRegion e chi m omega j) := by
  unfold positiveCellCharge
  rw [P1OriginalFifthLimit.positive_candidates_weighted_sum e chi m omega a N cap hN hcap j]
  unfold P1VariableOwnCubeResidualUniformity.actualPrimeBoxVariableOwnCubeMinusSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ P1OriginalFifthLimit.sourceRegion e chi m omega j
  · simp only [if_pos ht]
    rw [literalTupleCharge_on_selected_owner e chi m omega rows4 licensed4 J5 rows5
      N cap hN p (fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos) j hj ht.1]
    ring
  · simp only [if_neg ht, mul_zero, sub_self]

end
end ImbalancedChen.P1ActualVariableFifthProfiles
