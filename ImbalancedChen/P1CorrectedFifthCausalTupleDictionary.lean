import ImbalancedChen.P1CorrectedFifthDensityDictionary
import ImbalancedChen.ActualHistoricalFifthSavingIntegral

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Exact normalization of the literal causal fifth charge on the ORIGINAL
firstStop/raw-Q3 parent. The old exponent is identified with the pointwise
variable fourth maximum on the same actual fifth owner. Both strict
own-cube gates survive. No limit, fourth-to-fifth monotonicity, or equality
with the unrelated generic HistoricalPrefixCapData integral is assumed.

OPEN: prove the prime sum limit for the nonconstant old fourth profile on
the original joint region, including its row walls and activation split.
OPEN: prove the selected stored fifth cap dominates the actual fourth
ancestor before calling this charge a retained-density difference.
-/

namespace ImbalancedChen.P1CorrectedFifthCausalTupleDictionary

noncomputable section
open scoped Classical BigOperators
open P1CorrectedFifthDensityDictionary

def tupleHistory (p : Fin 5 → ℕ) : List ℕ := (List.ofFn p).reverse

theorem tupleHistory_primeHistoryTuple (history : List ℕ)
    (hlen : history.length = 5) :
    tupleHistory (primeHistoryTuple 5 history) = history := by
  exact primeHistoryTuple_reverse_ofFn hlen

theorem primeHistoryTuple_tupleHistory (p : Fin 5 → ℕ) :
    primeHistoryTuple 5 (tupleHistory p) = p := by
  apply List.ofFn_injective
  rw [primeHistoryTuple_ofFn (show (tupleHistory p).length = 5 by simp [tupleHistory])]
  simp only [tupleHistory, List.reverse_reverse]

theorem tupleHistory_log (N : ℕ) (p : Fin 5 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) = actualPrimeTupleLog N p := by
  rw [primeHistoryLogCoordinates_eq_actualPrimeTupleLog, primeHistoryTuple_tupleHistory]

/-- The literal normalized residual uses the actual complete history and
the actual fourth ancestor. It works for arbitrary level functions. -/
def literalTupleDifference (Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  (actualOwnCubeGatedMinusDensity N cap Q5 (tupleHistory p) -
    actualOwnCubeGatedMinusDensity N cap
      (fun history => Q4 (rosserAncestor 4 history)) (tupleHistory p)) *
    Real.log (N : ℝ) / singularSeries N

theorem literalTupleDifference_history (Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (history : List ℕ) (hlen : history.length = 5) :
    literalTupleDifference Q4 Q5 N cap (primeHistoryTuple 5 history) =
      (actualOwnCubeGatedMinusDensity N cap Q5 history -
        actualOwnCubeGatedMinusDensity N cap
          (fun pre => Q4 (rosserAncestor 4 pre)) history) *
        Real.log (N : ℝ) / singularSeries N := by
  rw [literalTupleDifference, tupleHistory_primeHistoryTuple history hlen]

/-- No candidate is filtered by either own cube. This theorem is equally
valid for the original variable maximum and the corrected stored policy. -/
theorem actualHistoricalFifthSaving_eq_literalTupleSum
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFifthSaving base Q3 Q4 Q5 N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitFrontierTuples 4 (thirdCappedUpperPolicy base Q3)
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) * literalTupleDifference Q4 Q5 N cap p := by
  let parent := thirdCappedUpperPolicy base Q3
  let h (q : ℕ) := 1 / ((q : ℝ) - 1)
  let states := firstExitDepthFrontier 4 parent h [] true 1 (roughPrimeUniverse N cap 0 z)
  let candidates (s : FirstExitDepthState ℕ) :=
    firstExitNextSelectionCandidates h s.selectedPrefix s.positive s.mass s.remaining
  let residual (history : List ℕ) :=
    actualOwnCubeGatedMinusDensity N cap Q5 history -
      actualOwnCubeGatedMinusDensity N cap
        (fun pre => Q4 (rosserAncestor 4 pre)) history
  let f := literalTupleDifference Q4 Q5 N cap
  have hn : actualHistoricalFifthSaving base Q3 Q4 Q5 N cap z *
      Real.log (N : ℝ) / singularSeries N =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum := by
    simp only [List.sum_map_mul_right]
    change _ * Real.log (N : ℝ) / singularSeries N =
      actualHistoricalFifthSaving base Q3 Q4 Q5 N cap z *
        (Real.log (N : ℝ) / singularSeries N)
    ring
  rw [hn]
  have heq : (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod *
          f (primeHistoryTuple 5 c.selectedPrefix))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    congr 1
    apply List.map_congr_left
    intro c hc
    have hlen := (actualPrimeNextSelection_geometry 4 parent N cap z s hs c hc).1
    dsimp [f]
    rw [literalTupleDifference_history Q4 Q5 N cap c.selectedPrefix hlen]
    dsimp [residual]
    ring
  rw [heq]
  exact actualPrimeFrontier_candidates_weighted_sum_eq_tuple_sum 4 parent h N cap 0 z f

section Corrected

variable (D : HistoricalPrefixCapData) (J : Finset (Label5 D.m))
  (e : ℚ) (chi omega : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)

/-- These exponents read actual prime histories, before any cell geometry
or analytic approximation is used. -/
def correctedTupleDifference (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  actualPrimeTupleOwnCubeMinus N cap
      (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredExponent5
        D J e chi omega (N : ℝ) rows4 licensed4 (tupleHistory p)) p -
    actualPrimeTupleOwnCubeMinus N cap
      (P1OriginalVariableFourthContinuation.exponent4 (e : ℝ) chi D.m omega (N : ℝ)
        rows4 (P1OriginalVariableFourthContinuation.producerEligible licensed4)
        (fun r => r.bufferedCandidate (e : ℝ)) (rosserAncestor 4 (tupleHistory p))) p

theorem correctedTupleDifference_eq_literal (N cap : ℕ) (p : Fin 5 → ℕ) :
    correctedTupleDifference D J e chi omega rows4 licensed4 N cap p =
      literalTupleDifference
        (originalQ4 e chi D.m omega N rows4 licensed4)
        (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5
          D J e chi omega (N : ℝ) rows4 licensed4) N cap p := by
  have hlen : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have hnew := actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap
    (P1VariableFifthOriginalBaseQ3Bridge.correctedStoredExponent5
      D J e chi omega (N : ℝ) rows4 licensed4 (tupleHistory p)) (k := 4) hlen
  have hold := actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap
    (P1OriginalVariableFourthContinuation.exponent4 (e : ℝ) chi D.m omega (N : ℝ)
      rows4 (P1OriginalVariableFourthContinuation.producerEligible licensed4)
      (fun r => r.bufferedCandidate (e : ℝ)) (rosserAncestor 4 (tupleHistory p)))
    (k := 4) hlen
  rw [primeHistoryTuple_tupleHistory] at hnew hold
  unfold correctedTupleDifference
  rw [hnew, hold]
  simp only [literalTupleDifference, actualOwnCubeGatedMinusDensity, originalQ4,
    P1VariableFifthOriginalBaseQ3Bridge.correctedStoredLevel5,
    P1OriginalVariableFourthContinuation.producerLevel4,
    P1OriginalVariableFourthContinuation.level4]
  ring

/-- The corrected finite charge has now been normalized and reindexed on
the exact original T3. No monotonicity or limiting premise is used. -/
theorem corrected_charge_eq_tupleSum (N cap : ℕ) (z : ℝ) :
    correctedStoredCharge D J e chi omega N cap z rows4 licensed4 *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitFrontierTuples 4 (originalT3 e chi D.m omega N)
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          correctedTupleDifference D J e chi omega rows4 licensed4 N cap p := by
  unfold correctedStoredCharge
  rw [actualHistoricalFifthSaving_eq_literalTupleSum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [correctedTupleDifference_eq_literal]

/-- The inherited third seed uses the actual original rough activation,
and its first-three history is exactly the projection of this fifth tuple. -/
theorem original_seed_on_fifth_cell
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : Label5 D.m)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j) :
    P1OriginalVariableFourthContinuation.seedExponent (e : ℝ) chi D.m omega
        (N : ℝ) (tupleHistory p) =
      HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
        (e : ℝ) chi D.m omega j (actualPrimeTupleLog N p) := by
  have hancestor : rosserAncestor 3 (tupleHistory p) =
      HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdHistory p := by
    simp [tupleHistory, List.ofFn_succ, rosserAncestor,
      HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdHistory]
  have hraw := HistoricalThirdCoarse.P1OriginalCoarseFifth.rawLevel_on_fifth_cell
    (e : ℝ) chi D.m omega N hN p hp j ht
  rw [P1CoarseFirstCubeFallbackMargin.rawLevel_eq_rpow_effectiveExponent] at hraw
  have hpow : (N : ℝ) ^
      P1OriginalVariableFourthContinuation.seedExponent (e : ℝ) chi D.m omega
        (N : ℝ) (tupleHistory p) =
      (N : ℝ) ^ HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
        (e : ℝ) chi D.m omega j (actualPrimeTupleLog N p) := by
    simpa only [P1OriginalVariableFourthContinuation.seedExponent, hancestor] using hraw
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  exact le_antisymm ((Real.rpow_le_rpow_left_iff hNr).mp hpow.le)
    ((Real.rpow_le_rpow_left_iff hNr).mp hpow.ge)

/-- Exact discrete-to-pointwise dictionary for the OLD variable fourth
maximum, including all eligible overlapping rows and the raw-Q3 floor. -/
theorem original_fourth_exponent_on_fifth_cell
    (N : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : Label5 D.m)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j) :
    P1OriginalVariableFourthContinuation.exponent4 (e : ℝ) chi D.m omega (N : ℝ)
        rows4 (P1OriginalVariableFourthContinuation.producerEligible licensed4)
        (fun r => r.bufferedCandidate (e : ℝ)) (rosserAncestor 4 (tupleHistory p)) =
      originalVariableFourthProfile e chi omega D.m j rows4 licensed4
        (actualPrimeTupleLog N p) := by
  have hlen : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have hlen4 : (rosserAncestor 4 (tupleHistory p)).length = 4 := by
    rw [rosserAncestor_length, hlen]
    norm_num
  have hcoords := primeHistoryLogCoordinates_eq_historicalPrefixProject
    (N : ℝ) (by omega : 4 ≤ 5) hlen
  rw [tupleHistory_log] at hcoords
  rw [P1OriginalVariableFourthContinuation.exponent4, if_pos hlen4,
    P1OriginalVariableFourthContinuation.seedExponent_ancestor_four,
    original_seed_on_fifth_cell D e chi omega N hN p hp j ht, hcoords]
  rfl

/-- A selected actual cell has the literal stored new cap and the exact
pointwise old fourth profile. The two residuals keep distinct strict gates. -/
theorem correctedTupleDifference_on_selected_cell
    (N cap : ℕ) (hN : 1 < N) (p : Fin 5 → ℕ) (hp : ∀ i, 0 < p i)
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j) :
    correctedTupleDifference D J e chi omega rows4 licensed4 N cap p =
      actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
        actualPrimeTupleOwnCubeMinus N cap
          (originalVariableFourthProfile e chi omega D.m j rows4 licensed4
            (actualPrimeTupleLog N p)) p := by
  unfold correctedTupleDifference
  rw [P1VariableFifthOriginalBaseQ3Bridge.corrected_stored_level_on_selected_cell
    D J e chi omega (N : ℝ) rows4 licensed4 (tupleHistory p)
      (by simp [tupleHistory]) j hj (by simpa only [tupleHistory_log] using ht),
    original_fourth_exponent_on_fifth_cell D e chi omega rows4 licensed4 N hN p hp j ht]

/-- Outside every selected fifth owner the two actual residuals cancel,
before any asymptotic or boundary argument. -/
theorem correctedTupleDifference_outside (N cap : ℕ) (p : Fin 5 → ℕ)
    (hout : ∀ j ∈ D.cells5 ∩ J,
      actualPrimeTupleLog N p ∉ logPrimeMeshCell 0 (19 / 96) D.m j) :
    correctedTupleDifference D J e chi omega rows4 licensed4 N cap p = 0 := by
  unfold correctedTupleDifference
  rw [P1VariableFifthOriginalBaseQ3Bridge.corrected_stored_exponent_outside
    D J e chi omega (N : ℝ) rows4 licensed4 (tupleHistory p)
      (by simpa only [tupleHistory_log] using hout), sub_self]

/-- A positive lower cut is recorded explicitly. It is not silently
discarded when the integral has a singular reciprocal-coordinate weight. -/
def correctedCellPrimeCorrection (a : ℝ) (N cap : ℕ) (j : Label5 D.m) : ℝ :=
  ∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (e : ℝ) chi D.m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈
          logPrimeBox (fun _ => a) (fun _ => (19 / 96 : ℝ)) ∩
            logPrimeMeshCell 0 (19 / 96) D.m j
        then correctedTupleDifference D J e chi omega rows4 licensed4 N cap p else 0)

/-- The original parent geometry and actual variable fourth profile are
both exact on this cell. This is the finite sum whose limit is still OPEN. -/
theorem correctedCellPrimeCorrection_eq_profileTupleSum
    (a : ℝ) (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 D.m) (hj : j ∈ D.cells5 ∩ J) :
    correctedCellPrimeCorrection D J e chi omega rows4 licensed4 a N cap j =
      ∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.primeBox N,
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ correctedOriginalCell e chi omega a D.m j
            then actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
              actualPrimeTupleOwnCubeMinus N cap
                (originalVariableFourthProfile e chi omega D.m j rows4 licensed4
                  (actualPrimeTupleLog N p)) p else 0) := by
  let low := logPrimeBox (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
  let mesh := logPrimeMeshCell 0 (19 / 96) D.m j
  have hfilter :
      (HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
        (e : ℝ) chi D.m omega N cap).filter
          (fun p => actualPrimeTupleLog N p ∈ low ∩ mesh) =
      (HistoricalThirdCoarse.P1OriginalCoarseFifth.primeBox N).filter
        (fun p => actualPrimeTupleLog N p ∈ correctedOriginalCell e chi omega a D.m j) := by
    calc
      _ = ((HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
          (e : ℝ) chi D.m omega N cap).filter
            (fun p => actualPrimeTupleLog N p ∈ mesh)).filter
              (fun p => actualPrimeTupleLog N p ∈ low) := by
        ext p
        simp only [Finset.mem_filter, Set.mem_inter_iff]
        tauto
      _ = _ := by
        rw [HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates_cell_filter
          (e : ℝ) chi D.m omega N cap hN hcap j]
        ext p
        simp only [Finset.mem_filter, correctedOriginalCell, Set.mem_inter_iff]
        tauto
  unfold correctedCellPrimeCorrection
  change (∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
    (e : ℝ) chi D.m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ low ∩ mesh then
        correctedTupleDifference D J e chi omega rows4 licensed4 N cap p else 0)) = _
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ correctedOriginalCell e chi omega a D.m j
  · rw [if_pos ht, if_pos ht]
    have hpos : ∀ i, 0 < p i := fun i =>
      (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
    rw [correctedTupleDifference_on_selected_cell D J e chi omega rows4 licensed4
      N cap hN p hpos j hj ht.2.1]
  · rw [if_neg ht, if_neg ht]

end Corrected

/-- The unit from the empty history survives in either original rough
coefficient. Thus the normalization never silently removes d=1. -/
theorem fixedRoughCoefficient_one_for_any_policy
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    fixedRoughCoefficient retainOdd N cap w z 1 = 1 := by
  simp only [fixedRoughCoefficient, oddFirstExitRetainedCoefficient_one, Int.cast_one]

end
end ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
