import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import ImbalancedChen.P1OriginalFifthWeightedSourceReduction

/-!
Canonical ACTUAL variable-fifth global source definitions.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.
No D, stored cap or owned-row surrogate appears. Both strict own-cube gates
remain inside the actual residual difference on every original T3 next
candidate, including candidates rejected by the old own test.
-/

namespace ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1CorrectedFifthCausalTupleDictionary
open P1OriginalFifthWeightedSourceReduction
open P1OriginalCoarseFifthContinuation

section Source
variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m)) (rows5 : Finset (FifthRow m))

/-- Literal actual new5 minus ACTUAL old4 normalized own-cube residuals. -/
def tupleDifference (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  literalTupleDifference
    (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
    (P1OriginalVariableFifthContinuation.level5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    N cap p

def normalizedSaving (N cap : ℕ) : ℝ :=
  actualFifthSaving e chi m omega rows4 licensed4 J5 rows5 N cap ((N : ℝ) ^ (19 / 96 : ℝ)) *
    Real.log (N : ℝ) / singularSeries N

def fullTupleCharge (N cap : ℕ) : ℝ :=
  ∑ p ∈ sourceCarrier e chi m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) * tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p

def fullCellCharge (N cap : ℕ) (j : P1OriginalVariableFifthContinuation.Label5 m) : ℝ :=
  ∑ p ∈ sourceCarrier e chi m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p else 0)

/-- The positive source keeps the exact same original next-candidate carrier. -/
def positiveCellCharge (a : ℝ) (N cap : ℕ) (j : P1OriginalVariableFifthContinuation.Label5 m) : ℝ :=
  ∑ p ∈ (sourceCarrier e chi m omega N cap).filter (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p else 0)

/-- Canonical actual variable-fifth small source, with every small face
and the literal signed same-source own-cube difference retained. -/
def smallCellRemainder (a : ℝ) (N cap : ℕ) (j : P1OriginalVariableFifthContinuation.Label5 m) : ℝ :=
  ∑ p ∈ (sourceCarrier e chi m omega N cap).filter (fun p => ∃ i, actualPrimeTupleLog N p i < a),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        tupleDifference e chi m omega rows4 licensed4 J5 rows5 N cap p else 0)

def positiveCharge (a : ℝ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    positiveCellCharge e chi m omega rows4 licensed4 J5 rows5 a N cap j

def smallRemainder (a : ℝ) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    smallCellRemainder e chi m omega rows4 licensed4 J5 rows5 a N cap j

/-- No normalization or frontier supplier is assumed: the general exact
causal dictionary is instantiated with the ACTUAL fourth and fifth levels. -/
theorem normalizedSaving_eq_fullTupleCharge (N cap : ℕ) :
    normalizedSaving e chi m omega rows4 licensed4 J5 rows5 N cap =
      fullTupleCharge e chi m omega rows4 licensed4 J5 rows5 N cap := by
  unfold normalizedSaving P1OriginalVariableFifthContinuation.actualFifthSaving
  rw [actualHistoricalFifthSaving_eq_literalTupleSum]
  rfl

end Source
end
end ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly
