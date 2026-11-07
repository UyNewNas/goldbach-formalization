import ImbalancedChen.P1OriginalVariableFourthSourceCoefficient
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

One original source through both variable continuations.  Its normalized
finite charge is the sum of the actual Fin4 PLUS residual charge and the
actual Fin5 two-own-cube MINUS residual charge.  Both use the identical
firstStop/raw-Q3 tree, target, enumeration cap and rough prime universe.

No generic HistoricalPrefixCapData parent or old5 lookup is inserted.
No convergence, selected numerical row table or final bound is assumed.
-/

namespace ImbalancedChen.P1OriginalFourthFifthTotalTupleSource

noncomputable section
open scoped Classical BigOperators
open P1CorrectedFifthDensityDictionary
open P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthContinuation

abbrev ProducerRow := P2OriginalFourthCapProducerInterface.ProducerRow
abbrev FifthRow (m : ℕ) := P1OriginalVariableFifthContinuation.FifthRow m

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- The fourth term is the original admitted four-tuple PLUS difference. -/
def fourthCharge (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ firstExitAdmittedTuples 4 (originalT3 e chi m omega N)
      (roughPrimeUniverse N cap 0 z),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      literalTupleResidualDifference
        (originalQ3 e chi m omega N)
        (originalQ4 e chi m omega N rows4 licensed4) N cap p

/-- The fifth term retains all next candidates and both strict own cubes. -/
def fifthCharge (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4 (originalT3 e chi m omega N)
      (roughPrimeUniverse N cap 0 z),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      P1CorrectedFifthCausalTupleDictionary.literalTupleDifference
        (originalQ4 e chi m omega N rows4 licensed4)
        (P1OriginalVariableFifthContinuation.level5 e chi m omega (N : ℝ)
          rows4 licensed4 J5 rows5) N cap p

def originalThirdRetained (N cap : ℕ) (z : ℝ) : ℝ :=
  firstExitRetainedPolynomial (originalT3 e chi m omega N)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)

/-- Exact simultaneous tuple dictionary for the ORIGINAL two-stage source.
The intermediate variable fourth retained polynomial cancels at finite N. -/
theorem original_third_sub_variable_fifth_eq_total_tuple_charge
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    (originalThirdRetained e chi m omega N cap z -
      variableFifthRetained e chi m omega N cap z rows4 licensed4 J5 rows5) *
        Real.log (N : ℝ) / singularSeries N =
      fourthCharge e chi m omega rows4 licensed4 N cap z +
        fifthCharge e chi m omega rows4 licensed4 J5 rows5 N cap z := by
  have h4 :=
    P1OriginalVariableFourthSourceCoefficient.original_policy_difference_eq_admitted_tuple_sum
      (e : ℝ) chi m omega N cap z rows4 licensed4 hN.le
  change (originalThirdRetained e chi m omega N cap z -
      originalFourthRetained e chi m omega N cap z rows4 licensed4) *
        Real.log (N : ℝ) / singularSeries N =
      fourthCharge e chi m omega rows4 licensed4 N cap z at h4
  have h5 :
      (originalFourthRetained e chi m omega N cap z rows4 licensed4 -
        variableFifthRetained e chi m omega N cap z rows4 licensed4 J5 rows5) *
          Real.log (N : ℝ) / singularSeries N =
        fifthCharge e chi m omega rows4 licensed4 J5 rows5 N cap z := by
    rw [variable_fifth_finite_density_identity e chi m omega N cap hN z
      rows4 licensed4 J5 rows5]
    exact P1CorrectedFifthCausalTupleDictionary.actualHistoricalFifthSaving_eq_literalTupleSum
      (originalBase e m N) (originalQ3 e chi m omega N)
      (originalQ4 e chi m omega N rows4 licensed4)
      (P1OriginalVariableFifthContinuation.level5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) N cap z
  calc
    _ = (originalThirdRetained e chi m omega N cap z -
        originalFourthRetained e chi m omega N cap z rows4 licensed4) *
          Real.log (N : ℝ) / singularSeries N +
        (originalFourthRetained e chi m omega N cap z rows4 licensed4 -
          variableFifthRetained e chi m omega N cap z rows4 licensed4 J5 rows5) *
          Real.log (N : ℝ) / singularSeries N := by ring
    _ = _ := congrArg₂ (· + ·) h4 h5

/-- Empty history is retained through both continuations without any row
licence.  Thus the normalized tuple telescope has not deleted d=1. -/
theorem variable_fifth_empty_history_mem (N cap : ℕ) (w z : ℝ) :
    ({selected := [], positive := true, mass := 1} : FirstExitLeaf ℕ) ∈
      firstExitRetainedLeaves
        (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
          rows4 licensed4 J5 rows5)
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) := by
  exact firstExitRetainedLeaves_skipAll_mem _ _ _ _ _ _

theorem variable_fifth_modulus_one_mem (N cap : ℕ) (w z : ℝ) :
    1 ∈ firstExitRetainedModuli
      (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) (roughPrimeUniverse N cap w z) := by
  apply (mem_firstExitRetainedModuli _ _ _).mpr
  exact ⟨⟨[], true, 1⟩,
    variable_fifth_empty_history_mem e chi m omega rows4 licensed4 J5 rows5 N cap w z,
    by simp⟩

theorem variable_fifth_modulus_one_coefficient (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedCoefficient
      (P1OriginalVariableFifthContinuation.policy5 e chi m omega (N : ℝ)
        rows4 licensed4 J5 rows5) (roughPrimeUniverse N cap w z) 1 = 1 := by
  have hmem := variable_fifth_modulus_one_mem
    e chi m omega rows4 licensed4 J5 rows5 N cap w z
  simp [firstExitRetainedCoefficient, hmem]

end
end ImbalancedChen.P1OriginalFourthFifthTotalTupleSource
