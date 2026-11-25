import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact evaluator representation mechanically copied from the original Q96
checker into an independent namespace. Types, bodies, generic index types,
and rounding direction are retained. A separate definitional bridge connects
the original namespace; existing analytic owners and objects are unchanged. -/
namespace ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure

noncomputable section
open scoped BigOperators

/-- Exactly Python Fraction.numerator*2^bits//Fraction.denominator. -/
def fixedNumerator (bits : ℕ) (r : ℚ) : ℤ := r.num * (2 : ℤ) ^ bits / (r.den : ℤ)

def roundDownQ (bits : ℕ) (r : ℚ) : ℚ := (fixedNumerator bits r : ℚ) / (2 : ℚ) ^ bits

/-- Moments are still stored rational fields here. They acquire semantics
only through actual moment equalities supplied to gapEvaluator_cast. -/
def gapEvaluator (moments : ℕ → ℚ) : ℚ :=
  ∑ j ∈ Finset.range 5, (moments (j + 2) - moments 1 ^ (j + 2)) / ((j : ℚ) + 2)

def factorFloorQ80 (moments : ℕ → ℚ) : ℤ := fixedNumerator 80 (gapEvaluator moments)

def factorLowerQ80 (moments : ℕ → ℚ) : ℚ := roundDownQ 80 (gapEvaluator moments)

variable {ι : Type*} [Fintype ι]

def totalLowerQ80 (moments : ι → ℕ → ℚ) : ℚ := ∑ i, factorLowerQ80 (moments i)

def cubicQ (T : ℚ) : ℚ := 1 + T * (1 + T * (1 / 2 + T / 6))

def oldEvaluator (actualMass : ℚ) (means : ι → ℚ) : ℚ := 4 * actualMass / ∏ i, means i

def newEvaluator (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : ℚ :=
  oldEvaluator actualMass means * cubicQ (totalLowerQ80 moments)

def oldFloorQ96 (actualMass : ℚ) (means : ι → ℚ) : ℤ :=
  fixedNumerator 96 (oldEvaluator actualMass means)

def newFloorQ96 (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : ℤ :=
  fixedNumerator 96 (newEvaluator actualMass means moments)

def simplexLowerQ96 (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : ℚ :=
  roundDownQ 96 (newEvaluator actualMass means moments)

def checkStoredQ96 (stored : ℤ) (m : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) : Bool :=
  decide (stored ≤ newFloorQ96 m means moments)

end

end ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure
