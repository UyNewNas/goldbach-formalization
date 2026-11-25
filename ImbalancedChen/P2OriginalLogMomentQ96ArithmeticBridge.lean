import ImbalancedChen.P2OriginalLogMomentQ96Checker
import ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure

/-! SOURCE-ONLY integration candidate. These definitional equalities retain
the existing analytic checker and its accepted dependency context. This file
has not been compiled locally: the old checker objects are not available in
the isolated pure-arithmetic environment. No old proof is assumed here. -/
namespace ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge

theorem fixedNumerator_eq (bits : ℕ) (r : ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.fixedNumerator bits r =
      P2OriginalLogMomentQ96CheckerSourceOnly.fixedNumerator bits r := rfl

theorem roundDownQ_eq (bits : ℕ) (r : ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.roundDownQ bits r =
      P2OriginalLogMomentQ96CheckerSourceOnly.roundDownQ bits r := rfl

theorem gapEvaluator_eq (moments : ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.gapEvaluator moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.gapEvaluator moments := rfl

theorem factorFloorQ80_eq (moments : ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.factorFloorQ80 moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 moments := rfl

theorem factorLowerQ80_eq (moments : ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.factorLowerQ80 moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.factorLowerQ80 moments := rfl

variable {ι : Type*} [Fintype ι]

theorem totalLowerQ80_eq (moments : ι → ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.totalLowerQ80 moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.totalLowerQ80 moments := rfl

theorem cubicQ_eq (T : ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.cubicQ T =
      P2OriginalLogMomentQ96CheckerSourceOnly.cubicQ T := rfl

theorem oldEvaluator_eq (actualMass : ℚ) (means : ι → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.oldEvaluator actualMass means =
      P2OriginalLogMomentQ96CheckerSourceOnly.oldEvaluator actualMass means := rfl

theorem newEvaluator_eq (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.newEvaluator actualMass means moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.newEvaluator actualMass means moments := rfl

theorem oldFloorQ96_eq (actualMass : ℚ) (means : ι → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.oldFloorQ96 actualMass means =
      P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 actualMass means := rfl

theorem newFloorQ96_eq (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.newFloorQ96 actualMass means moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96 actualMass means moments := rfl

theorem simplexLowerQ96_eq (actualMass : ℚ) (means : ι → ℚ) (moments : ι → ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.simplexLowerQ96 actualMass means moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.simplexLowerQ96 actualMass means moments := rfl

theorem checkStoredQ96_eq (stored : ℤ) (actualMass : ℚ)
    (means : ι → ℚ) (moments : ι → ℕ → ℚ) :
    P2OriginalLogMomentQ96ArithmeticPure.checkStoredQ96 stored actualMass means moments =
      P2OriginalLogMomentQ96CheckerSourceOnly.checkStoredQ96 stored actualMass means moments := rfl

#print axioms fixedNumerator_eq
#print axioms roundDownQ_eq
#print axioms gapEvaluator_eq
#print axioms factorFloorQ80_eq
#print axioms factorLowerQ80_eq
#print axioms totalLowerQ80_eq
#print axioms cubicQ_eq
#print axioms oldEvaluator_eq
#print axioms newEvaluator_eq
#print axioms oldFloorQ96_eq
#print axioms newFloorQ96_eq
#print axioms simplexLowerQ96_eq
#print axioms checkStoredQ96_eq

end ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge
