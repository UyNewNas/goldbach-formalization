import ImbalancedChen.P2EnhancedSeedActualFeedbackAssembly
import ImbalancedChen.P2EnhancedSeedD5PlusLogFubini
import ImbalancedChen.P2EnhancedSeedPairD7Integral
import ImbalancedChen.P2EnhancedSeedPairD8PieceSum

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal original W2 feedback coefficient is the sum of its three
singleton logarithmic integrals and FOUR actual pair logarithmic integrals.
D5+ has its three rational affine pieces; D6 is untruncated; D7 retains
its actual max boundary; D8 has its two rational affine pieces. These
identities do not supply the missing numerical proof lambda/50>13/5000.
-/

namespace ImbalancedChen.P2EnhancedSeedActualSevenLogIdentity
noncomputable section
open Set MeasureTheory Classical
open scoped Interval
open P2EnhancedSeedSingletonPrimitive (parameters seedUpper)
open P2EnhancedSeedActualFeedbackAssembly
open P5OriginalActionMassBound (Point W2PairDomain)

section D5
open P2EnhancedSeedD5PlusGeometry P2EnhancedSeedD5PlusLogFubini
def d5Logs : ℝ :=
  (∫ u in P2EnhancedSeedSingletonPrimitive.a0..cutOne,logSlice u (supportSum-u) cap)+
  (∫ u in cutOne..cutTwo,logSlice u u cap)+
  (∫ u in cutTwo..top,logSlice u u (1-2*u))
end D5

def d6Log : ℝ :=
  ∫ u in Ioo P2EnhancedSeedPairD6Primitive.uLo P2EnhancedSeedPairD6Primitive.uHi,
    P2EnhancedSeedInheritedCellBounds.d6OuterSlice u

def d7Log : ℝ :=
  ∫ u in Ioo P2EnhancedSeedPairD7Domain.supportStart P2EnhancedSeedPairD7Domain.uHi,
    P2EnhancedSeedPairD7Integral.outerSlice u

section D8
open P2EnhancedSeedPairD8Geometry P2EnhancedSeedPairD8Integral
def d8Logs : ℝ := (∫ u in Ioc uLo cut,firstSlice u)+(∫ u in Ioo cut uHi,secondSlice u)
end D8

/-- Raw normalisation is paid on each literal original pair domain.
This binds the suppliers' log formulas to the actual W2 integrands. -/
theorem pairTerm_raw (J : ℝ) (j : Fin 4) : pairTerm J j =
    ∫ x in W2PairDomain parameters j,
      seedUpper J (P5OriginalFeedbackDomains.pairProfile parameters j x)*
        P2EnhancedSeedPairD6Primitive.pairKernel x := by
  apply setIntegral_congr_fun (P5OriginalFeedbackDomains.measurableSet_W2PairDomain _ _)
  intro x hx
  have hg := P5OriginalFeedbackDomains.W2PairDomain_geometry
    P2EnhancedSeedSingletonPrimitive.parameters_geometry j hx
  rw [P5OriginalActionMassBound.pairKernel_eq_raw hg.1 hg.2]
  dsimp [P2EnhancedSeedPairD6Primitive.pairKernel]
  ring

theorem pairCoefficient_D5_logs : pairCoefficient 0=d5Logs := by
  calc
    _ = pairTerm 1 0 := by rw [pairTerm_exact,one_mul]
    _ = ∫ x in P2EnhancedSeedD5PlusGeometry.D5plus,
        P2EnhancedSeedD5PlusGeometry.feedback 1 x := pairTerm_raw 1 0
    _ = _ := by
      simpa only [one_mul,d5Logs] using
        P2EnhancedSeedD5PlusLogFubini.feedback_three_affine_logs (1 : ℝ)

theorem pairCoefficient_D7_log : pairCoefficient 2=d7Log := by
  calc
    _ = pairTerm 1 2 := by rw [pairTerm_exact,one_mul]
    _ = ∫ x in P2EnhancedSeedPairD7Domain.D7,
        P2EnhancedSeedPairD7Domain.feedback 1 x := pairTerm_raw 1 2
    _ = _ := by
      simpa only [one_mul,d7Log] using
        P2EnhancedSeedPairD7Integral.D7_feedback_outer_log (1 : ℝ)

theorem pairCoefficient_D8_logs : pairCoefficient 3=d8Logs := by
  calc
    _ = pairTerm 1 3 := by rw [pairTerm_exact,one_mul]
    _ = ∫ x in P2EnhancedSeedPairD8Geometry.D8,
        P2EnhancedSeedPairD8Integral.feedback 1 x := pairTerm_raw 1 3
    _ = ∫ u in Ioo P2EnhancedSeedPairD8Geometry.uLo P2EnhancedSeedPairD8Geometry.uHi,
        P2EnhancedSeedPairD8Integral.outerSlice u := by
      simpa only [one_mul] using
        P2EnhancedSeedPairD8Integral.feedback_outer_log (1 : ℝ)
    _ = d8Logs := P2EnhancedSeedPairD8PieceSum.outerSlice_piece_sum

/-- Exact additive sum of the ACTUAL seven positive terms, after the
same common division by five. No cell-bound or coefficient premise. -/
theorem lambda_exact_seven_logs : lambda=
    (singletonCoefficient 0+singletonCoefficient 1+singletonCoefficient 2+
      d5Logs+d6Log+d7Log+d8Logs)/5 := by
  unfold lambda
  rw [pairCoefficient_D5_logs,pairCoefficient_D6_log,
    pairCoefficient_D7_log,pairCoefficient_D8_logs]
  rfl

theorem actualFeedback_exact_seven_logs (J : ℝ) : actualFeedback J=
    J*((singletonCoefficient 0+singletonCoefficient 1+singletonCoefficient 2+
      d5Logs+d6Log+d7Log+d8Logs)/5) := by
  rw [actualFeedback_eq_mul_lambda,lambda_exact_seven_logs]

/-- The original J=1/50 input. Evaluating this real expression with a
passing rational certificate is still required for the claimed budget. -/
theorem actualFeedback_one_fiftieth_exact : actualFeedback (1/50)=
    (singletonCoefficient 0+singletonCoefficient 1+singletonCoefficient 2+
      d5Logs+d6Log+d7Log+d8Logs)/250 := by
  rw [actualFeedback_exact_seven_logs]
  ring

end
end ImbalancedChen.P2EnhancedSeedActualSevenLogIdentity
