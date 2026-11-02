import ImbalancedChen.Part3OriginalTwoZFourierAssembly
import ImbalancedChen.Part3OriginalNonzeroCuspOneSource
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is the original Q Fourier atom, converted to the arithmetic side of
the normalized infinity/one trace formula.  The preexisting ordinary
Kloosterman sign involution is applied BEFORE the cusp conversion.  Thus
the completed index is positive and the second cusp index includes the
original residue, y sign AND Poisson sign.  The original beta and common
additive phase are not conjugated.  The physical outside factor is exactly
M*sqrt(Z), and the inner denominator is the true cusp modulus c*sqrt(z).

No automorphic basis, Fourier coefficient, trace formula or spectral-energy
theorem is postulated or supplied by this arithmetic conversion.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalTwoZSourceAssembly20261102
open ImbalancedChen.Part3.OriginalTwoZFourierAssembly20261102
open ImbalancedChen.Part3.OriginalNonzeroCuspOneSource20261102
open ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e norm_e spectralTest)

namespace ImbalancedChen.Part3.OriginalSignedTraceInput20261102

/-- The second index after making the ORIGINAL Poisson index positive.
It is not merely the primary y-sign and is not an independently chosen sign. -/
def traceIndex (D : OriginalData) (k : BlockKey) (negativeM : Bool)
    (z n : ℕ) : ℤ :=
  if negativeM then -(D.block.atom.residue * (decode k z n).2)
  else D.block.atom.residue * (decode k z n).2

/-- One sign for the entire fixed primary/Poisson block, before choosing z,n,c,p. -/
def traceNegative (D : OriginalData) (k : BlockKey) (negativeM : Bool) : Bool :=
  if negativeM then !(if D.block.atom.residue < 0 then !k.2.2 else k.2.2)
  else if D.block.atom.residue < 0 then !k.2.2 else k.2.2

theorem traceIndex_eq_signedY (D : OriginalData) (k : BlockKey)
    (negativeM : Bool) (z n : ℕ) :
    traceIndex D k negativeM z n =
      signedY (traceNegative D k negativeM)
        (D.block.atom.residue.natAbs * (k.1 * n)) := by
  by_cases ha : D.block.atom.residue < 0
  · cases negativeM <;> cases hY : k.2.2 <;>
      simp [traceIndex, traceNegative, decode, signedY, ha, hY,
        Int.natCast_natAbs, abs_of_neg ha] <;> ring
  · have ha0 : 0 ≤ D.block.atom.residue := le_of_not_gt ha
    cases negativeM <;> cases hY : k.2.2 <;>
      simp [traceIndex, traceNegative, decode, signedY, ha, hY,
        Int.natCast_natAbs, abs_of_nonneg ha0] <;> ring

theorem traceIndex_natAbs (D : OriginalData) (k : BlockKey)
    (negativeM : Bool) (z n : ℕ) :
    (traceIndex D k negativeM z n).natAbs =
      D.block.atom.residue.natAbs * (k.1 * n) := by
  cases negativeM <;>
    simp only [traceIndex, Bool.false_eq_true, if_false, if_true,
      Int.natAbs_neg, Int.natAbs_mul, decode, signedY_natAbs]

/-- Positivity is obtained from the actual row, not from a spectral hypothesis. -/
theorem traceIndex_natAbs_pos (D : OriginalData) (k : BlockKey)
    (negativeM : Bool) (z : ℕ) {n : ℕ} (hn : n ∈ nCarrier D k z)
    (ha : D.block.atom.residue ≠ 0) :
    0 < (traceIndex D k negativeM z n).natAbs := by
  rw [traceIndex_natAbs]
  have hrow := nCarrier_positive_coprime D k z hn
  exact Nat.mul_pos (Int.natAbs_pos.mpr ha) (Nat.mul_pos hrow.1 hrow.2.1)

/-- Reuse the already proved all-residue involution; the original coefficient
and its Fourier mode are unaffected.  This also includes modulus one. -/
theorem sourceKloosterman_eq_positive_m (D : OriginalData) (k : BlockKey)
    (negativeM : Bool) (z n c p : ℕ) [NeZero c] :
    sourceKloosterman D k negativeM z n c p =
      kloosterman c ((p : ℤ) * inverseResidue c (z : ℤ))
        (traceIndex D k negativeM z n) := by
  cases negativeM
  · simp only [sourceKloosterman, traceIndex, signedY,
      Bool.false_eq_true, if_false]
  · simp only [sourceKloosterman, traceIndex, signedY, if_true, neg_mul]
    exact kloosterman_negative_linear _ _

/-- Exact positive-m trace input at the manuscript's fixed old cusp-one
scaling.  The reciprocal phase must use traceIndex, including negativeM. -/
theorem sourceKloosterman_eq_positive_cuspOne
    (D : OriginalData) (k : BlockKey) (negativeM : Bool)
    (z n c p : ℕ) [NeZero c] (hz : 0 < z) (hzc : z.Coprime c) :
    sourceKloosterman D k negativeM z n c p =
      e (-((traceIndex D k negativeM z n : ℤ) : ℝ) / (z : ℝ)) *
        cuspOneMatrixSum z c hzc (p : ℤ) (traceIndex D k negativeM z n) := by
  rw [sourceKloosterman_eq_positive_m]
  simpa only [neg_div] using
    physical_kloosterman_eq_cuspOne z c hz hzc (p : ℤ)
      (traceIndex D k negativeM z n)

def traceModulus (z c : ℕ) : ℝ := Real.sqrt (z : ℝ) * (c : ℝ)

theorem traceModulus_pos {z c : ℕ} (hz : 0 < z) (hc : 0 < c) :
    0 < traceModulus z c := by
  unfold traceModulus
  exact mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hz)) (by exact_mod_cast hc)

/-- The original 4*pi argument is the trace argument with the absolute
value of the actual signed second index.  No c-integral or Jacobian occurs. -/
theorem sourceArgument_eq_traceArgument (D : OriginalData) (k : BlockKey)
    (negativeM : Bool) (z n c p : ℕ) :
    sourceArgument D k z n c p =
      4 * Real.pi * Real.sqrt ((p : ℝ) *
        ((traceIndex D k negativeM z n).natAbs : ℝ)) / traceModulus z c := by
  rw [traceIndex_natAbs]
  unfold sourceArgument spectralArgument traceModulus
  have hproduct : (D.block.atom.residue.natAbs : ℝ) * (p : ℝ) *
      ((k.1 * n : ℕ) : ℝ) = (p : ℝ) *
      ((D.block.atom.residue.natAbs * (k.1 * n) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hproduct, mul_comm (c : ℝ) (Real.sqrt (z : ℝ))]

theorem chartScalar_eq_trace_modulus (D : OriginalData) (upper : Bool)
    (M : ℝ) (z c : ℕ) :
    chartScalar D upper M z c =
      ((M * Real.sqrt (fixedZ D upper) : ℝ) : ℂ) / (traceModulus z c : ℂ) := by
  rw [chartScalar, traceModulus, mul_comm (c : ℝ) (Real.sqrt (z : ℝ)),
    Complex.ofReal_div]

/-- This coefficient is the literal primary beta with its Q modes and the
inverse cusp phase.  In particular it has no c, p or spectral-height input. -/
def traceBeta (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (ell : D4 → ℤ) (z n : ℕ) : ℂ :=
  modulatedBeta D r k upper ell z n *
    e (-((traceIndex D k negativeM z n : ℤ) : ℝ) / (z : ℝ))

theorem norm_traceBeta (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (ell : D4 → ℤ) (z n : ℕ) :
    ‖traceBeta D r k upper negativeM ell z n‖ =
      ‖blockBeta D r k (decode k z n)‖ := by
  simp only [traceBeta, norm_mul, norm_e, mul_one, norm_modulatedBeta]

/-- The actual Q atom at a licensed source level, now in normalized trace
coordinates.  It still contains the matrix-defined generalized Kloosterman
sum; replacing that sum by a complete spectral expansion is a separate theorem. -/
theorem original_chartModeAtom_eq_normalized_cuspOne
    (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) (z n c p : ℕ) [NeZero c]
    (hz : z ∈ chartLevels D k upper) (hcz : c.Coprime z) :
    chartModeAtom D r k upper J j negativeM M N ell z n c p =
      ((M * Real.sqrt (fixedZ D upper) : ℝ) : ℂ) *
        (commonPoissonCompleted J j (ell 1)).weight p *
        traceBeta D r k upper negativeM ell z n *
        (cuspOneMatrixSum z c hcz.symm (p : ℤ)
          (traceIndex D k negativeM z n) / (traceModulus z c : ℂ) *
          spectralTest ell (chartY0 D k upper j N)
            (4 * Real.pi * Real.sqrt ((p : ℝ) *
              ((traceIndex D k negativeM z n).natAbs : ℝ)) /
              traceModulus z c)) := by
  have hzpos := (levelCarrier_licensed D k (chartLevels_subset D k upper hz)).1
  rw [chartModeAtom,
    sourceKloosterman_eq_positive_cuspOne D k negativeM z n c p hzpos hcz.symm,
    chartScalar_eq_trace_modulus,
    sourceArgument_eq_traceArgument D k negativeM]
  unfold traceBeta
  ring

end ImbalancedChen.Part3.OriginalSignedTraceInput20261102
end
