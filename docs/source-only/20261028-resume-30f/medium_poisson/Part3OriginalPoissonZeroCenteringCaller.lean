import ImbalancedChen.Part3OriginalActualLambdaPairExpansion
import ImbalancedChen.Part3MediumActualS3ZeroCentering
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The exact off-diagonal zero term already retained in our actual S3
correction dictionary is the peer's independently centered zero source.
Its MT+P identity is consumed in one direction, with rough-replacement
and diagonal zero corrections displayed. No Gram or variance bound is
assumed, and no centering theorem depends on this Poisson caller.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalPoissonSourceCorrections20261028
open ImbalancedChen.Part3.OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
open ImbalancedChen.Part3.MediumActualS3ZeroCentering20261028

namespace ImbalancedChen.Part3.OriginalPoissonZeroCenteringCaller20261028

theorem actual_offDiagonalZero_eq_independent_zero
    (atom : MediumAtom) (z y : ℝ) (k : Key) :
    offDiagonalZero atom z y k =
      genuineOffDiagonalZero atom (strictReceiverCutoff z) y k := rfl

/-- Exactly the original restoration/retained-diagonal corrections
other than the independently centered off-diagonal zero mode. -/
def remainingCorrectionKey (atom : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  (∑ t ∈ diagonalCarrier atom k,
    S3DeletedTerm atom (strictReceiverCutoff z) y k t) +
  offDiagonalOmitted atom z y k - diagonalRetained atom z y k -
  (∑ t ∈ offDiagonalCarrier atom k,
    firstZeroTerm atom (strictReceiverCutoff z) y k t) -
  ∑ t ∈ offDiagonalCarrier atom k,
    secondZeroTerm atom (strictReceiverCutoff z) y k t

theorem sourceCorrectionKey_eq_zero_add_remaining
    (atom : MediumAtom) (z y : ℝ) (k : Key) :
    sourceCorrectionKey atom z y k =
      offDiagonalZero atom z y k + remainingCorrectionKey atom z y k := by
  unfold sourceCorrectionKey remainingCorrectionKey
  ring

/-- Actual coefficient/source dictionary into MT+P. The nonclean rough
replacement and true diagonal zero remain separate signed corrections. -/
theorem actual_sourceCorrection_re_eq_MT_P_remaining
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    (sourceCorrectionKey atom z y k).re =
      (nativeMT atom (strictReceiverCutoff z) y k).re +
        nativeP atom (strictReceiverCutoff z) y k +
        (roughReplacementCorrection atom (strictReceiverCutoff z) y k).re -
        (genuineDiagonalZero atom (strictReceiverCutoff z) y k).re +
        (remainingCorrectionKey atom z y k).re := by
  rw [sourceCorrectionKey_eq_zero_add_remaining, Complex.add_re,
    actual_offDiagonalZero_eq_independent_zero,
    genuineOffDiagonalZero_re_eq_MT_P_corrections hA]

/-- Pointwise original primitive S3 source now has both the genuine
constructed full Poisson family and the correct independent MT+P source.
No principal term is silently canceled with an S1 or S2 contribution. -/
theorem literalS3_eq_family_MT_P_remaining
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) (Csep : ℕ) :
    primitiveS3 atom (strictReceiverCutoff z) y k =
      (keyRawFamily atom z y k hA Csep).re +
      (nativeMT atom (strictReceiverCutoff z) y k).re +
      nativeP atom (strictReceiverCutoff z) y k +
      (roughReplacementCorrection atom (strictReceiverCutoff z) y k).re -
      (genuineDiagonalZero atom (strictReceiverCutoff z) y k).re +
      (remainingCorrectionKey atom z y k).re := by
  have hs := congrArg Complex.re (literalS3_eq_actual_family_add_corrections hA z y k Csep)
  simp only [Complex.ofReal_re, Complex.add_re] at hs
  rw [actual_sourceCorrection_re_eq_MT_P_remaining hA z y k] at hs
  exact hs.trans (by ring)

end ImbalancedChen.Part3.OriginalPoissonZeroCenteringCaller20261028
