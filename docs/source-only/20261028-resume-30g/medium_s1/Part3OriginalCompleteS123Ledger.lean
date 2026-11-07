import ImbalancedChen.Part3OriginalPrincipalVarianceInOuterCauchy
import ImbalancedChen.Part3OriginalS2ActualCenteringLedger
import ImbalancedChen.Part3OriginalPoissonZeroCenteringCaller
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Expand the EXISTING actualResidualFunctional in its independently defined
S2 and S3 packets. This does not redefine the ledger or assume any packet
bound. The original signedError entrance, smooth discard and exact-product
correction are attached with their original coefficients and signs.
-/

namespace ImbalancedChen.Part3.OriginalCompleteS123Ledger20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumActualPreliminaryCauchy20261028
open MediumActualPsiPreliminaryDispersion20261028 MediumReceiverCutoffArithmetic20261028
open MediumLiteralS3Stages20261028 MediumActualS3ZeroCentering20261028
open MediumNativePrincipalSource20261028
open ActualMediumVarianceAtomBindingSourceOnly OriginalS1OuterCauchy20261028
open OriginalPrincipalVarianceInOuterCauchy20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3OriginalS2ActualCenteringLedger
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary

/-- The true F residual has the full original retained nonzero source,
the S3 omitted/diagonal/single-zero restoration packet, the rough and
diagonal-zero differences, and all four S2 terms with their actual signs.
The independently separated actual off-diagonal zero cancels by identity.
No principal model is substituted for a physical source. -/
theorem actual_residual_key_eq_original_packets
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) :
    ((primitiveS3 atom (strictReceiverCutoff z) y k -
        (genuineOffDiagonalZero atom (strictReceiverCutoff z) y k).re +
        (roughReplacementCorrection atom (strictReceiverCutoff z) y k).re -
        (genuineDiagonalZero atom (strictReceiverCutoff z) y k).re) -
      2 * (primitiveS2 atom (strictReceiverCutoff z) y k -
        (nativeMT atom (strictReceiverCutoff z) y k).re)) =
    (retainedSourceKey atom z y k).re + (remainingCorrectionKey atom z y k).re +
      (roughReplacementCorrection atom (strictReceiverCutoff z) y k).re -
      (genuineDiagonalZero atom (strictReceiverCutoff z) y k).re -
      2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) y k).re +
        (actualZeroGramError atom (strictReceiverCutoff z) y k).re -
        (otherRoughCorrection atom (strictReceiverCutoff z) y k).re -
        (singleZeroCorrection atom (strictReceiverCutoff z) y k).re) := by
  have h3 := congrArg Complex.re (literalS3_eq_retained_add_corrections hA z y k)
  rw [sourceCorrectionKey_eq_zero_add_remaining,
    actual_offDiagonalZero_eq_independent_zero] at h3
  simp only [Complex.ofReal_re, Complex.add_re] at h3
  have h2 := actual_primitive_S2_centered_identity hA (strictReceiverCutoff z) y k
  linarith

/-- Whole original ledger equality, retaining its actual outerL2 and
second owner-bank cardinality. No renamed candidate ledger is introduced. -/
theorem actualResidualFunctional_eq_complete_original_packets
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z : ℝ)
    (hA : MediumAdmissible b σ κ c0 atom) :
    actualResidualFunctional atom z = ((originalNumericKeys atom z).card : ℝ) *
      ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
        ((retainedSourceKey atom z (originalSmoothTrim atom) k).re +
          (remainingCorrectionKey atom z (originalSmoothTrim atom) k).re +
          (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
          2 * ((actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re +
            (actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re -
            (singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k).re)) := by
  unfold actualResidualFunctional
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [actual_residual_key_eq_original_packets atom z (originalSmoothTrim atom) k hA]

private theorem neg_re_le_norm (v : ℂ) : -v.re ≤ ‖v‖ := by
  simpa only [Complex.neg_re, norm_neg] using Complex.re_le_norm (-v)

/-- A genuine norm bound for every independent source packet, with the
two S2 factors and every original outside weight explicit. It does not
claim that any of these positive packet norms has yet been paid. -/
theorem actualResidualFunctional_le_original_packet_norms
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z : ℝ)
    (hA : MediumAdmissible b σ κ c0 atom) :
    actualResidualFunctional atom z ≤ ((originalNumericKeys atom z).card : ℝ) *
      ∑ k ∈ originalNumericKeys atom z, outerL2 atom k *
        (‖retainedSourceKey atom z (originalSmoothTrim atom) k‖ +
          ‖remainingCorrectionKey atom z (originalSmoothTrim atom) k‖ +
          ‖roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          ‖genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
          2 * (‖actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
            ‖actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
            ‖otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖ +
            ‖singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k‖)) := by
  rw [actualResidualFunctional_eq_complete_original_packets atom z hA]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
  linarith [Complex.re_le_norm (retainedSourceKey atom z (originalSmoothTrim atom) k),
    Complex.re_le_norm (remainingCorrectionKey atom z (originalSmoothTrim atom) k),
    Complex.re_le_norm (roughReplacementCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k),
    neg_re_le_norm (genuineDiagonalZero atom (strictReceiverCutoff z) (originalSmoothTrim atom) k),
    neg_re_le_norm (actualS2NonzeroModes atom (strictReceiverCutoff z) (originalSmoothTrim atom) k),
    neg_re_le_norm (actualZeroGramError atom (strictReceiverCutoff z) (originalSmoothTrim atom) k),
    Complex.re_le_norm (otherRoughCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k),
    Complex.re_le_norm (singleZeroCorrection atom (strictReceiverCutoff z) (originalSmoothTrim atom) k)]

/-- Exact entrance from the installed original signedError, including
the actual smooth-factor discard and preliminary exact products. -/
theorem signedError_eq_original_retained_discarded_exact
    (atom : MediumAtom) (z y : ℝ) (hz : 0 ≤ z) :
    atom.signedError = originalRetainedSource atom z y +
      discardedSource atom (strictReceiverCutoff z) y + exactProductCorrection atom := by
  have heq : retainedSource atom (strictReceiverCutoff z) y = originalRetainedSource atom z y := by
    unfold retainedSource originalRetainedSource
    rw [originalRetainedRows_eq_receiver atom z y hz]
  rw [signedError_eq_retained_discarded_exact atom (strictReceiverCutoff z) y, heq]

theorem original_signedError_norm_sq_le_entrance_terms
    (atom : MediumAtom) (z y : ℝ) (hz : 0 ≤ z) :
    ‖atom.signedError‖ ^ 2 ≤ 3 * ‖originalRetainedSource atom z y‖ ^ 2 +
      3 * ‖discardedSource atom (strictReceiverCutoff z) y‖ ^ 2 +
        3 * ‖exactProductCorrection atom‖ ^ 2 := by
  rw [signedError_eq_original_retained_discarded_exact atom z y hz]
  have hn := (norm_add_le (originalRetainedSource atom z y +
      discardedSource atom (strictReceiverCutoff z) y) (exactProductCorrection atom)).trans
    (add_le_add_right (norm_add_le _ _) _)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖originalRetainedSource atom z y‖ -
      ‖discardedSource atom (strictReceiverCutoff z) y‖),
    sq_nonneg (‖originalRetainedSource atom z y‖ - ‖exactProductCorrection atom‖),
    sq_nonneg (‖discardedSource atom (strictReceiverCutoff z) y‖ - ‖exactProductCorrection atom‖)]

/-- The paid S1/P step now enters the actual original signedError,
with its real unchanged residual and BOTH entrance corrections present.
This is an intermediate deduction, not a restricted-medium theorem. -/
theorem uniformAuxiliarySW_signedError_sq_le_complete_entrance
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (σ κ c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, 0 ≤ z →
        ‖(F i).signedError‖ ^ 2 ≤ 3 * actualResidualFunctional (F i) z +
          C * (F i).scale ^ 2 / Real.log (F i).scale ^ A +
          3 * ‖discardedSource (F i) (strictReceiverCutoff z) (originalSmoothTrim (F i))‖ ^ 2 +
          3 * ‖exactProductCorrection (F i)‖ ^ 2 := by
  obtain ⟨C, hC, x0, hx0, hbound⟩ :=
    uniformAuxiliarySW_original_source_sq_le_residual_add_log_error F B C0 σ κ c0
      hadmissible hSW hσ A hA
  refine ⟨3 * C, by positivity, x0, hx0, ?_⟩
  intro i hx z hz
  have he := original_signedError_norm_sq_le_entrance_terms (F i) z (originalSmoothTrim (F i)) hz
  have hr := hbound i hx z hz
  nlinarith

end
end ImbalancedChen.Part3.OriginalCompleteS123Ledger20261028
