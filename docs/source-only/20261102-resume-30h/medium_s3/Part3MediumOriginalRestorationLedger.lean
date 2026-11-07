import ImbalancedChen.Part3MediumOriginalRestorationLogPayment
import ImbalancedChen.Part3OriginalPoissonZeroCenteringCaller
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Bind the new analytic payment to the existing actual S3 and the EXISTING
remainingCorrectionKey. Omitted modes and the retained Fourier diagonal
remain visible. This does not identify the full retained source with its
clean E2 part or pay the gcd, close-pair or roughReplacement corrections.
-/

namespace ImbalancedChen.Part3.MediumOriginalRestorationLedger20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumOriginalRestorationLogPayment20261102
open MediumActualDiagonalDivisorPayment20261028 MediumActualRestorationPayment20261028
open MediumLiteralS3Stages20261028 MediumGlobalDyadicOwnership20261028
open MediumReceiverCutoffArithmetic20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding

/-- This expands the independently defined F ledger, rather than
declaring a new correction object equal to the desired bound. -/
theorem remainingCorrectionKey_eq_restoration_omitted_diagonal
    (atom : MediumAtom) (z y : ℝ) (k : Key) :
    remainingCorrectionKey atom z y k =
      restorationCorrection atom (strictReceiverCutoff z) y k +
        offDiagonalOmitted atom z y k - diagonalRetained atom z y k := by
  unfold remainingCorrectionKey restorationCorrection actualDiagonal
    actualFirstZero actualSecondZero
  ring

/-- Exact original deleted/full source comparison. In particular the
double-zero diagonal is never restored. -/
theorem primitiveS3_sub_restoredOffDiagonal_eq_restoration
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hAdm : MediumAdmissible B σ κ c0 atom) (z y : ℝ) (k : Key) :
    (primitiveS3 atom z y k : ℂ) - restoredOffDiagonal atom z y k =
      restorationCorrection atom z y k := by
  rw [actual_S3_restoration_identity atom z y k (zero_lt_one.trans_le hAdm.2.1)]
  ring

/-- The logarithmic payment is attached directly to the unchanged
primitiveS3 and the literal full-indicator off-diagonal sum. -/
theorem exists_original_S3_deleted_full_comparison
    (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ (z : ℝ) (k : Key), 0 ≤ z →
      k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) →
      ‖(primitiveS3 atom (strictReceiverCutoff z) (roughY atom.scale) k : ℂ) -
        restoredOffDiagonal atom (strictReceiverCutoff z) (roughY atom.scale) k‖ ≤
        3 * actualVScale atom k / Real.log atom.scale ^ A := by
  obtain ⟨x0, hx0, hpay⟩ := exists_original_S3_restoration_log_payment σ κ A hσ hσsmall
  refine ⟨x0, hx0, ?_⟩
  intro B c0 atom hAdm hc0 hx z k hz hk
  rw [primitiveS3_sub_restoredOffDiagonal_eq_restoration hAdm]
  exact hpay B c0 atom hAdm hc0 hx z k hz hk

/-- A genuine partial payment of the EXISTING remaining correction.
The two unestimated Fourier terms are kept with their actual norm costs. -/
theorem exists_original_remainingCorrection_partial_payment
    (σ κ A : ℝ) (hσ : 0 < σ) (hσsmall : σ < 1 / 100) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B σ κ c0 atom → 0 < c0 → x0 ≤ atom.scale →
      ∀ (z : ℝ) (k : Key), 0 ≤ z →
      k ∈ keyBank atom (strictReceiverCutoff z) (roughY atom.scale) →
      ‖remainingCorrectionKey atom z (roughY atom.scale) k‖ ≤
        3 * actualVScale atom k / Real.log atom.scale ^ A +
        ‖offDiagonalOmitted atom z (roughY atom.scale) k‖ +
        ‖diagonalRetained atom z (roughY atom.scale) k‖ := by
  obtain ⟨x0, hx0, hpay⟩ := exists_original_S3_restoration_log_payment σ κ A hσ hσsmall
  refine ⟨x0, hx0, ?_⟩
  intro B c0 atom hAdm hc0 hx z k hz hk
  rw [remainingCorrectionKey_eq_restoration_omitted_diagonal]
  calc
    _ ≤ ‖restorationCorrection atom (strictReceiverCutoff z) (roughY atom.scale) k +
        offDiagonalOmitted atom z (roughY atom.scale) k‖ +
        ‖diagonalRetained atom z (roughY atom.scale) k‖ := norm_sub_le _ _
    _ ≤ (‖restorationCorrection atom (strictReceiverCutoff z) (roughY atom.scale) k‖ +
        ‖offDiagonalOmitted atom z (roughY atom.scale) k‖) +
        ‖diagonalRetained atom z (roughY atom.scale) k‖ :=
      add_le_add_right (norm_add_le _ _) _
    _ ≤ _ := add_le_add_right
      (add_le_add_right (hpay B c0 atom hAdm hc0 hx z k hz hk) _) _

end
end ImbalancedChen.Part3.MediumOriginalRestorationLedger20261102
