import ImbalancedChen.Part3OriginalActualSingleZeroPayment
import Mathlib.Tactic

/-! Transfer the proved two-source payment to the unchanged actual
restored/deleted S3 and its original primitive square. Diagonal and all
rough/mixed deletion corrections remain independent terms.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalActualSingleZeroRestoration

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalActualSingleZeroPayment
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open Classical Finset
open scoped BigOperators

noncomputable section

/-- This is a norm bound for the actual original source difference,
not merely a new finite term or a pointwise divisor envelope. -/
theorem exists_actual_offDiagonal_singleZero_restoration_payment
    (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key) (z : ℝ),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → 0 ≤ z →
        ‖(∑ t ∈ offDiagonalCarrier d k,
            S3FullTerm d (strictReceiverCutoff z) (roughY d.scale) k t) -
          (∑ t ∈ offDiagonalCarrier d k,
            S3DeletedTerm d (strictReceiverCutoff z) (roughY d.scale) k t)‖ ≤
        C * (singleZeroR k * (d.U + singleZeroY d k) * d.scale ^ epsilon) := by
  obtain ⟨C, hC, hbound⟩ := exists_actual_singleZeros_subpower_budget kappa epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro B sigma c0 d k z hd hsigma hc0 hz
  rw [offDiagonal_restore_identity d (strictReceiverCutoff z) (roughY d.scale) k
    (zero_lt_one.trans_le hd.2.1)]
  change ‖(_ + actualFirstZero d (strictReceiverCutoff z) (roughY d.scale) k +
    actualSecondZero d (strictReceiverCutoff z) (roughY d.scale) k) - _‖ ≤ _
  have heq (a b c : ℂ) : a + b + c - a = b + c := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (hbound B sigma c0 d k z hd hsigma hc0 hz)

/-- The independently defined primitive S3 is retained. Its true
diagonal is explicitly present, and only the two genuine off-diagonal
single-zero restoration differences are paid here. -/
theorem exists_actual_primitiveS3_singleZero_restoration_payment
    (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key) (z : ℝ),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → 0 ≤ z →
        ‖(primitiveS3 d (strictReceiverCutoff z) (roughY d.scale) k : ℂ) -
          ((∑ t ∈ diagonalCarrier d k,
              S3DeletedTerm d (strictReceiverCutoff z) (roughY d.scale) k t) +
            (∑ t ∈ offDiagonalCarrier d k,
              S3FullTerm d (strictReceiverCutoff z) (roughY d.scale) k t))‖ ≤
        C * (singleZeroR k * (d.U + singleZeroY d k) * d.scale ^ epsilon) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_actual_offDiagonal_singleZero_restoration_payment kappa epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro B sigma c0 d k z hd hsigma hc0 hz
  rw [S3_exact_diagonal_offDiagonal]
  have heq (a b c : ℂ) : (a + b) - (a + c) = -(c - b) := by ring
  rw [heq, norm_neg]
  exact hbound B sigma c0 d k z hd hsigma hc0 hz

end
end ImbalancedChen.Part3OriginalActualSingleZeroRestoration
