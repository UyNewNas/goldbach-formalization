import ImbalancedChen.Part3OriginalPrimaryPacketRows
import ImbalancedChen.Part3OriginalCommonPoissonLanes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact O arithmetic six-piece -> actual primary coefficient rows.  The
zero-difference term retains all m.  Only nonzero y is partitioned into
primary/sign/y-dyadic blocks, with its separate m=0, positive/reflected
negative common m blocks, and actual summable tail.  Nothing is discarded.

The kernel is STILL the original discrete-c Kloosterman kernel.  No spectral
identity or desired energy bound is an input or a claimed conclusion.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly
open P3ActualLiteralPacketIntegralSourceOnly

namespace ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102

attribute [local instance] Classical.propDecidable

/-- Finite coordinate notation, used below only with the existing literal
completed/zero-m/common-block/tail kernels.  K is a payload, not a proof
of a source equality or an estimate. -/
def rowPairing (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (K : Output → ℂ) : ℂ :=
  ∑ z ∈ levelCarrier D k, ∑ n ∈ nCarrier D k z,
    blockBeta D r k (decode k z n) * K (decode k z n)

theorem original_source_block_eq_rows (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (K : Output → ℂ) :
    (∑ s ∈ primaryBlock D k, weight (D.lambda r) D.omega s * K (output s)) =
      rowPairing D r k K := by
  rw [weighted_pushforward]
  exact sum_output_eq_rows D k (fun zy => blockBeta D r k zy * K zy)

/-- The same identity in genuine CoprimePacket coefficient coordinates.
The inverse cusp phase remains explicit; it is not silently deleted. -/
theorem row_fibre_eq_signed_coefficients (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (K : Output → ℂ) :
    (∑ n ∈ nCarrier D k z.val,
      blockBeta D r k (decode k z.val n) * K (decode k z.val n)) =
      ∑ n ∈ nCarrier D k z.val,
        signedCoefficient k.2.2 (rowPacket D r k z) n *
          cuspPhase (!k.2.2) z.val n * K (decode k z.val n) := by
  apply sum_congr rfl
  intro n hn
  rw [rowCoefficient_unphase]

def resolvedRows (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (J : ℕ) (M N : ℝ) : ℂ :=
  rowPairing D r k (zeroMKernel M N D.cScale D.block.atom.residue) +
    (∑ j ∈ blockIndices J,
      (rowPairing D r k (blockKernel J j false M N D.cScale D.block.atom.residue) +
       rowPairing D r k (blockKernel J j true M N D.cScale D.block.atom.residue))) +
    rowPairing D r k (tailKernel J M N D.cScale D.block.atom.residue)

/-- The cutoff J and the positive/reflected intervals are identical at
every level and every primary/y block.  The rough-s frequency r remains
only in the original coefficient. -/
theorem rowPairing_completed_eq_resolved (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) {M : ℝ}
    (hM : 0 < M) (J : ℕ) (N : ℝ) :
    rowPairing D r k (completedKernel M N D.cScale D.block.atom.residue) =
      resolvedRows D r k J M N := by
  have h := jointMass_eq_resolved D r hM J N (primaryBlock D k)
  unfold jointMass resolvedJointMass jointZeroM jointBlock jointTail at h
  simp_rw [sum_output_eq_rows D k] at h
  exact h

def primaryRowPiece (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) : ℂ :=
  jointMass D r M N (zeroSource (originalSource D)) +
    ∑ k ∈ originalKeys D, resolvedRows D r k J M N

/-- First, the exact block partition of the original completed piece,
before any estimate or truncation. -/
theorem completedPiece_eq_zero_and_primary_rows (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (M N : ℝ) :
    completedPiece 1 D.block.atom.residue D.sCarrier D.hBound
      (D.lambda r) D.omega M N D.bScale D.cScale D.fScale =
      jointMass D r M N (zeroSource (originalSource D)) +
        ∑ k ∈ originalKeys D,
          rowPairing D r k (completedKernel M N D.cScale D.block.atom.residue) := by
  rw [completedPiece_eq_source]
  change (∑ s ∈ originalSource D,
    weight (D.lambda r) D.omega s *
      completedKernel M N D.cScale D.block.atom.residue (output s)) = _
  rw [sum_zero_nonzero, finite_source_assembly D.block.atom.residue (originalSource D)]
  congr 1
  · exact weighted_pushforward (zeroSource (originalSource D))
      (D.lambda r) D.omega (completedKernel M N D.cScale D.block.atom.residue)
  · apply sum_congr rfl
    intro k hk
    exact original_source_block_eq_rows D r k
      (completedKernel M N D.cScale D.block.atom.residue)

theorem completedPiece_eq_primaryRowPiece (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) {M : ℝ} (hM : 0 < M) (J : ℕ) (N : ℝ) :
    completedPiece 1 D.block.atom.residue D.sCarrier D.hBound
      (D.lambda r) D.omega M N D.bScale D.cScale D.fScale =
      primaryRowPiece D r J M N := by
  rw [completedPiece_eq_zero_and_primary_rows]
  unfold primaryRowPiece
  congr 1
  apply sum_congr rfl
  intro k hk
  exact rowPairing_completed_eq_resolved D r k hM J N

/-- Full original six-piece identity in actual level/n coordinates.
Each nonzero original beta has the nonempty coefficient-row witness
proved in nonzero_original_beta_has_row.  Neither a zero lane nor a
Poisson tail is claimed to be paid by this exact identity. -/
theorem original_six_eq_primary_rows (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (x epsilon : ℝ) :
    let J := globalCutoff D x epsilon
    (smoothSix D r : ℂ) =
      primaryRowPiece D r J D.bScale D.cScale +
      primaryRowPiece D r J D.bScale (2 * D.cScale) +
      primaryRowPiece D r J D.bScale (4 * D.cScale) +
      primaryRowPiece D r J (2 * D.bScale) D.cScale +
      primaryRowPiece D r J (2 * D.bScale) (2 * D.cScale) +
      primaryRowPiece D r J (2 * D.bScale) (4 * D.cScale) := by
  dsimp only
  unfold smoothSix OriginalData.row
  rw [sixSmoothMass_eq_completed _ _ _ _ _ _ D.bScale_pos]
  have hB2 : 0 < 2 * D.bScale := mul_pos (by norm_num) D.bScale_pos
  simp only [completedPiece_eq_primaryRowPiece D r D.bScale_pos
    (globalCutoff D x epsilon),
    completedPiece_eq_primaryRowPiece D r hB2 (globalCutoff D x epsilon)]

end ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102
end
