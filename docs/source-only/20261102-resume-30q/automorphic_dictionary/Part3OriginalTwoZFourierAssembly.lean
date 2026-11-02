import ImbalancedChen.Part3OriginalTwoZSourceAssembly
import ImbalancedChen.Part3NativePeriod64Reconstruction

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual normalized-F reconstruction is applied to both fixed Z charts
of the original source, then summed over every real z/n/c/p index.  Its
commonPoissonCompleted weight is derived from that reconstruction; it
is not an unrelated phase definition.  A final single HasSum/tsum
retains all primary keys, both Poisson signs and all six smooth pieces.

The remainder is explicitly the old full y=0 term plus the nonzero-y
m=0 and outside-window tail terms.  No bound for these terms is claimed.
Every mode still contains the signed discrete Kloosterman sum.  No
Kuznetsov, ABL, spectral Fourier product, PacketData or energy premise
is introduced or manufactured by this Fourier separation.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102
open ImbalancedChen.Part3.OriginalTwoZSourceAssembly20261102
open ImbalancedChen.Part3.ActualNormalizedSmoothF
open ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (e norm_e point4 actualCoeff spectralMode spectralTest actual_global_separation_hasSum)

namespace ImbalancedChen.Part3.OriginalTwoZFourierAssembly20261102

attribute [local instance] Classical.propDecidable

/-- The literal O completed-variable weight equals the m-character
which the actual normalized-F reconstruction supplies. -/
theorem commonPoissonCompleted_weight_eq_e (J j : ℕ) (ell : D4 → ℤ)
    {p : ℕ} (hp : p ∈ commonMBlock J j) :
    (commonPoissonCompleted J j (ell 1)).weight p =
      e ((ell 1 : ℝ) / 64 * ((p : ℝ) / (2 ^ j : ℕ))) := by
  rw [commonPoissonCompleted_weight J j (ell 1) p hp]
  unfold e
  push_cast
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A modulation of the original beta.  It has no m, c or height input. -/
def modulatedBeta (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (ell : D4 → ℤ) (z n : ℕ) : ℂ :=
  blockBeta D r k (decode k z n) *
    e ((ell 2 : ℝ) / 64 * (((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1) +
      (ell 3 : ℝ) / 64 * ((z : ℝ) / fixedZ D upper))

theorem norm_modulatedBeta (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (ell : D4 → ℤ) (z n : ℕ) :
    ‖modulatedBeta D r k upper ell z n‖ = ‖blockBeta D r k (decode k z n)‖ := by
  simp only [modulatedBeta, norm_mul, norm_e, mul_one]

/-- Compatibility with P's actual CoprimePacket.  The inverse cusp
phase is retained, so this is NOT the automorphic ABL extraction. -/
theorem modulatedBeta_eq_unphased_row (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (ell : D4 → ℤ) (z : Row D k) (n : ℕ) :
    signedCoefficient k.2.2
        (modePacket (rowPacket D r k z) ell (dyadicScale k.2.1) (fixedZ D upper)) n *
      cuspPhase (!k.2.2) z.val n = modulatedBeta D r k upper ell z.val n := by
  rw [signedCoefficient_modePacket]
  change (signedCoefficient k.2.2 (rowPacket D r k z) n *
      e ((ell 2 : ℝ) / 64 * (((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1) +
        (ell 3 : ℝ) / 64 * ((z.val : ℝ) / fixedZ D upper))) *
      cuspPhase (!k.2.2) z.val n = _
  rw [mul_right_comm, rowCoefficient_unphase]
  rfl

def chartModeAtom (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) (z n c p : ℕ) : ℂ :=
  (commonPoissonCompleted J j (ell 1)).weight p *
    modulatedBeta D r k upper ell z n * chartScalar D upper M z c *
      spectralTest ell (chartY0 D k upper j N) (sourceArgument D k z n c p) *
        sourceKloosterman D k negativeM z n c p

def chartMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ∑ z ∈ chartLevels D k upper, ∑ n ∈ nCarrier D k z,
    ∑ c ∈ Ioc 0 (Nat.floor (10 * D.cScale)),
      if c.Coprime z then
        ∑ p ∈ commonMBlock J j, chartModeAtom D r k upper J j negativeM M N ell z n c p
      else 0

/-- Actual Fourier reconstruction at a literal discrete c and signed
Kloosterman value.  The spectral argument is not integrated or changed
to an independent variable.  All three coordinate bounds are derived. -/
theorem original_chart_atom_hasSum (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (J j L : ℕ) (negativeM : Bool) (M N : ℝ) {z n c p : ℕ}
    (hz : z ∈ chartLevels D k upper) (hn : n ∈ nCarrier D k z)
    (hp : p ∈ commonMBlock J j) :
    HasSum (fun ell : D4 → ℤ =>
      actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
        chartModeAtom D r k upper J j negativeM M N ell z n c p)
      (blockBeta D r k (decode k z n) *
        normalizedFrequency D k upper j negativeM M N z n c p) := by
  have hp0 := commonMBlock_normalized J j hp
  have hn0 := nCarrier_normalized D k z hn
  have hz0 := chartLevels_normalized D k upper hz
  have hpCell : (p : ℝ) / (2 ^ j : ℕ) ∈ Set.Ioo (-32 : ℝ) 32 := by
    constructor <;> linarith [hp0.1, hp0.2]
  have hnCell : ((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1 ∈
      Set.Ioo (-32 : ℝ) 32 := by
    constructor <;> linarith [hn0.1, hn0.2]
  have hzCell : (z : ℝ) / fixedZ D upper ∈ Set.Ioo (-32 : ℝ) 32 := by
    constructor <;> linarith [hz0.1, hz0.2]
  have h := actual_global_separation_hasSum
    ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) L
    (sourceArgument D k z n c p / chartY0 D k upper j N)
    ((p : ℝ) / (2 ^ j : ℕ)) (((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1)
    ((z : ℝ) / fixedZ D upper) hpCell hnCell hzCell
  have hh : HasSum (fun ell : D4 → ℤ =>
      actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
        chartModeAtom D r k upper J j negativeM M N ell z n c p)
      ((blockBeta D r k (decode k z n) * chartScalar D upper M z c *
        sourceKloosterman D k negativeM z n c p) *
        normalizedF ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1)
          (point4 (sourceArgument D k z n c p / chartY0 D k upper j N)
            ((p : ℝ) / (2 ^ j : ℕ)) (((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1)
            ((z : ℝ) / fixedZ D upper))) := by
    apply (HasSum.mul_left
      (blockBeta D r k (decode k z n) * chartScalar D upper M z c *
        sourceKloosterman D k negativeM z n c p) h).congr_fun
    intro ell
    simp only [chartModeAtom, modulatedBeta,
      commonPoissonCompleted_weight_eq_e J j ell hp, spectralTest]
    ring
  convert hh using 1
  simp only [normalizedFrequency, point, point4]
  ring

/-- A single actualCoeff multiplies the ENTIRE fixed-Z source family;
finite/infinite exchange follows from HasSum, without a target premise. -/
theorem chart_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j L : ℕ) (negativeM : Bool) (M N : ℝ) :
    HasSum (fun ell : D4 → ℤ =>
      actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
        chartMode D r k upper J j negativeM M N ell)
      (chartPhysical D r k upper J j negativeM M N) := by
  have hc (z n c : ℕ) (hz : z ∈ chartLevels D k upper)
      (hn : n ∈ nCarrier D k z) :
      HasSum (fun ell : D4 → ℤ =>
        if c.Coprime z then
          ∑ p ∈ commonMBlock J j,
            actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
              chartModeAtom D r k upper J j negativeM M N ell z n c p
        else 0)
        (if c.Coprime z then
          ∑ p ∈ commonMBlock J j, blockBeta D r k (decode k z n) *
            normalizedFrequency D k upper j negativeM M N z n c p
        else 0) := by
    by_cases hcz : c.Coprime z
    · simp only [if_pos hcz]
      exact hasSum_sum (s := commonMBlock J j) (fun p hp =>
        original_chart_atom_hasSum D r k upper J j L negativeM M N hz hn hp)
    · simp only [if_neg hcz]
      exact hasSum_zero
  have hs := hasSum_sum (s := chartLevels D k upper) (fun z hz =>
    hasSum_sum (s := nCarrier D k z) (fun n hn =>
      hasSum_sum (s := Ioc 0 (Nat.floor (10 * D.cScale))) (fun c _hc => hc z n c hz hn)))
  apply hs.congr_fun
  intro ell
  simp only [chartMode, mul_sum, mul_ite, mul_zero]

def blockMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (J j : ℕ) (negativeM : Bool) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
    (chartMode D r k false J j negativeM M N ell +
      chartMode D r k true J j negativeM M N ell)

/-- This is the original whole block, not a chosen PacketData.  The
same commonPoissonCompleted J j (ell 1) occurs on BOTH fixed-Z charts. -/
theorem original_block_hasSum (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (J j L : ℕ)
    (negativeM : Bool) (M N : ℝ) (hM : 0 < M) (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) :
    HasSum (blockMode D r k J j negativeM M N)
      (rowPairing D r k
        (blockKernel J j negativeM M N D.cScale D.block.atom.residue)) := by
  rw [rowPairing_block_eq_two_chartPhysical D r k J j negativeM M N hM hN ha]
  have h := (chart_hasSum D r k false J j L negativeM M N).add
    (chart_hasSum D r k true J j L negativeM M N)
  apply h.congr_fun
  intro ell
  exact mul_add _ _ _

/-- Every excluded lane is an original object, not an error defined
by subtraction from the claimed Fourier identity. -/
def pieceRemainder (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) : ℂ :=
  jointMass D r M N (zeroSource (originalSource D)) +
    ∑ k ∈ originalKeys D,
      (rowPairing D r k (zeroMKernel M N D.cScale D.block.atom.residue) +
        rowPairing D r k (tailKernel J M N D.cScale D.block.atom.residue))

def nonzeroBlocks (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) : ℂ :=
  ∑ k ∈ originalKeys D, ∑ j ∈ blockIndices J,
    (rowPairing D r k (blockKernel J j false M N D.cScale D.block.atom.residue) +
      rowPairing D r k (blockKernel J j true M N D.cScale D.block.atom.residue))

def pieceMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ∑ k ∈ originalKeys D, ∑ j ∈ blockIndices J,
    (blockMode D r k J j false M N ell + blockMode D r k J j true M N ell)

theorem primaryRowPiece_eq_remainder_add_nonzero (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (J : ℕ) (M N : ℝ) :
    primaryRowPiece D r J M N =
      pieceRemainder D r J M N + nonzeroBlocks D r J M N := by
  unfold primaryRowPiece resolvedRows pieceRemainder nonzeroBlocks
  simp only [sum_add_distrib]
  ring

theorem nonzeroBlocks_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J L : ℕ) (M N : ℝ) (hM : 0 < M) (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) :
    HasSum (pieceMode D r J M N) (nonzeroBlocks D r J M N) := by
  exact hasSum_sum (s := originalKeys D) (fun k _hk =>
    hasSum_sum (s := blockIndices J) (fun j _hj =>
      (original_block_hasSum D r k J j L false M N hM hN ha).add
        (original_block_hasSum D r k J j L true M N hM hN ha)))

theorem completedPiece_eq_remainder_and_fourier (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (J L : ℕ) (M N : ℝ)
    (hM : 0 < M) (hN : 0 < N) (ha : D.block.atom.residue ≠ 0) :
    completedPiece 1 D.block.atom.residue D.sCarrier D.hBound
      (D.lambda r) D.omega M N D.bScale D.cScale D.fScale =
      pieceRemainder D r J M N + ∑' ell : D4 → ℤ, pieceMode D r J M N ell := by
  rw [completedPiece_eq_primaryRowPiece D r hM J N,
    primaryRowPiece_eq_remainder_add_nonzero,
    (nonzeroBlocks_hasSum D r J L M N hM hN ha).tsum_eq]

def sixRemainder (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ) : ℂ :=
  pieceRemainder D r J D.bScale D.cScale +
    pieceRemainder D r J D.bScale (2 * D.cScale) +
    pieceRemainder D r J D.bScale (4 * D.cScale) +
    pieceRemainder D r J (2 * D.bScale) D.cScale +
    pieceRemainder D r J (2 * D.bScale) (2 * D.cScale) +
    pieceRemainder D r J (2 * D.bScale) (4 * D.cScale)

def sixMode (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ)
    (ell : D4 → ℤ) : ℂ :=
  pieceMode D r J D.bScale D.cScale ell +
    pieceMode D r J D.bScale (2 * D.cScale) ell +
    pieceMode D r J D.bScale (4 * D.cScale) ell +
    pieceMode D r J (2 * D.bScale) D.cScale ell +
    pieceMode D r J (2 * D.bScale) (2 * D.cScale) ell +
    pieceMode D r J (2 * D.bScale) (4 * D.cScale) ell

/-- One Fourier series for the complete original six-piece family.
J is the same global cutoff in every primary block and at every level.
r remains the earlier rough-s frequency, never the Poisson variable.
All zero-y/m=0/tail terms remain in the explicit sixRemainder. -/
theorem original_six_eq_remainder_and_fourier (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (x epsilon : ℝ) (L : ℕ)
    (ha : D.block.atom.residue ≠ 0) :
    let J := globalCutoff D x epsilon
    (smoothSix D r : ℂ) = sixRemainder D r J + ∑' ell : D4 → ℤ, sixMode D r J ell := by
  let J := globalCutoff D x epsilon
  change (smoothSix D r : ℂ) = sixRemainder D r J + ∑' ell : D4 → ℤ, sixMode D r J ell
  have hB2 : 0 < 2 * D.bScale := mul_pos (by norm_num) D.bScale_pos
  have hC2 : 0 < 2 * D.cScale := mul_pos (by norm_num) D.cScale_pos
  have hC4 : 0 < 4 * D.cScale := mul_pos (by norm_num) D.cScale_pos
  have hs := (((((nonzeroBlocks_hasSum D r J L D.bScale D.cScale
      D.bScale_pos D.cScale_pos ha).add
    (nonzeroBlocks_hasSum D r J L D.bScale (2 * D.cScale)
      D.bScale_pos hC2 ha)).add
    (nonzeroBlocks_hasSum D r J L D.bScale (4 * D.cScale)
      D.bScale_pos hC4 ha)).add
    (nonzeroBlocks_hasSum D r J L (2 * D.bScale) D.cScale
      hB2 D.cScale_pos ha)).add
    (nonzeroBlocks_hasSum D r J L (2 * D.bScale) (2 * D.cScale)
      hB2 hC2 ha)).add
    (nonzeroBlocks_hasSum D r J L (2 * D.bScale) (4 * D.cScale) hB2 hC4 ha)
  have hsource := original_six_eq_primary_rows D r x epsilon
  dsimp only at hsource
  simp only [primaryRowPiece_eq_remainder_add_nonzero] at hsource
  calc
    (smoothSix D r : ℂ) = sixRemainder D r J +
        (nonzeroBlocks D r J D.bScale D.cScale +
          nonzeroBlocks D r J D.bScale (2 * D.cScale) +
          nonzeroBlocks D r J D.bScale (4 * D.cScale) +
          nonzeroBlocks D r J (2 * D.bScale) D.cScale +
          nonzeroBlocks D r J (2 * D.bScale) (2 * D.cScale) +
          nonzeroBlocks D r J (2 * D.bScale) (4 * D.cScale)) := by
      rw [hsource]
      dsimp only [sixRemainder, J]
      ring
    _ = _ := by
      congr 1
      exact hs.tsum_eq.symm

end ImbalancedChen.Part3.OriginalTwoZFourierAssembly20261102
end
