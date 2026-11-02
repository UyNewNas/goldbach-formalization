import ImbalancedChen.Part3OriginalSixTailPhysicalPayment
import ImbalancedChen.Part3ActualZeroPoissonNativeSource
import ImbalancedChen.Part3OriginalFullModulusAssembly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two zero lanes in the same Q remainder receive their actual existing
finite estimates.  The y=0 lane keeps all completed m; the m=0 lane is
restricted to y!=0.  The original source, signed f, multiplicities,
common s frequency, and the original 10*C modulus carrier are preserved.

The resulting divisor envelope, beta norm and support cardinality are
explicit.  This file does not claim their final normalized small-power
payment or the nonzero-m automorphic estimate.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.ActualCompletedZeroPaymentSourceOnly
open ImbalancedChen.Part3.ActualZeroPoissonNativeSource20261102
open ImbalancedChen.Part3.OriginalReciprocalPrefixDictionary20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalSixTailBinding20261102
open ImbalancedChen.Part3.OriginalSixTailPhysicalPayment20261102
open ImbalancedChen.Part3.OriginalFullModulusAssembly20261102
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

namespace ImbalancedChen.Part3.OriginalZeroLaneBinding20261102

attribute [local instance] Classical.propDecidable

def originalZeroY (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (M N : ℝ) : ℂ := jointMass D r M N (zeroSource (originalSource D))

def originalZeroM (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (M N : ℝ) : ℂ :=
  ∑ k ∈ originalKeys D,
    rowPairing D r k (zeroMKernel M N D.cScale D.block.atom.residue)

theorem pieceZeros_eq_original_zero_lanes (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (M N : ℝ) :
    pieceZeros D r M N = originalZeroY D r M N + originalZeroM D r M N := rfl

/-- Native zeroPiece and O's original joint y=0 source are definitionally
the same grouped source, with its full signed f window. -/
theorem originalZeroY_eq_zeroPiece (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (M N : ℝ) :
    originalZeroY D r M N =
      zeroPiece 1 D.block.atom.residue D.sCarrier D.hBound
        (D.lambda r) D.omega M N D.cScale D.fScale := rfl

theorem originalZeroY_norm_le {b : ℕ} {sigma kappa c0 : ℝ}
    (D : OriginalData) (hA : MediumAdmissible b sigma kappa c0 D.atom)
    (r : ZMod (prefixPeriod D.key)) {M N : ℝ} (hM : 0 < M) (hN : 0 < N) :
    ‖originalZeroY D r M N‖ ≤
      72 * M * N * D.fScale * (D.hBound : ℝ) * scaleS D.key *
        (tauEnvelope D.sCarrier (poissonNonzeroFrequencyWindow D.hBound) : ℝ) := by
  rw [originalZeroY_eq_zeroPiece]
  exact zeroPiece_norm_le 1 D.block.atom.residue D.sCarrier D.hBound
    (D.lambda r) D.omega D.cScale hM hN (scaleS_pos D.key).le D.fScale_pos.le
    (fun s hs => D.sCarrier_positive hs) (original_sCarrier_card_le D)
    (fun s _ => original_lambda_norm_le_one D hA r s)
    (fun h _ => originalOmega_norm_le_one D.block D.rectangle h)

/-- The 5/2 support of the actual bump covers N=C,2C,4C exactly.
No endpoint correction is manufactured by this native conversion. -/
theorem original_zeroMKernel_eq_native (D : OriginalData) (M : ℝ)
    {N : ℝ} (hN : 0 < N) (hNC : N ≤ 4 * D.cScale) (zy : Output) :
    zeroMKernel M N D.cScale D.block.atom.residue zy =
      ActualZeroPoissonKernel20261102.zeroKernel N M D.block.atom.residue zy := by
  calc
    _ = ∑ c ∈ Ioc 0 (Nat.floor (10 * D.cScale)),
        (scaledDyadicCutoff N c : ℂ) *
          (if c.Coprime zy.1 then
            frequency M c D.block.atom.residue zy.2 (zy.1 : ℤ) 0 else 0) := by
      unfold zeroMKernel weightedC
      apply sum_congr rfl
      intro c hc
      by_cases hz : c.Coprime zy.1 <;> simp only [hz, if_true, if_false, mul_zero]
    _ = _ := (smooth_modulus_sum_eq_capped hN hNC _).symm

/-- The exact primary partition is consumed before the native m=0
estimate, so all primary/dyadic/sign labels are accounted for once. -/
theorem originalZeroM_eq_native (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (M : ℝ) {N : ℝ}
    (hN : 0 < N) (hNC : N ≤ 4 * D.cScale) :
    originalZeroM D r M N =
      nativeZeroPiece (nonzeroSource (originalSource D)) (D.lambda r) D.omega
        N M D.block.atom.residue := by
  unfold originalZeroM
  simp_rw [← original_source_block_eq_rows]
  rw [← finite_source_assembly D.block.atom.residue (originalSource D)]
  unfold nativeZeroPiece
  apply sum_congr rfl
  intro s hs
  rw [original_zeroMKernel_eq_native D M hN hNC]

theorem originalZeroM_sq_le (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) :
    let U := nonzeroSource (originalSource D)
    ‖originalZeroM D r M N‖ ^ 2 ≤
      (6 * M * ActualZeroPoissonKernel20261102.zeroFourierMass *
        (nativeResidueDivisorMaximum U D.block.atom.residue : ℝ)) ^ 2 *
        ((U.image output).card : ℝ) * nativeCoefficientNorm U (D.lambda r) D.omega := by
  dsimp only
  rw [originalZeroM_eq_native D r M hN hNC]
  exact nativeZeroPiece_sq_le hN hM (nonzeroSource (originalSource D))
    (D.lambda r) D.omega D.block.atom.residue ha
    (fun s hs => (mem_filter.mp hs).2)

/-- R20's full-positive-modulus source is consumed literally.  Its exact
zero Fourier correction adds no new cost to these three original lanes.
This is still an arithmetic identity, not a normalized spectral return. -/
theorem original_six_eq_zeros_tail_and_full_modulus (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (x eps : ℝ) (L : ℕ)
    (ha : D.block.atom.residue ≠ 0) :
    let J := globalCutoff D x eps
    (smoothSix D r : ℂ) = sixZeros D r + sixTail D r J +
      ∑' ell : P3NativePeriod64SamplingSourceOnly.D4 → ℤ, fullSixMode D r J ell := by
  dsimp only
  rw [original_six_eq_remainder_and_full_modulus D r x eps L ha,
    sixRemainder_eq_zeros_add_tail]

end ImbalancedChen.Part3.OriginalZeroLaneBinding20261102
end
