import ImbalancedChen.Part3OriginalPrescribedChartSpectrum
import ImbalancedChen.Part3OriginalOccupiedTraceSigns

/-! Reinsert the prescribed opposite-sign spectrum in every one of
the six original scale pairs. The positive-sign lane remains the
actual full-modulus arithmetic sum. The outer Fourier series retains
its original order relative to every inner spectral evaluation. -/
namespace ImbalancedChen.Part3.OriginalSixOppositeSpectrum20261112

noncomputable section
open Set Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102 OriginalCommonPoissonLanes20261102
open OriginalTwoZFourierAssembly20261102 OriginalFullModulusAssembly20261102
open OriginalOccupiedTraceSigns20261112 OriginalPrescribedChartSpectrum20261112

def pieceSpectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ)
    (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ∑ k∈originalKeys D,∑ j∈blockIndices J,
    (fullBlockMode D r k J j (positiveLane D k) M N ell+
     oppositeBlockSpectrum D r k J j (!(positiveLane D k)) M N ell)

theorem full_piece_opposite_spectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (ha : D.block.atom.residue≠0) (J : ℕ) (M : ℝ) {N : ℝ} (hN : 0<N) (ell : D4 → ℤ) :
    fullPieceMode D r J M N ell=pieceSpectrum D r J M N ell := by
  rw [fullPieceMode,pieceSpectrum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [← full_block_opposite_spectrum D r k ha J j _ (opposite_lanes D k).2 M hN ell]
  cases positiveLane D k <;> simp [add_comm]

theorem piece_spectrum_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J L : ℕ)
    {M N : ℝ} (hM : 0<M) (hN : 0<N) (hNC : N≤4*D.cScale) (ha : D.block.atom.residue≠0) :
    HasSum (pieceSpectrum D r J M N) (nonzeroBlocks D r J M N) :=
  (fullPiece_hasSum D r J L hM hN hNC ha).congr_fun (fun ell => (full_piece_opposite_spectrum D r ha J M hN ell).symm)

def sixSpectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ) (ell : D4 → ℤ) : ℂ :=
  pieceSpectrum D r J D.bScale D.cScale ell+
  pieceSpectrum D r J D.bScale (2*D.cScale) ell+
  pieceSpectrum D r J D.bScale (4*D.cScale) ell+
  pieceSpectrum D r J (2*D.bScale) D.cScale ell+
  pieceSpectrum D r J (2*D.bScale) (2*D.cScale) ell+
  pieceSpectrum D r J (2*D.bScale) (4*D.cScale) ell

/-- At the original global cutoff and Fourier reconstruction, all
opposite-sign portions now use the native spectrum. No exchange of
this outer Fourier series with an infinite spectral sum is needed. -/
theorem original_six_opposite_spectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (x epsilon : ℝ) (L : ℕ) (ha : D.block.atom.residue≠0) :
    let J := globalCutoff D x epsilon
    (smoothSix D r:ℂ)=sixRemainder D r J+∑' ell : D4 → ℤ,sixSpectrum D r J ell := by
  let J := globalCutoff D x epsilon
  rw [original_six_eq_remainder_and_full_modulus D r x epsilon L ha]
  congr 1
  apply tsum_congr
  intro ell
  have hC := D.cScale_pos
  have h₂ : 0<2*D.cScale := mul_pos (by norm_num) hC
  have h₄ : 0<4*D.cScale := mul_pos (by norm_num) hC
  simp only [fullSixMode,sixSpectrum,full_piece_opposite_spectrum D r ha J _ hC ell,
    full_piece_opposite_spectrum D r ha J _ h₂ ell,full_piece_opposite_spectrum D r ha J _ h₄ ell]

end
end ImbalancedChen.Part3.OriginalSixOppositeSpectrum20261112
