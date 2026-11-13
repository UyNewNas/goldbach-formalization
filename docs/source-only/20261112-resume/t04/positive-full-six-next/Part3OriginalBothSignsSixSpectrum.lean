import ImbalancedChen.Part3OriginalPrescribedPositiveChart

/-! Both signs of the one original arithmetic singleton, at all six
physical scales. The outer period-64 Fourier sum retains its position. -/
namespace ImbalancedChen.Part3.OriginalBothSignsSixSpectrum20261112
noncomputable section
open Complex
open scoped BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102 OriginalCommonPoissonLanes20261102
open OriginalTwoZFourierAssembly20261102 OriginalFullModulusAssembly20261102
open OriginalOccupiedTraceSigns20261112 OriginalPrescribedChartSpectrum20261112
open OriginalSixOppositeSpectrum20261112 OriginalPrescribedPositiveChart20261112

def bothPiece (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ) (M N : ℝ) (ell : D4→ℤ) : ℂ :=
  ∑ k∈originalKeys D,∑ j∈blockIndices J,
    (positiveBlock D r k J j (positiveLane D k) M N ell+
      oppositeBlockSpectrum D r k J j (!(positiveLane D k)) M N ell)

theorem piece_eq (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (ha : D.block.atom.residue≠0)
    (J : ℕ) (M : ℝ) {N : ℝ} (hN : 0<N) (ell : D4→ℤ) :
    pieceSpectrum D r J M N ell=bothPiece D r J M N ell := by
  unfold pieceSpectrum bothPiece
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  rw [full_block_positive D r k ha J j _ (opposite_lanes D k).1 M hN ell]

theorem both_piece_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J L : ℕ)
    {M N : ℝ} (hM : 0<M) (hN : 0<N) (hNC : N≤4*D.cScale) (ha : D.block.atom.residue≠0) :
    HasSum (bothPiece D r J M N) (nonzeroBlocks D r J M N) :=
  (piece_spectrum_hasSum D r J L hM hN hNC ha).congr_fun (fun ell => (piece_eq D r ha J M hN ell).symm)

def bothSix (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ) (ell : D4→ℤ) :=
  bothPiece D r J D.bScale D.cScale ell+
    bothPiece D r J D.bScale (2*D.cScale) ell+
    bothPiece D r J D.bScale (4*D.cScale) ell+
    bothPiece D r J (2*D.bScale) D.cScale ell+
    bothPiece D r J (2*D.bScale) (2*D.cScale) ell+
    bothPiece D r J (2*D.bScale) (4*D.cScale) ell

/-- Absolute convergence over the original Fourier modes after the six
spectral expressions have been evaluated at each individual mode. -/
theorem both_six_summable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J L : ℕ)
    (ha : D.block.atom.residue≠0) : Summable (fun ell : D4→ℤ => ‖bothSix D r J ell‖) := by
  have b₂ : 0<2*D.bScale := mul_pos (by norm_num) D.bScale_pos
  have c₂ : 0<2*D.cScale := mul_pos (by norm_num) D.cScale_pos
  have c₄ : 0<4*D.cScale := mul_pos (by norm_num) D.cScale_pos
  have c₁₄ : D.cScale≤4*D.cScale := by linarith [D.cScale_pos]
  have c₂₄ : 2*D.cScale≤4*D.cScale := by linarith [D.cScale_pos]
  have S := (((((both_piece_hasSum D r J L D.bScale_pos D.cScale_pos c₁₄ ha).add
    (both_piece_hasSum D r J L D.bScale_pos c₂ c₂₄ ha)).add
    (both_piece_hasSum D r J L D.bScale_pos c₄ le_rfl ha)).add
    (both_piece_hasSum D r J L b₂ D.cScale_pos c₁₄ ha)).add
    (both_piece_hasSum D r J L b₂ c₂ c₂₄ ha)).add
    (both_piece_hasSum D r J L b₂ c₄ le_rfl ha)
  exact S.summable.norm

/-- The original global cutoff, six remainder and outer mode for the
prescribed test. Each positive chart contains its full Petersson,
Maaß and Eisenstein components. Each opposite chart uses the original
Maaß and Eisenstein components. -/
theorem original_six_spectrum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (x epsilon : ℝ) (L : ℕ) (ha : D.block.atom.residue≠0) :
    let J := globalCutoff D x epsilon
    (smoothSix D r:ℂ)=sixRemainder D r J+∑' ell : D4→ℤ,bothSix D r J ell := by
  let J := globalCutoff D x epsilon
  rw [original_six_opposite_spectrum D r x epsilon L ha]
  congr 1; apply tsum_congr; intro ell
  have c := D.cScale_pos
  have c2 : 0<2*D.cScale := mul_pos (by norm_num) c
  have c4 : 0<4*D.cScale := mul_pos (by norm_num) c
  simp only [sixSpectrum,bothSix,piece_eq D r ha J _ c ell,piece_eq D r ha J _ c2 ell,piece_eq D r ha J _ c4 ell]

end
end ImbalancedChen.Part3.OriginalBothSignsSixSpectrum20261112
