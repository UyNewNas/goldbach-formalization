import ImbalancedChen.Part3OriginalOppositeChartSplit

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Reassemble the two literal physical Z charts into the original opposite
block, retaining the exceptional, cusp complement and continuous terms. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalOppositeBlockSplit20261120
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalPrescribedChartSpectrum20261112
  (oppositeBlockSpectrum full_block_opposite_spectrum full_chart_opposite_spectrum)
open OriginalSignedExceptionalMode20261120 (signedExceptionalMode)
open OriginalOppositeChartSplit20261120
  (oppositeComplementMode oppositeContinuousMode opposite_chart_split)

/-- Both physical Z charts' finite strict exceptional terms. -/
def blockExceptional (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  signedExceptionalMode D r k false negativeM J j M N ell +
    signedExceptionalMode D r k true negativeM J j M N ell

/-- The two physical charts' native cuspidal complements. -/
def blockCuspComplement (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  oppositeComplementMode D r k false negativeM J j M N ell +
    oppositeComplementMode D r k true negativeM J j M N ell

/-- The two original continuous spectral integrals, with their separate
chart test scales and physical scalars. -/
def blockContinuous (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  oppositeContinuousMode D r k false negativeM J j M N ell +
    oppositeContinuousMode D r k true negativeM J j M N ell

/-- At the actual opposite composite trace sign, the original full block
is exactly the sum of its two-chart exceptional, complement and
continuous contributions. -/
theorem opposite_block_split (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (negativeM : Bool) (J j : ℕ) (M : ℝ) {N : ℝ}
    (ell : D4 → ℤ) (hN : 0 < N) (ha : D.block.atom.residue ≠ 0)
    (hs : traceNegative D k negativeM = true) :
    fullBlockMode D r k J j negativeM M N ell =
      blockExceptional D r k negativeM J j M N ell +
      blockCuspComplement D r k negativeM J j M N ell +
      blockContinuous D r k negativeM J j M N ell := by
  rw [full_block_opposite_spectrum D r k ha J j negativeM hs M hN ell,
    oppositeBlockSpectrum,
    ← full_chart_opposite_spectrum D r k ha false negativeM hs J j ell M hN,
    ← full_chart_opposite_spectrum D r k ha true negativeM hs J j ell M hN,
    mul_add,
    opposite_chart_split D r k false negativeM J j M ell hN ha hs,
    opposite_chart_split D r k true negativeM J j M ell hN ha hs]
  simp only [blockExceptional,blockCuspComplement,blockContinuous]
  ring

/-- A squared-norm reduction for the original block, leaving the three
contributions explicit for their distinct analytic estimates. -/
theorem opposite_block_sq_le_parts (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (negativeM : Bool) (J j : ℕ) (M : ℝ) {N : ℝ}
    (ell : D4 → ℤ) (hN : 0 < N) (ha : D.block.atom.residue ≠ 0)
    (hs : traceNegative D k negativeM = true) :
    ‖fullBlockMode D r k J j negativeM M N ell‖^2 ≤
      3 * (‖blockExceptional D r k negativeM J j M N ell‖^2 +
        ‖blockCuspComplement D r k negativeM J j M N ell‖^2 +
        ‖blockContinuous D r k negativeM J j M N ell‖^2) := by
  rw [opposite_block_split D r k negativeM J j M ell hN ha hs]
  let E := blockExceptional D r k negativeM J j M N ell
  let R := blockCuspComplement D r k negativeM J j M N ell
  let C := blockContinuous D r k negativeM J j M N ell
  have ht : ‖E+R+C‖ ≤ ‖E‖+‖R‖+‖C‖ :=
    (norm_add_le (E+R) C).trans (add_le_add_right (norm_add_le E R) ‖C‖)
  have hsquare := pow_le_pow_left₀ (norm_nonneg (E+R+C)) ht 2
  have hthree : (‖E‖+‖R‖+‖C‖)^2 ≤ 3*(‖E‖^2+‖R‖^2+‖C‖^2) := by
    nlinarith only [sq_nonneg (‖E‖-‖R‖),sq_nonneg (‖R‖-‖C‖),
      sq_nonneg (‖C‖-‖E‖)]
  exact hsquare.trans hthree

end ImbalancedChen.Part3.OriginalOppositeBlockSplit20261120
end
