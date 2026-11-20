import ImbalancedChen.Part3OriginalSignedExceptionalChart
import ImbalancedChen.Part3OriginalPrescribedChartSpectrum

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Restore the original physical chart scalar, actual test scale and the
two signed original Fourier coefficients on the finite exceptional part.
-/
noncomputable section
namespace ImbalancedChen.Part3.OriginalSignedExceptionalMode20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels pascadiJ)
open OriginalExceptionalPostRemovalPair20261113 (levels Slots rowMass rowLength)
open OriginalSignedExceptionalChart20261120 (signedRawSlot signed_chart_with_raw_sieve)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)

/-- The finite strict-exceptional part with the original Fourier
coefficient, chart scalar and actual positive chart test scale. -/
def signedExceptionalMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell *
    (((M*Real.sqrt (fixedZ D upper):ℝ):ℂ) *
      ∑ a : Slots D k upper, signedRawSlot D r k upper negativeM J j ell
        (chartY0 D k upper j N) a)

/-- One actual chart, both original Poisson signs and their distinct
Fourier coefficients, with one m-side phase for both signs. -/
theorem signed_exceptional_two_modes (D : OriginalData) (k : BlockKey)
    (upper : Bool) (J j : ℕ) (M : ℝ) {N : ℝ} (hN : 0 < N)
    (ell : D4 → ℤ) (ha : D.block.atom.residue ≠ 0) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
    let W := threshold V Z
    ∃ B : ℝ, 0 ≤ B ∧ ∃ ω : ℝ, ∀ (r : ZMod (prefixPeriod D.key)),
      ‖signedExceptionalMode D r k upper false J j M N ell +
        signedExceptionalMode D r k upper true J j M N ell‖^2 ≤
      2 * (‖actualCoeff ((2^j:ℕ)*M/N) 1 ell‖^2 +
        ‖actualCoeff ((2^j:ℕ)*M/N) (-1) ell‖^2) *
        ((M^2*Z) * (B^2 * (((2+Real.log (4*V+1))^2 *
          ((pascadiJ (classicalLevels (Z/2)) W j ω +
            pascadiJ (classicalLevels Z) W j ω)/4)) *
          ((2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/Z)) *
            ∑ z : ↥(levels D k upper), rowMass D r k z.val)))) := by
  classical
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  let Y := chartY0 D k upper j N
  have hZ : 0 < Z := fixedZ_pos D upper
  have hY : 0 < Y := original_spectral_scale_pos D k upper j hN ha
  obtain ⟨B,hB,hchart⟩ := signed_chart_with_raw_sieve ell hY
  obtain ⟨ω,hω⟩ := hchart D k upper J j ha
  refine ⟨B,hB,ω,?_⟩
  intro r
  let coeff (b : Bool) : ℂ := actualCoeff ((2^j:ℕ)*M/N) (if b then -1 else 1) ell
  let R (b : Bool) : ℂ := signedExceptionalMode D r k upper b J j M N ell
  let Jprice : ℝ := (2+Real.log (4*V+1))^2 *
    ((pascadiJ (classicalLevels (Z/2)) W j ω + pascadiJ (classicalLevels Z) W j ω)/4)
  let Nprice : ℝ := (2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/Z)) *
    ∑ z : ↥(levels D k upper), rowMass D r k z.val
  let P : ℝ := B^2 * (Jprice*Nprice)
  let Q : ℝ := (M^2*Z)*P
  have hscale : ‖((M*Real.sqrt Z:ℝ):ℂ)‖^2 = M^2*Z := by
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,Real.sq_sqrt hZ.le]
  have each (b : Bool) : ‖R b‖^2 ≤ ‖coeff b‖^2 * Q := by
    let S : ℂ := ∑ a : Slots D k upper, signedRawSlot D r k upper b J j ell Y a
    have hn : ‖S‖ ≤ ∑ a : Slots D k upper, ‖signedRawSlot D r k upper b J j ell Y a‖ := by
      exact norm_sum_le _ _
    have hs := pow_le_pow_left₀ (norm_nonneg S) hn 2
    have hspec : ‖S‖^2 ≤ P := hs.trans (hω r b)
    have hfactor : 0 ≤ ‖coeff b‖^2 * (M^2*Z) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hZ.le)
    calc
      _ = ‖coeff b‖^2 * (M^2*Z) * ‖S‖^2 := by
        dsimp only [R,signedExceptionalMode,coeff,S,Y,Z]
        rw [norm_mul,norm_mul,mul_pow,mul_pow,hscale]
        ring
      _ ≤ ‖coeff b‖^2 * (M^2*Z) * P := mul_le_mul_of_nonneg_left hspec hfactor
      _ = _ := by dsimp [Q]; ring
  have htri : ‖R false+R true‖ ≤ ‖R false‖+‖R true‖ := norm_add_le _ _
  have ht := pow_le_pow_left₀ (norm_nonneg (R false+R true)) htri 2
  have htwo : (‖R false‖+‖R true‖)^2 ≤ 2*(‖R false‖^2+‖R true‖^2) := by
    nlinarith only [sq_nonneg (‖R false‖-‖R true‖)]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (each false) (each true)) (by norm_num : (0:ℝ) ≤ 2)
  calc
    _ ≤ (‖R false‖+‖R true‖)^2 := ht
    _ ≤ 2*(‖R false‖^2+‖R true‖^2) := htwo
    _ ≤ 2*(‖coeff false‖^2*Q+‖coeff true‖^2*Q) := hsum
    _ = _ := by simp only [coeff,Bool.false_eq_true,if_false,if_true,Q,P,Jprice,Nprice,Z,V,W]; ring

end ImbalancedChen.Part3.OriginalSignedExceptionalMode20261120
end
