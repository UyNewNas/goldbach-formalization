import ImbalancedChen.Part3OriginalPositiveStrip
import ImbalancedChen.Part3ActualPositiveHolomorphicDiagonal

/-! The zero ordinate of the residual density is exactly the original Petersson
identity term. The indicator for equal cusp and equal index stays on the trace side. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStrip20261112
open Set MeasureTheory Complex
open scoped BigOperators ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment positive_holomorphic_diagonal)
open OriginalPositiveJacobiAnger20261112 (oddOrder)
open OriginalPositiveStripMoments20261112 (coeff sign m)
open OriginalPositiveStripDensity20261112 (tail h_formula)
open private h_smooth from ImbalancedChen.Part3OriginalPositiveStripDensity

theorem smooth (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : ContDiff ℝ ∞ (h ell Y) := h_smooth ell hY

theorem half_at_zero (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    h ell Y 0/2=diagonalMoment 0 (spectralTest ell Y)/(2*(Real.pi:ℂ)) := by
  have D := (positive_holomorphic_diagonal ell hY).div_const 4
  have T : tail ell Y 1 0=(-2*diagonalMoment 0 (spectralTest ell Y))/4 := by
    unfold tail
    apply (D.congr_fun _).tsum_eq
    intro j
    simp only [coeff,m,sign,holWeight,oddOrder,pow_mul,I_sq,pow_succ,pow_one,
      mul_zero,Complex.exp_zero,mul_one]
    ring
  rw [h_formula ell hY,T,Real.sinh_zero,Complex.ofReal_zero,zero_mul]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
end ImbalancedChen.Part3.OriginalPositiveStrip20261112
end
