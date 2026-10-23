import ImbalancedChen.ActualThirdPrefixTailIntegralCore
import ImbalancedChen.ActualPrimeBoxOwnCubeResidual

/-!
# The canonical third-prefix correction and the actual tuple density profile

The noncompact canonical-kernel integral and its rounded-cap tail estimate are
proved in ActualThirdPrefixTailIntegralCore. This module supplies the exact
normalization, sign, reciprocal-coordinate density and own-cube identity with
the existing actual prime-tuple profile. The broader compact arithmetic-density
imports are needed only for that identification; they are not prerequisites for
compiling the canonical integral estimate.

This source does not identify an adopted measurable selector or assemble the
full physical upper coefficient. It is candidate source, not a compilation
receipt.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped BigOperators ENNReal

/-- The coordinates are in exactly the order used by the prime-tuple profile. -/
def thirdPrefixTuple (x y z : ℝ) : Fin 3 → ℝ := ![x, y, z]

/-- This fixes the normalization and the sign against the existing actual
own-cube profile, rather than defining an unrelated scalar kernel. -/
theorem thirdPrefixCorrectionKernel_eq_actualTupleProfile {old cap x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgate : x + y + 3 * z ≤ cap) (hlevels : cap ≤ old) :
    thirdPrefixCorrectionKernel old cap x y z =
      (primeTupleMinusProfile old (thirdPrefixTuple x y z) -
        primeTupleMinusProfile cap (thirdPrefixTuple x y z)) *
          ∏ i, 1 / thirdPrefixTuple x y z i := by
  have hlastval : thirdPrefixTuple x y z (Fin.last 2) = z := rfl
  have hsum : (∑ i, thirdPrefixTuple x y z i) = x + y + z := by
    simp [thirdPrefixTuple, Fin.sum_univ_succ] <;> ring
  have hprod : (∏ i, 1 / thirdPrefixTuple x y z i) = 1 / (x * y * z) := by
    simp [thirdPrefixTuple, Fin.prod_univ_succ]
    <;> field_simp [hx.ne', hy.ne', hz.ne']
    <;> ring
  have hlast : 0 < thirdPrefixTuple x y z (Fin.last 2) := by rwa [hlastval]
  have hg : primeTupleOwnCubeForm (thirdPrefixTuple x y z) ≤ cap := by
    unfold primeTupleOwnCubeForm
    rw [hsum, hlastval]
    linarith
  rw [primeTupleMinusProfile_of_ownCube hlast (hg.trans hlevels),
    primeTupleMinusProfile_of_ownCube hlast hg, hlastval, hsum, hprod]
  simp only [sub_add_eq_sub_sub]
  unfold thirdPrefixCorrectionKernel thirdTailLowerFactor
  rw [Real.exp_neg]
  field_simp [hx.ne', hy.ne', hz.ne',
    ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]
  <;> ring

end

end ImbalancedChen
