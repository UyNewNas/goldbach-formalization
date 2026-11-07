import ImbalancedChen.P5ZU1011OriginalSixteenWalls

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Every actual selected/W residual query has a proper affine equality wall,
for every real query coefficient. In particular this includes knot50 at2,
the open-cell endpoints and exterior cutoff5. Properness of the equality
L=2w does not identify the whole clamp half-space L<=2w as a null set.
-/
namespace ImbalancedChen.P5Z.U1011OriginalSixteenResidualWalls

noncomputable section

open Set
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenWalls

def queryGate (p : Policy) (left : Bool) (q : ℝ) : LogFour →L[ℝ] ℝ :=
  capLinear p left - sumLinear - q • ContinuousLinearMap.proj 3

/-- The query coefficient multiplies coordinate3, so evaluation at the
actual coordinate0 basis leaves cap coefficients0,1/2,-3/2 minus1.
The distinct W branch leaves-1. None of these values can vanish. -/
theorem queryGate_ne_zero (p : Policy) (left : Bool) (q : ℝ) :
    queryGate p left q ≠ 0 := by
  intro hz
  have he := congrArg (fun F : LogFour →L[ℝ] ℝ => F (basis 0)) hz
  simp only [queryGate, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
    sumLinear_basis, capLinear_basis] at he
  norm_num [basis] at he
  split_ifs at he <;> norm_num at he

theorem queryGate_eq_dictionary (p : Policy) (left : Bool) (q : ℝ) (v : LogFour)
    (hbranch : cap p v = affineCap p left v) :
    typedResidual p v = q * v 3 ↔ queryGate p left q v = -capOffset p left := by
  simp only [typedResidual, hbranch, affineCap, queryGate, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    sumLinear_apply]
  linarith

theorem queryGate_lt_dictionary (p : Policy) (left : Bool) (q : ℝ) (v : LogFour)
    (hbranch : cap p v = affineCap p left v) :
    typedResidual p v < q * v 3 ↔ queryGate p left q v < -capOffset p left := by
  simp only [typedResidual, hbranch, affineCap, queryGate, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    sumLinear_apply]
  linarith

theorem queryGate_le_dictionary (p : Policy) (left : Bool) (q : ℝ) (v : LogFour)
    (hbranch : cap p v = affineCap p left v) :
    typedResidual p v ≤ q * v 3 ↔ queryGate p left q v ≤ -capOffset p left := by
  simp only [typedResidual, hbranch, affineCap, queryGate, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    sumLinear_apply]
  linarith

end
end ImbalancedChen.P5Z.U1011OriginalSixteenResidualWalls
