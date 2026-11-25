import Mathlib.Data.Rat.Floor

/-!
SOURCE ONLY / NOT COMPILED.

The original saving16 Q96 floor definition is moved here unchanged, in its
original namespace and noncomputable section context. The analytic Jensen
owner imports this module and retains all its original floor-transport
proofs. This file introduces no new mathematical assertion.
-/
namespace ImbalancedChen.P2OriginalSaving16JensenFloor

noncomputable section

/-- Exact Python operation `bound.numerator * 2**96 // bound.denominator`.
This is integer floor division, including its sign convention. -/
def q96Floor (q : ℚ) : ℤ := (q.num * (2 ^ 96 : ℤ)) / q.den

end
end ImbalancedChen.P2OriginalSaving16JensenFloor
