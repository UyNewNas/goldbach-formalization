import ImbalancedChen.P2Winner9MixedZeroCoefficientCurvatureLink
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is the k=1 finite polynomial normalization of the pinned mixed
generating-function identity (M). It expands the signed coefficient one
degree beyond the k=0 curvature term and normalizes its exact rational
correction to the source's binomial and rising-factorial expression.
No final mixed moment identity is assumed as an input.

The actual measure statement E_nu[Y*b_j^2] = the rational candidate here
requires the dimension-eight canonical simplex monomial integral through
degree four, followed by the affine Jacobian and gap-weighted mixture.
That integral primitive is not proved in this source. No producer, checker,
Lean kernel or numerical replay ran, and no physical cap or row is certified.
-/

namespace ImbalancedChen.P2Winner9MixedDegreeOnePolynomialMoment

open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
open ImbalancedChen.P2Winner9MixedZeroCoefficientCurvatureLink

/-- Degree-one convolution uses precisely the two coefficient pairs. -/
theorem conv_one (a b : Nat → ℤ) :
    conv a b 1 = a 0 * b 1 + a 1 * b 0 := by
  simp [conv]

/-- Expand the signed mixed generating-function coefficient at t¹.
No positivity of B1, W1 or the intermediate signed convolutions is used. -/
theorem doubled_one (d : SimplexData) (j : Fin 10) :
    doubled d j 1 =
      2 * W2 d j 1 +
      2 * (B1 d j 0 * W1 d j 1 + B1 d j 1 * W1 d j 0) +
      ((B1 d j 0)^2 + B2 d j 0) * W0 d 1 +
      (2 * B1 d j 0 * B1 d j 1 + B2 d j 1) * W0 d 0 := by
  simp [doubled, conv_one, conv_zero]
  ring

/-- The complete-homogeneous factor contributes its constant and linear
coefficients; the constant coefficient is the D2 term from Phase13. -/
theorem mixed_numerator_one (d : SimplexData) (j : Fin 10) :
    mixedNumerator d j 1 =
      doubled d j 1 + homogeneous d.y 1 * doubled d j 0 := by
  simp [mixedNumerator, conv_one, homogeneous_zero]
  ring

/-- Exact signed rational candidate for E_nu[Y*b_j²] at k=1, with the
unreduced vertex scales `Y_i=y_i/U`, `b_i=deviation_i/L` and total
Dirichlet parameter ten. The moment/integral equality is still open. -/
def momentOneCandidate (d : SimplexData) (j : Fin 10) : ℚ :=
  (mixedNumerator d j 1 : ℚ) /
    ((gapTotal d.gaps : ℚ) * d.U * d.L^2 * (10 * 11 * 12))

/-- The source correction factor at k=1 is `choose(10,1)` times the
candidate moment, divided by `2 V_j² U_phys^10`. Exact cancellation
matches the Phase12 per-factor degree-one fraction. -/
theorem mixed_degree_one_fraction_normalization
    (d : SimplexData) (j : Fin 10) :
    value (mixedTerm d j (1 : Fin 7)) =
      10 * momentOneCandidate d j /
        (2 * ((d.maxima j : ℚ) / d.L)^2 *
          ((d.U : ℚ) / d.L)^10) := by
  have hG : (gapTotal d.gaps : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt d.gapsPos)
  have hU : (d.U : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.UPos)
  have hL : (d.L : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.LPos)
  have hv : (d.maxima j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (d.maximaPos j))
  unfold momentOneCandidate value mixedTerm
    mixedTermNumerator mixedTermDenominator
  push_cast
  field_simp [hG, hU, hL, hv]
  ring

end ImbalancedChen.P2Winner9MixedDegreeOnePolynomialMoment
