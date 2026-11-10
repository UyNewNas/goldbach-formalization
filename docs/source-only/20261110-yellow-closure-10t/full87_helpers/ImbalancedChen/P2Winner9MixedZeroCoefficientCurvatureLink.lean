import ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is the finite k=0 coefficient normalization of the pinned mixed
generating-function formula (M). The mixed signed numerator reduces to
the D2 signed numerator for the SAME ten-factor simplex, and its exact
fraction denominator reduces to the already used curvature Q0 denominator.
Thus Q0 is present inside Q6; it cannot be a separately added saving.

The Dirichlet mixture/integral identity for all k=0..6 is not proved here.
The exact physical vertices, cap and enclosure, all source rows, and the
kernel evaluation of these source-only proofs remain separate.
-/

namespace ImbalancedChen.P2Winner9MixedZeroCoefficientCurvatureLink

open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

/-- At degree zero, coefficient convolution selects its constant terms. -/
theorem conv_zero (a b : Nat → ℤ) :
    conv a b 0 = a 0 * b 0 := by
  simp [conv]

/-- The complete homogeneous constant coefficient is one, for any nine
integer vertex values. This is a finite polynomial normalization. -/
theorem homogeneous_zero (y : Fin 9 → Nat) :
    homogeneous y 0 = 1 := by
  classical
  simp [homogeneous]

/-- Direct polynomial identity for the u² coefficient at t⁰. Signed b_i
are retained; no covariance or individual mixed coefficient sign is used. -/
theorem signed_zero_coefficient_identity
    (g : Fin 9 → Nat) (b : Fin 9 → ℤ) :
    2 * (∑ i : Fin 9, (g i : ℤ) * (b i)^2) +
      2 * (∑ i : Fin 9, b i) *
        (∑ i : Fin 9, (g i : ℤ) * b i) +
      ((∑ i : Fin 9, b i)^2 +
        (∑ i : Fin 9, (b i)^2)) * (gapTotal g : ℤ) =
      signedMomentNumerator g b := by
  dsimp [signedMomentNumerator]
  ring

/-- The Phase12 signed generating-function coefficient at k=0 is exactly
the Phase9 D2 numerator, factor by factor on the same simplex. -/
theorem mixed_numerator_zero (d : SimplexData) (j : Fin 10) :
    mixedNumerator d j 0 =
      signedMomentNumerator d.gaps (d.deviations j) := by
  simp [mixedNumerator, doubled, conv_zero, homogeneous_zero,
    B1, B2, W0, W1, W2, signedMomentNumerator, gapTotal]
  ring

/-- At k=0 the exact mixed denominator is the exact curvature Q0
denominator, including the common `U^10` factor. -/
theorem mixed_denominator_zero (d : SimplexData) (j : Fin 10) :
    mixedTermDenominator d j 0 =
      curvatureDenominator d.gaps d.U (d.maxima j) := by
  simp [mixedTermDenominator, curvatureDenominator]
  ring

theorem mixed_numerator_fraction_zero (d : SimplexData) (j : Fin 10) :
    mixedTermNumerator d j 0 =
      curvatureNumerator d.gaps (d.deviations j) d.L := by
  simp [mixedTermNumerator, curvatureNumerator, mixed_numerator_zero]

/-- Exact k=0 mixed factor fraction equals the curvature factor fraction.
This is an equality of rationals, not merely of printed Q80 floors. -/
theorem mixed_term_zero_eq_curvature (d : SimplexData) (j : Fin 10) :
    value (mixedTerm d j (0 : Fin 7)) =
      (curvatureNumerator d.gaps (d.deviations j) d.L : ℚ) /
        curvatureDenominator d.gaps d.U (d.maxima j) := by
  simp [value, mixedTerm, mixed_numerator_fraction_zero,
    mixed_denominator_zero]

/-- The selected mixed floor replaces the current curvature maximum.
The old log floor is subtracted once, even when the k=0 component recurs
inside Q6. -/
theorem same_simplex_chronological_increment
    (logFloor curvatureRaw mixedRaw : Nat) :
    let curvatureSelected := max logFloor curvatureRaw
    let mixedSelected := max curvatureSelected mixedRaw
    ((mixedSelected : ℤ) - logFloor) =
      ((curvatureSelected : ℤ) - logFloor) +
        ((mixedSelected : ℤ) - curvatureSelected) := by
  dsimp
  ring

end ImbalancedChen.P2Winner9MixedZeroCoefficientCurvatureLink
