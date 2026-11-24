import ImbalancedChen.P2Winner9MixedKOneFiniteCollapse
import ImbalancedChen.P2Winner9PhysicalVertexInterpolation

/-! The canonical gap-weighted deviation square, with the exact signed
numerator used by the original curvature certificate. -/
namespace ImbalancedChen.P2Winner9CanonicalCurvatureMoment

noncomputable section

open MeasureTheory
open P2Winner9BarycentricMixedDegreeOne
open P2Winner9CurvatureExactMomentFloor
open P2Winner9CurvatureFullExactAssembly
open P2Winner9MixedDegreeOnePolynomialMoment
open P2Winner9MixedDegreeSixExactAssembly
open P2Winner9MixedKOneFiniteCollapse
open P2Winner9MixedZeroCoefficientCurvatureLink
open P2Winner9PhysicalVertexInterpolation (affine_constant)
open P2Winner9SimplexCoordinateSlice (standardSimplex)
open scoped BigOperators

private def constantOneY (d : SimplexData) : SimplexData :=
  { d with y := fun _ => 1, U := 1, UPos := by decide }

private theorem constantOneY_mixedNumerator (d : SimplexData) (j : Fin 10) :
    mixedNumerator (constantOneY d) j 1 =
      12 * signedMomentNumerator d.gaps (d.deviations j) := by
  rw [mixed_numerator_one, doubled_one, homogeneous_one]
  norm_num [constantOneY, doubled, conv_zero, B1, B2, W0, W1, W2, Nat.choose,
    signedMomentNumerator, gapTotal]
  ring

/-- The actual Lebesgue expectation of the squared signed deviation,
under the normalized canonical gap weight. -/
theorem actualWeightedDeviationSquare_eq (d : SimplexData) (j : Fin 10) :
    (∫ x in standardSimplex 8 (1 : ℝ),
      affine (gapVertices d) x * (affine (bVertices d j) x)^2) / actualGapMass d =
      (signedMomentNumerator d.gaps (d.deviations j) : ℝ) /
        (110 * (gapTotal d.gaps : ℝ) * (d.L : ℝ)^2) := by
  have hgap : gapVertices (constantOneY d) = gapVertices d := rfl
  have hdev : bVertices (constantOneY d) j = bVertices d j := rfl
  have hy : yVertices (constantOneY d) = fun _ => 1 := by
    funext i
    norm_num [yVertices, constantOneY]
  calc
    _ = actualMixedExpectation (constantOneY d) j := by
      simp only [actualMixedExpectation, actualMixedNumerator, actualGapMass,
        hgap, hdev, hy, affine_constant, mul_one]
    _ = _ := by
      rw [actualMixedExpectation_eq_candidate, constantOneY_mixedNumerator]
      have hden : (gapTotal d.gaps : ℝ) * 1 * (d.L : ℝ)^2 * (10 * 11 * 12) =
          12 * (110 * (gapTotal d.gaps : ℝ) * (d.L : ℝ)^2) := by ring
      simp only [constantOneY, Nat.cast_one]
      rw [hden, Int.cast_mul]
      exact mul_div_mul_left _ _ (by norm_num : (12 : ℝ) ≠ 0)

end

end ImbalancedChen.P2Winner9CanonicalCurvatureMoment
