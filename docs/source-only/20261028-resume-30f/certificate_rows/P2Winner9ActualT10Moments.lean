import ImbalancedChen.P2Winner9T10TailJensen
import ImbalancedChen.P2Winner9SelectedPhysicalMeans
import ImbalancedChen.P2Winner9SelectedPhysicalQ6Floor
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual T10 source expression is connected to independent real physical
power moments. Closed finite polynomial coefficient comparisons are only
source proposals, and are not executed here. The original literal Jensen
factor is also bound to the actual physical mass and true stored means.
-/

namespace ImbalancedChen.P2Winner9ActualT10Moments

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedAllMixedMoments
open ImbalancedChen.P2Winner9SelectedPhysicalMeans
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly

def yPoly (r : Fin 2) : Poly := affinePoly (rawY (vertices r) (means r) (upper r))

def powerPoly (r : Fin 2) (k : Nat) : Poly := gapPoly r * (yPoly r)^k

def physicalPowerMean (r : Fin 2) (k : Nat) : ℝ :=
  (∫ z in sourceSupport (vertices r),
    physicalGap z * (physicalY (fun j => (means r j : ℝ)) (upper r : ℝ) z)^k) /
      gapMass r

def storedJacobian (r : Fin 2) : ℚ :=
  (8.factorial : ℚ) * (if r = 0 then P2Winner9Row21RawVertexData.physicalVolume else row22Volume)

/-- Independent source comparisons for all power moments through10,
retaining the actual physical gap and Y polynomials. NOT EXECUTED. -/
theorem actual_T10_arithmetic : ∀ r : Fin 2,
    value (t10 (data r)) = (1 / (upper r)^10) *
      (∑ k ∈ Finset.range 11, ((9 + k).choose k : ℚ) *
        (polynomialMoment (powerPoly r k) / polynomialMoment (gapPoly r) -
          (polynomialMoment (powerPoly r 1) / polynomialMoment (gapPoly r))^k)) ∧
      polynomialMoment (powerPoly r 1) / polynomialMoment (gapPoly r) =
        1 - 1 / upper r ∧
      ((data r).jensenNum : ℚ) / (data r).jensenDen =
        4 * storedJacobian r * polynomialMoment (gapPoly r) /
          ∏ j : Fin 10, means r j := by
  decide +kernel

theorem yPoly_eval (r : Fin 2) (x : Ambient) :
    (yPoly r).eval₂ (Rat.castHom ℝ) x =
      physicalY (fun j => (means r j : ℝ)) (upper r : ℝ)
        (vertexMap (realVertices (vertices r)) x) := by
  simp only [yPoly, affinePoly_eval, rawY_cast, physicalY_vertexMap]

theorem physicalPowerMean_eq (r : Fin 2) (k : Nat) :
    physicalPowerMean r k =
      ((polynomialMoment (powerPoly r k) / polynomialMoment (gapPoly r) : ℚ) : ℝ) := by
  rw [physicalPowerMean, source_integral (vertices r) (row_det_ne_zero r)]
  have he (x : Ambient) :
      physicalGap (vertexMap (realVertices (vertices r)) x) *
        (physicalY (fun j => (means r j : ℝ)) (upper r : ℝ)
          (vertexMap (realVertices (vertices r)) x))^k =
      (powerPoly r k).eval₂ (Rat.castHom ℝ) x := by
    simp only [powerPoly, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
      gapPoly_eval, yPoly_eval]
  simp_rw [he]
  rw [canonical_polynomial_integral, gapMass_eq]
  have hJ : jacobian r ≠ 0 := ne_of_gt (jacobian_pos r)
  have hG : (polynomialMoment (gapPoly r) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast (actual_first_moment_arithmetic r).1)
  change jacobian r * _ / (jacobian r * _) = _
  push_cast
  field_simp [hJ, hG] <;> ring

/-- Genuine physical T10 as a Jensen-GAP of measured powers, not merely
a pointwise binomial sum. Degrees0/1 are included and cancel exactly. -/
theorem actual_T10_identity (r : Fin 2) :
    (value (t10 (data r)) : ℝ) = (1 / (upper r : ℝ)^10) *
      (∑ k ∈ Finset.range 11, ((9 + k).choose k : ℝ) *
        (physicalPowerMean r k - (physicalPowerMean r 1)^k)) := by
  simp_rw [physicalPowerMean_eq]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (actual_T10_arithmetic r).1
  push_cast at h ⊢
  exact h

theorem actual_Y_mean (r : Fin 2) :
    physicalPowerMean r 1 = 1 - 1 / (upper r : ℝ) := by
  rw [physicalPowerMean_eq]
  exact_mod_cast (actual_T10_arithmetic r).2.1

theorem jacobian_eq_stored (r : Fin 2) : jacobian r = (storedJacobian r : ℝ) := by
  fin_cases r
  · simpa [jacobian, vertices, storedJacobian] using
      (show |((edgeMatrix row21).det : ℝ)| =
        (((8.factorial : ℚ) * P2Winner9Row21RawVertexData.physicalVolume : ℚ) : ℝ) from
        by exact_mod_cast row21_abs_det_volume)
  · simpa [jacobian, vertices, storedJacobian] using
      (show |((edgeMatrix row22).det : ℝ)| =
        (((8.factorial : ℚ) * row22Volume : ℚ) : ℝ) from
        by exact_mod_cast row22_abs_det_volume)

/-- Literal reconstructed J_T is now the true mass/mean-product factor. -/
theorem actual_Jensen_factor (r : Fin 2) :
    ((data r).jensenNum : ℝ) / (data r).jensenDen =
      4 * gapMass r / ∏ j : Fin 10, (means r j : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (actual_T10_arithmetic r).2.2
  push_cast at h
  rw [gapMass_eq, jacobian_eq_stored]
  convert h using 1 <;> ring

end

end ImbalancedChen.P2Winner9ActualT10Moments
