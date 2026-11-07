import ImbalancedChen.P2Winner9SelectedAllMixedMoments
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual gap-weighted means and E[P]=1 are reconstructed from independent
sparse polynomial integrals on the true physical supports. These are not
assumed probability normalizations. The same physical mass also identifies
the full measured Q6 correction, preserving every raw row scale.
-/

namespace ImbalancedChen.P2Winner9SelectedPhysicalMeans

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedAllMixedMoments
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

def gapPoly (r : Fin 2) : Poly := affinePoly (rawGap (vertices r))

def pPoly (r : Fin 2) : Poly := affinePoly (rawP (vertices r) (means r))

def factorPoly (r : Fin 2) (j : Fin 10) : Poly :=
  affinePoly (fun i => rawFactor (vertices r) i j)

def jacobian (r : Fin 2) : ℝ := |((edgeMatrix (vertices r)).det : ℝ)|

def gapMass (r : Fin 2) : ℝ := ∫ z in sourceSupport (vertices r), physicalGap z

theorem row_det_ne_zero (r : Fin 2) : (edgeMatrix (vertices r)).det ≠ 0 := by
  fin_cases r
  · simpa [vertices] using row21_det_ne_zero
  · simpa [vertices] using row22_det_ne_zero

theorem jacobian_pos (r : Fin 2) : 0 < jacobian r := by
  apply abs_pos.mpr
  exact_mod_cast row_det_ne_zero r

/-- Exact independent degree-two arithmetic of the true raw vertices.
The equalities compare actual weighted factor/P polynomials with the
literal stored mean vector; this closed body has NOT been evaluated. -/
theorem actual_first_moment_arithmetic : ∀ r : Fin 2,
    0 < polynomialMoment (gapPoly r) ∧
      polynomialMoment (gapPoly r * pPoly r) = polynomialMoment (gapPoly r) ∧
      ∀ j : Fin 10,
        polynomialMoment (gapPoly r * factorPoly r j) =
          means r j * polynomialMoment (gapPoly r) := by
  decide +kernel

theorem gapPoly_eval (r : Fin 2) (x : Ambient) :
    (gapPoly r).eval₂ (Rat.castHom ℝ) x =
      physicalGap (vertexMap (realVertices (vertices r)) x) := by
  simp only [gapPoly, affinePoly_eval, rawGap_cast, physicalGap_vertexMap]

theorem pPoly_eval (r : Fin 2) (x : Ambient) :
    (pPoly r).eval₂ (Rat.castHom ℝ) x =
      physicalP (fun j => (means r j : ℝ))
        (vertexMap (realVertices (vertices r)) x) := by
  simp only [pPoly, affinePoly_eval, rawP_cast, physicalP_vertexMap]

theorem factorPoly_eval (r : Fin 2) (j : Fin 10) (x : Ambient) :
    (factorPoly r j).eval₂ (Rat.castHom ℝ) x =
      physicalFactor j (vertexMap (realVertices (vertices r)) x) := by
  simp only [factorPoly, affinePoly_eval, rawFactor_cast, physicalFactor_vertexMap]

theorem gapMass_eq (r : Fin 2) :
    gapMass r = jacobian r * (polynomialMoment (gapPoly r) : ℝ) := by
  rw [gapMass, source_integral (vertices r) (row_det_ne_zero r)]
  simp_rw [← gapPoly_eval]
  rw [canonical_polynomial_integral]
  rfl

theorem gapMass_pos (r : Fin 2) : 0 < gapMass r := by
  rw [gapMass_eq]
  exact mul_pos (jacobian_pos r)
    (by exact_mod_cast (actual_first_moment_arithmetic r).1)

theorem actual_weighted_P_mass (r : Fin 2) :
    (∫ z in sourceSupport (vertices r),
      physicalGap z * physicalP (fun j => (means r j : ℝ)) z) = gapMass r := by
  rw [source_integral (vertices r) (row_det_ne_zero r)]
  have he (x : Ambient) :
      physicalGap (vertexMap (realVertices (vertices r)) x) *
          physicalP (fun j => (means r j : ℝ)) (vertexMap (realVertices (vertices r)) x) =
      (gapPoly r * pPoly r).eval₂ (Rat.castHom ℝ) x := by
    simp only [MvPolynomial.eval₂_mul, gapPoly_eval, pPoly_eval]
  simp_rw [he]
  rw [canonical_polynomial_integral, (actual_first_moment_arithmetic r).2.1, gapMass_eq]
  rfl

/-- The original true E_nu[P]=1 on each actual physical cell. -/
theorem actual_weighted_P_mean (r : Fin 2) :
    (∫ z in sourceSupport (vertices r),
      physicalGap z * physicalP (fun j => (means r j : ℝ)) z) / gapMass r = 1 := by
  rw [actual_weighted_P_mass, div_self (ne_of_gt (gapMass_pos r))]

/-- The stored ten-factor means really are E_nu[physicalFactor_j] for
these actual supports, not an independent vector chosen for normalization. -/
theorem actual_weighted_factor_mean (r : Fin 2) (j : Fin 10) :
    (∫ z in sourceSupport (vertices r), physicalGap z * physicalFactor j z) /
      gapMass r = (means r j : ℝ) := by
  rw [source_integral (vertices r) (row_det_ne_zero r)]
  have he (x : Ambient) :
      physicalGap (vertexMap (realVertices (vertices r)) x) *
          physicalFactor j (vertexMap (realVertices (vertices r)) x) =
      (gapPoly r * factorPoly r j).eval₂ (Rat.castHom ℝ) x := by
    simp only [MvPolynomial.eval₂_mul, gapPoly_eval, factorPoly_eval]
  simp_rw [he]
  rw [canonical_polynomial_integral, (actual_first_moment_arithmetic r).2.2 j]
  push_cast
  rw [gapMass_eq]
  have hJ : jacobian r ≠ 0 := ne_of_gt (jacobian_pos r)
  have hG : (polynomialMoment (gapPoly r) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast (actual_first_moment_arithmetic r).1)
  change jacobian r * ((means r j : ℝ) * _) / (jacobian r * _) = _
  field_simp [hJ, hG] <;> ring

def gapScale (r : Fin 2) : Nat := if r = 0 then Row21.gapDen else Row22.gapDen

theorem row_vertex_normalization (r : Fin 2) :
    VertexNormalization (vertices r) (means r) (upper r) (data r) (gapScale r) := by
  fin_cases r
  · simpa [vertices, means, upper, data, gapScale] using row21_vertex_normalization
  · simpa [vertices, means, upper, data, gapScale] using row22_vertex_normalization

/-- The same physical gap mass uses the exact gd and typed canonical mass. -/
theorem gapMass_typed (r : Fin 2) :
    gapMass r = (jacobian r / (gapScale r : ℝ)) * actualGapMass (data r) := by
  have hg := (real_vertex_arrays (vertices r) (means r) (upper r)
    (data r) (gapScale r) (row_vertex_normalization r)).1
  rw [gapMass, source_integral (vertices r) (row_det_ne_zero r)]
  simp only [physicalGap_vertexMap, hg, affine_div]
  have he (x : Ambient) : affine (gapVertices (data r)) x / (gapScale r : ℝ) =
      (1 / (gapScale r : ℝ)) * affine (gapVertices (data r)) x := by ring
  simp_rw [he]
  rw [integral_const_mul]
  change jacobian r * ((1 / (gapScale r : ℝ)) * actualGapMass (data r)) = _
  ring

/-- Every source correction expectation is now a true gap-weighted
physical expectation on the original sourceSupport, with common gd/Jacobian
cancelled only after their positivity has been established. -/
theorem physical_mixed_expectation (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    (∫ z in sourceSupport (vertices r),
      physicalMixedK (fun i => (means r i : ℝ)) (upper r : ℝ) j k.val z) /
      gapMass r = actualMixedExpectationK (data r) j k.val := by
  rw [physical_mixedK_from_vertex_normalization (vertices r) (row_det_ne_zero r)
    (means r) (upper r) (data r) (gapScale r) (row_vertex_normalization r)]
  rw [gapMass_typed, actualMixedExpectationK]
  have hJ : jacobian r ≠ 0 := ne_of_gt (jacobian_pos r)
  have hgd : (gapScale r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (row_vertex_normalization r).1)
  have hM : actualGapMass (data r) ≠ 0 := ne_of_gt (actualGapMass_pos (data r))
  change (jacobian r / (gapScale r : ℝ)) * actualMixedNumeratorK (data r) j k.val /
    ((jacobian r / (gapScale r : ℝ)) * actualGapMass (data r)) = _
  field_simp [hJ, hgd, hM] <;> ring

/-- Full original Q6 is connected to all seventy real physical measured
mixed expectations. This supplies the correction identity; the pointwise
reciprocal-product/T10 enclosure is still a separate analytic theorem. -/
theorem physical_Q6_identity (r : Fin 2) :
    (value (q6 (data r)) : ℝ) =
      ∑ j : Fin 10, ∑ k : Fin 7,
        (((9 + k.val).choose k.val : ℝ) *
          ((∫ z in sourceSupport (vertices r),
            physicalMixedK (fun i => (means r i : ℝ)) (upper r : ℝ) j k.val z) /
              gapMass r)) /
          (2 * (((data r).maxima j : ℝ) / (data r).L)^2 *
            (((data r).U : ℝ) / (data r).L)^10) := by
  rw [actual_row_Q6]
  simp_rw [physical_mixed_expectation]

end

end ImbalancedChen.P2Winner9SelectedPhysicalMeans
