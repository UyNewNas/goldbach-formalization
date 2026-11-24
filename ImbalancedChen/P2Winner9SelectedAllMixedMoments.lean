import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The real measured polynomial integral is first proved from the actual Δ8
monomial theorem for every rational sparse polynomial. The source's mixed
convolution is a separate arithmetic object: two closed finite identities
compare it with the independently expanded sparse polynomial for k=0..6.
Those arithmetic proof bodies have NOT been evaluated. The concrete real
moment formulas then have no assumed mixed-moment or enclosure hypothesis.
-/

namespace ImbalancedChen.P2Winner9SelectedAllMixedMoments

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9NestedEightSimplexMoment
open ImbalancedChen.P2Winner9ActualEightSimplexMoment
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

abbrev Poly := MvPolynomial (Fin 8) ℚ

def rationalMonomialMoment (e : Fin 8 →₀ Nat) : ℚ :=
  (factorialProduct (List.ofFn fun i : Fin 8 => e i) : ℚ) /
    (((List.ofFn fun i : Fin 8 => e i).sum + 8).factorial : ℚ)

/-- Exact rational simplex integration of an independently represented
sparse polynomial, not the mixed source's generating-function formula. -/
def polynomialMoment (p : Poly) : ℚ :=
  ∑ e ∈ p.support, p.coeff e * rationalMonomialMoment e

theorem canonical_monomial_integral (e : Fin 8 →₀ Nat) :
    (∫ x in canonicalSupport, ∏ i : Fin 8, (x i)^(e i)) =
      (rationalMonomialMoment e : ℝ) := by
  have h := actual_eight_factorial 0 (fun i : Fin 8 => e i)
    (s := (1 : ℝ)) (by norm_num)
  simpa [P2Winner9NestedEightSimplexMoment.actualMoment, canonicalSupport,
    P2Winner9SimplexCoordinateSlice.standardSimplex_eight,
    rationalMonomialMoment] using h

/-- This is the actual measured Δ8 polynomial law, proved by a finite
sum of genuine monomial integrals and compact polynomial integrability. -/
theorem canonical_polynomial_integral (p : Poly) :
    (∫ x in canonicalSupport, p.eval₂ (Rat.castHom ℝ) x) =
      (polynomialMoment p : ℝ) := by
  classical
  have hi (e : Fin 8 →₀ Nat) : IntegrableOn
      (fun x : Ambient => (p.coeff e : ℝ) * ∏ i : Fin 8, (x i)^(e i))
      canonicalSupport := by
    apply ContinuousOn.integrableOn_compact _ canonicalSupport_compact
    fun_prop
  have he : (fun x : Ambient => p.eval₂ (Rat.castHom ℝ) x) =
      (fun x => ∑ e ∈ p.support,
        (p.coeff e : ℝ) * ∏ i : Fin 8, (x i)^(e i)) := by
    funext x
    exact MvPolynomial.eval₂_eq' (Rat.castHom ℝ) x p
  rw [he, integral_finsetSum p.support (fun e _ => hi e)]
  simp_rw [integral_const_mul, canonical_monomial_integral]
  simp [polynomialMoment]

def barycentricPoly (i : Fin 9) : Poly :=
  Fin.cases (1 - ∑ j : Fin 8, MvPolynomial.X j)
    (fun j : Fin 8 => MvPolynomial.X j) i

def affinePoly (v : Fin 9 → ℚ) : Poly :=
  ∑ i : Fin 9, MvPolynomial.C (v i) * barycentricPoly i

theorem barycentricPoly_eval (i : Fin 9) (x : Ambient) :
    (barycentricPoly i).eval₂ (Rat.castHom ℝ) x = barycentric i x := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [barycentricPoly, barycentric]
  · simp [barycentricPoly, barycentric]

theorem affinePoly_eval (v : Fin 9 → ℚ) (x : Ambient) :
    (affinePoly v).eval₂ (Rat.castHom ℝ) x = affine (fun i => (v i : ℝ)) x := by
  simp [affinePoly, affine, barycentricPoly_eval]

/-- Unnormalized integer vertex polynomial. Coefficients are expanded
in the eight true canonical coordinates; the signed deviation is squared
without changing its intermediate coefficients to nonnegative integers. -/
def integerMixedPolynomial (d : SimplexData) (j : Fin 10) (k : Nat) : Poly :=
  affinePoly (fun i => (d.gaps i : ℚ)) *
    (affinePoly (fun i => (d.y i : ℚ)))^k *
    (affinePoly (fun i => (d.deviations j i : ℚ)))^2

def actualMixedNumeratorK (d : SimplexData) (j : Fin 10) (k : Nat) : ℝ :=
  ∫ x in canonicalSupport, affine (gapVertices d) x *
    (affine (yVertices d) x)^k * (affine (bVertices d j) x)^2

theorem actualMixedNumeratorK_polynomial (d : SimplexData) (j : Fin 10)
    (k : Nat) :
    actualMixedNumeratorK d j k =
      (polynomialMoment (integerMixedPolynomial d j k) : ℝ) /
        ((d.U : ℝ)^k * (d.L : ℝ)^2) := by
  have he (x : Ambient) :
      affine (gapVertices d) x * (affine (yVertices d) x)^k *
          (affine (bVertices d j) x)^2 =
      (1 / ((d.U : ℝ)^k * (d.L : ℝ)^2)) *
        (integerMixedPolynomial d j k).eval₂ (Rat.castHom ℝ) x := by
    simp only [integerMixedPolynomial, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_pow, affinePoly_eval, gapVertices,
      yVertices, bVertices, affine_div, div_pow]
    push_cast
    ring
  unfold actualMixedNumeratorK
  simp_rw [he]
  rw [integral_const_mul, canonical_polynomial_integral]
  ring

/-- Exact independent finite coefficient comparison for the actual first
row. This compares sparse polynomial integration to the original signed
convolution; neither side is defined by the other. NOT EXECUTED. -/
theorem row21_sparse_mixed_coefficients : ∀ j : Fin 10, ∀ k : Fin 7,
    polynomialMoment (integerMixedPolynomial Row21.data j k.val) =
      ((k.val.factorial : ℚ) * (mixedNumerator Row21.data j k.val : ℚ)) /
        ((k.val + 11).factorial : ℚ) := by
  decide +kernel

/-- The same independent check for row22's distinct actual geometry and
integer normalization. NOT EXECUTED; no resource feasibility is claimed. -/
theorem row22_sparse_mixed_coefficients : ∀ j : Fin 10, ∀ k : Fin 7,
    polynomialMoment (integerMixedPolynomial Row22.data j k.val) =
      ((k.val.factorial : ℚ) * (mixedNumerator Row22.data j k.val : ℚ)) /
        ((k.val + 11).factorial : ℚ) := by
  decide +kernel

theorem actual_sparse_mixed_coefficients (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    polynomialMoment (integerMixedPolynomial (data r) j k.val) =
      ((k.val.factorial : ℚ) * (mixedNumerator (data r) j k.val : ℚ)) /
        ((k.val + 11).factorial : ℚ) := by
  fin_cases r
  · simpa [data] using row21_sparse_mixed_coefficients j k
  · simpa [data] using row22_sparse_mixed_coefficients j k

/-- All seventy actual measured canonical mixed numerators for each row,
including precisely the requested degrees 2..6. No moment premise remains. -/
theorem actual_row_mixed_numerator (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    actualMixedNumeratorK (data r) j k.val =
      ((k.val.factorial : ℝ) * (mixedNumerator (data r) j k.val : ℝ)) /
        (((k.val + 11).factorial : ℝ) * (data r).U^k.val * (data r).L^2) := by
  rw [actualMixedNumeratorK_polynomial]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (actual_sparse_mixed_coefficients r j k)
  push_cast at h
  rw [h]
  ring

def actualMixedExpectationK (d : SimplexData) (j : Fin 10) (k : Nat) : ℝ :=
  actualMixedNumeratorK d j k / actualGapMass d

/-- The source's exact binomial correction term, now attached to a real
measured mixed expectation for the actual row. It is not an enclosure. -/
theorem actual_row_mixed_term (r : Fin 2) (j : Fin 10) (k : Fin 7) :
    (value (mixedTerm (data r) j k) : ℝ) =
      (((9 + k.val).choose k.val : ℝ) *
        actualMixedExpectationK (data r) j k.val) /
        (2 * (((data r).maxima j : ℝ) / (data r).L)^2 *
          (((data r).U : ℝ) / (data r).L)^10) := by
  have hG : (gapTotal (data r).gaps : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (data r).gapsPos)
  have hU : ((data r).U : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (data r).UPos)
  have hL : ((data r).L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (data r).LPos)
  have hV : ((data r).maxima j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((data r).maximaPos j))
  rw [actualMixedExpectationK, actual_row_mixed_numerator, actualGapMass_eq]
  unfold value mixedTerm mixedTermNumerator mixedTermDenominator
  push_cast
  fin_cases k <;> norm_num <;> field_simp [hG, hU, hL, hV] <;> ring

/-- The full exact original Q6, rather than Q0 plus an unrelated extra
copy, is now identified with the seventy actual measured mixed terms. -/
theorem actual_row_Q6 (r : Fin 2) :
    (value (q6 (data r)) : ℝ) =
      ∑ j : Fin 10, ∑ k : Fin 7,
        (((9 + k.val).choose k.val : ℝ) *
          actualMixedExpectationK (data r) j k.val) /
          (2 * (((data r).maxima j : ℝ) / (data r).L)^2 *
            (((data r).U : ℝ) / (data r).L)^10) := by
  rw [q6_value]
  simp only [mixedTerms, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact actual_row_mixed_term r j k

/-- The raw physical polynomial for every k, on the same source support. -/
def physicalMixedK (means : Fin 10 → ℝ) (upper : ℝ)
    (j : Fin 10) (k : Nat) (z : Ambient) : ℝ :=
  physicalGap z * (physicalY means upper z)^k * (physicalDeviation means j z)^2

theorem physical_mixedK_from_vertex_normalization (v : RationalVertices)
    (hv : (edgeMatrix v).det ≠ 0) (means : Fin 10 → ℚ) (upper : ℚ)
    (d : SimplexData) (gd : Nat) (h : VertexNormalization v means upper d gd)
    (j : Fin 10) (k : Nat) :
    (∫ z in sourceSupport v,
      physicalMixedK (fun i => (means i : ℝ)) (upper : ℝ) j k z) =
      (|((edgeMatrix v).det : ℝ)| / (gd : ℝ)) * actualMixedNumeratorK d j k := by
  have hg := (real_vertex_arrays v means upper d gd h).1
  have hy := (real_vertex_arrays v means upper d gd h).2.1
  have hb := (real_vertex_arrays v means upper d gd h).2.2 j
  rw [source_integral v hv]
  simp only [physicalMixedK, physicalGap_vertexMap, physicalY_vertexMap,
    physicalDeviation_vertexMap, hg, hy, hb, affine_div]
  have he (x : Ambient) :
      (affine (gapVertices d) x / (gd : ℝ)) *
          (affine (yVertices d) x)^k * (affine (bVertices d j) x)^2 =
      (1 / (gd : ℝ)) * (affine (gapVertices d) x *
        (affine (yVertices d) x)^k * (affine (bVertices d j) x)^2) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  change |((edgeMatrix v).det : ℝ)| *
    ((1 / (gd : ℝ)) * actualMixedNumeratorK d j k) = _
  ring

/-- Concrete row21 measured physical identities for all k=0..6. -/
theorem row21_physical_all_mixed (j : Fin 10) (k : Fin 7) :
    (∫ z in sourceSupport row21,
      physicalMixedK (fun i => (Row21.means i : ℝ)) (Row21.upper : ℝ) j k.val z) =
      (((8.factorial : ℝ) * (P2Winner9Row21RawVertexData.physicalVolume : ℝ)) /
        (Row21.gapDen : ℝ)) *
      (((k.val.factorial : ℝ) * (mixedNumerator Row21.data j k.val : ℝ)) /
        (((k.val + 11).factorial : ℝ) * Row21.data.U^k.val * Row21.data.L^2)) := by
  rw [physical_mixedK_from_vertex_normalization row21 row21_det_ne_zero
    Row21.means Row21.upper Row21.data Row21.gapDen row21_vertex_normalization]
  have h := actual_row_mixed_numerator (0 : Fin 2) j k
  simp only [data, if_pos rfl] at h
  rw [h]
  congr 2
  exact_mod_cast row21_abs_det_volume

/-- Concrete row22 uses its own U/L, signed b/L and gap denominator. -/
theorem row22_physical_all_mixed (j : Fin 10) (k : Fin 7) :
    (∫ z in sourceSupport row22,
      physicalMixedK (fun i => (Row22.means i : ℝ)) (Row22.upper : ℝ) j k.val z) =
      (((8.factorial : ℝ) * (row22Volume : ℝ)) / (Row22.gapDen : ℝ)) *
      (((k.val.factorial : ℝ) * (mixedNumerator Row22.data j k.val : ℝ)) /
        (((k.val + 11).factorial : ℝ) * Row22.data.U^k.val * Row22.data.L^2)) := by
  rw [physical_mixedK_from_vertex_normalization row22 row22_det_ne_zero
    Row22.means Row22.upper Row22.data Row22.gapDen row22_vertex_normalization]
  have h := actual_row_mixed_numerator (1 : Fin 2) j k
  simp [data] at h
  rw [h]
  congr 2
  exact_mod_cast row22_abs_det_volume

end

end ImbalancedChen.P2Winner9SelectedAllMixedMoments
