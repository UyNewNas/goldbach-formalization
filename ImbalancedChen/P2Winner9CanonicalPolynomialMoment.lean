import ImbalancedChen.P2Winner9PhysicalVertexInterpolation
import Mathlib.Algebra.MvPolynomial.Eval

/-!
The actual Lebesgue integral of a rational polynomial over the canonical
8-simplex is the sum of its monomial moments. Expressing signed mixed
moments as such polynomials keeps their vertex scales explicit.
-/

namespace ImbalancedChen.P2Winner9CanonicalPolynomialMoment

noncomputable section

open MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9NestedEightSimplexMoment
open ImbalancedChen.P2Winner9ActualEightSimplexMoment
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly

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
      (fun x : Ambient => ((p.coeff e : ℚ) : ℝ) * ∏ i : Fin 8, (x i)^(e i))
      canonicalSupport := by
    apply ContinuousOn.integrableOn_compact canonicalSupport_compact
    fun_prop
  have he : (fun x : Ambient => p.eval₂ (Rat.castHom ℝ) x) =
      (fun x => ∑ e ∈ p.support,
        ((p.coeff e : ℚ) : ℝ) * ∏ i : Fin 8, (x i)^(e i)) := by
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
    unfold gapVertices yVertices bVertices
    rw [affine_div, affine_div]
    simp only [integerMixedPolynomial, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_pow, affinePoly_eval, div_pow]
    push_cast
    ring
  unfold actualMixedNumeratorK
  simp_rw [he]
  rw [integral_const_mul, canonical_polynomial_integral]
  ring

end

end ImbalancedChen.P2Winner9CanonicalPolynomialMoment
