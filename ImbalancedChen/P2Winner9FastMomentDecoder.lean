import ImbalancedChen.P2Winner9CanonicalPolynomialMoment
import ImbalancedChen.P2Winner9FastExactAssembly
import ImbalancedChen.P2Winner9MixedPowerSource
import ImbalancedChen.P2Winner9PowerMoment
import ImbalancedChen.P2Winner9Row22Arithmetic
import ImbalancedChen.P2Winner9TaylorCorrection

/-! Exact computational replacements for the rational polynomial moment decoder. -/

namespace ImbalancedChen.P2Winner9FastMomentDecoder

open MeasureTheory
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9CanonicalPolynomialMoment
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor (gapTotal)
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly (SimplexData homogeneous weightedMoment value)
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly (mixedTerm mixedTermNumerator)
open ImbalancedChen.P2Winner9TaylorCorrection (actual_T10_identity_range)
open ImbalancedChen.P2Winner9FastExactAssembly
open ImbalancedChen.P2Winner9MixedPowerMoment
open ImbalancedChen.P2Winner9MixedPowerSource
open ImbalancedChen.P2Winner9PhysicalAffineTransfer (Ambient canonicalSupport)
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation (affine_div)
open ImbalancedChen.P2Winner9PowerMoment
open ImbalancedChen.P2Winner9Row22Arithmetic
  (RationalVertices VertexNormalization rawGap rawY rawDeviation)
open ImbalancedChen.P2Winner9HomogeneousRecurrence (homogeneousFast_eq_source)

/-- Executable rational power moment using the homogeneous prefix recurrence. -/
def powerMomentQ (d : SimplexData) (k : ℕ) : ℚ :=
  (((9 : ℕ).factorial : ℚ) / (gapTotal d.gaps : ℚ)) *
    ((k.factorial : ℚ) / ((k + 9).factorial : ℚ)) *
    (weightedMomentFast d k : ℚ) / (d.U : ℚ)^k

/-- Executable rational mixed moment retaining the source signed convolution. -/
def mixedMomentQ (d : SimplexData) (j : Fin 10) (k : ℕ) : ℚ :=
  (((9 : ℕ).factorial : ℚ) * (k.factorial : ℚ) / ((k + 11).factorial : ℚ)) *
    ((mixedNumeratorFast d j k : ℚ) /
      ((gapTotal d.gaps : ℚ) * (d.U : ℚ)^k * (d.L : ℚ)^2))

theorem actualPowerExpectation_eq_cast (d : SimplexData) (k : ℕ) :
    actualPowerExpectation d k = (powerMomentQ d k : ℝ) := by
  have h (n : ℕ) : P2Winner9HomogeneousRecurrence.homogeneousFast d.y n =
      homogeneous d.y n := homogeneousFast_eq_source d.y n
  have hfast : weightedMomentFast d k = weightedMoment d k := by
    simp only [weightedMomentFast, weightedMoment, h]
  rw [actualPowerExpectation_eq_weightedMoment, powerMomentQ, hfast]
  push_cast
  rfl

theorem actualMixedPowerExpectation_eq_cast (d : SimplexData) (j : Fin 10) (k : ℕ) :
    actualMixedPowerExpectation d j k = (mixedMomentQ d j k : ℝ) := by
  rw [actualMixedPowerExpectation_eq_source, mixedMomentQ, mixedNumerator_eq]
  push_cast
  rfl

/-- The exact raw polynomial for the gap-weighted power used by the all-row decoder. -/
noncomputable def rawPowerMoment (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (k : ℕ) : ℚ :=
  polynomialMoment (affinePoly (rawGap v) * (affinePoly (rawY v means upper))^k) /
    polynomialMoment (affinePoly (rawGap v))

/-- The exact raw polynomial for a mixed term used by the all-row decoder. -/
noncomputable def rawMixedMoment (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (j : Fin 10) (k : ℕ) : ℚ :=
  polynomialMoment (affinePoly (rawGap v) * (affinePoly (rawY v means upper))^k *
      (affinePoly (fun i => rawDeviation v means i j))^2) /
    polynomialMoment (affinePoly (rawGap v))

private theorem eval_gap (g : Fin 9 → ℚ) (d : SimplexData) (s : ℕ)
    (h : ∀ i, g i = (d.gaps i : ℚ) / s) (x : Ambient) :
    (affinePoly g).eval₂ (Rat.castHom ℝ) x = affine (gapVertices d) x / (s : ℝ) := by
  rw [affinePoly_eval, ← affine_div]
  congr 1
  funext i
  simp [h i, gapVertices]

/-- The independent rational polynomial gap normalizer is the same
nine-vertex mass with the appropriate integer scale. -/
theorem gap_polynomialMoment_eq (g : Fin 9 → ℚ) (d : SimplexData) (s : ℕ)
    (h : ∀ i, g i = (d.gaps i : ℚ) / s) :
    polynomialMoment (affinePoly g) =
      ((gapTotal d.gaps : ℚ) / ((9 : ℕ).factorial : ℚ)) / (s : ℚ) := by
  apply Rat.cast_injective (α := ℝ)
  rw [← canonical_polynomial_integral]
  simp_rw [eval_gap g d s h]
  rw [integral_div]
  change actualGapMass d / (s : ℝ) = _
  rw [actualGapMass_eq]
  push_cast
  rfl

/-- A generic polynomial weighted by any exact rational gap array transports
to the normalized measured canonical polynomial with the integer gap array. -/
theorem weighted_polynomial_cast (g : Fin 9 → ℚ) (d : SimplexData) (s : ℕ)
    (hs : 0 < s) (hg : ∀ i, g i = (d.gaps i : ℚ) / s) (p : Poly)
    (f : Ambient → ℝ) (hf : ∀ x, p.eval₂ (Rat.castHom ℝ) x = f x) :
    ((polynomialMoment (affinePoly g * p) / polynomialMoment (affinePoly g) : ℚ) : ℝ) =
      (∫ x in canonicalSupport, affine (gapVertices d) x * f x) / actualGapMass d := by
  push_cast
  rw [← canonical_polynomial_integral, ← canonical_polynomial_integral]
  simp_rw [MvPolynomial.eval₂_mul, eval_gap g d s hg, hf, div_mul_eq_mul_div]
  rw [integral_div, integral_div]
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  exact div_div_div_cancel_right₀ hs' _ _

private theorem eval_y (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (s : ℕ) (h : VertexNormalization v means upper d s)
    (x : Ambient) :
    (affinePoly (rawY v means upper)).eval₂ (Rat.castHom ℝ) x = affine (yVertices d) x := by
  rw [affinePoly_eval]
  congr 1
  funext i
  simp [((h.2 i).2).1, yVertices]

private theorem eval_b (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (s : ℕ) (h : VertexNormalization v means upper d s)
    (j : Fin 10) (x : Ambient) :
    (affinePoly (fun i => rawDeviation v means i j)).eval₂ (Rat.castHom ℝ) x =
      affine (bVertices d j) x := by
  rw [affinePoly_eval]
  congr 1
  funext i
  simp [((h.2 i).2).2 j, bVertices]

/-- Replace the decoder's sparse polynomial power by the fast exact rational moment. -/
theorem rawPowerMoment_eq_fast (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (s : ℕ) (h : VertexNormalization v means upper d s) (k : ℕ) :
    rawPowerMoment v means upper k = powerMomentQ d k := by
  apply Rat.cast_injective (α := ℝ)
  rw [← actualPowerExpectation_eq_cast, rawPowerMoment]
  exact weighted_polynomial_cast (rawGap v) d s h.1 (fun i => (h.2 i).1)
    ((affinePoly (rawY v means upper))^k) (fun x => (affine (yVertices d) x)^k)
    (fun x => by rw [MvPolynomial.eval₂_pow, eval_y v means upper d s h])

/-- Replace the decoder's sparse mixed polynomial by the fast signed coefficient. -/
theorem rawMixedMoment_eq_fast (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (s : ℕ) (h : VertexNormalization v means upper d s)
    (j : Fin 10) (k : ℕ) :
    rawMixedMoment v means upper j k = mixedMomentQ d j k := by
  apply Rat.cast_injective (α := ℝ)
  rw [← actualMixedPowerExpectation_eq_cast, rawMixedMoment, mul_assoc]
  have hcast := weighted_polynomial_cast (rawGap v) d s h.1 (fun i => (h.2 i).1)
    ((affinePoly (rawY v means upper))^k *
      (affinePoly (fun i => rawDeviation v means i j))^2)
    (fun x => (affine (yVertices d) x)^k * (affine (bVertices d j) x)^2)
    (fun x => by
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, eval_y v means upper d s h,
        eval_b v means upper d s h])
  simpa only [actualMixedPowerExpectation, actualMixedPowerNumerator, canonicalSupport, mul_assoc] using hcast

/-- The decoder's original rational Taylor expression equals the executable
source fraction whenever its physical upper bound has the typed scale. -/
theorem rawT10_eq_fast (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (d : SimplexData) (s : ℕ) (h : VertexNormalization v means upper d s)
    (hupper : upper = (d.U : ℚ) / d.L) :
    (1 / upper^10) * (∑ k ∈ Finset.range 11, ((9 + k).choose k : ℚ) *
        (rawPowerMoment v means upper k - (rawPowerMoment v means upper 1)^k)) =
      value (t10Fast d) := by
  apply Rat.cast_injective (α := ℝ)
  rw [t10_eq, actual_T10_identity_range]
  simp_rw [rawPowerMoment_eq_fast v means upper d s h]
  push_cast
  simp only [← actualPowerExpectation_eq_cast, hupper, Rat.cast_div, Rat.cast_natCast]

/-- The decoder's original rational mixed term equals its executable
source fraction with the exact common and per-factor upper-bound scales. -/
theorem rawMixedTerm_eq_fast (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (transverseUpper : Fin 10 → ℚ) (d : SimplexData) (s : ℕ)
    (h : VertexNormalization v means upper d s)
    (hupper : upper = (d.U : ℚ) / d.L)
    (htransverse : ∀ j, transverseUpper j = (d.maxima j : ℚ) / d.L)
    (j : Fin 10) (k : Fin 7) :
    ((9 + k.val).choose k.val : ℚ) * rawMixedMoment v means upper j k.val /
        (2 * (transverseUpper j)^2 * upper^10) =
      value (mixedTermFast d j k) := by
  have ht : mixedTermFast d j k = mixedTerm d j k := by
    simp only [mixedTermFast, mixedTerm, mixedTermNumerator, mixedNumerator_eq]
  apply Rat.cast_injective (α := ℝ)
  rw [ht, ← actual_mixedTerm_eq, rawMixedMoment_eq_fast v means upper d s h]
  push_cast
  simp only [← actualMixedPowerExpectation_eq_cast, hupper, htransverse j,
    Rat.cast_div, Rat.cast_natCast]

/-- The decoder's full 70-term rational correction equals the executable
exact Q6 fraction at the same normalized vertex data and caps. -/
theorem rawQ6_eq_fast (v : RationalVertices) (means : Fin 10 → ℚ)
    (upper : ℚ) (transverseUpper : Fin 10 → ℚ) (d : SimplexData) (s : ℕ)
    (h : VertexNormalization v means upper d s)
    (hupper : upper = (d.U : ℚ) / d.L)
    (htransverse : ∀ j, transverseUpper j = (d.maxima j : ℚ) / d.L) :
    (∑ j : Fin 10, ∑ k : Fin 7,
      ((9 + k.val).choose k.val : ℚ) * rawMixedMoment v means upper j k.val /
        (2 * (transverseUpper j)^2 * upper^10)) =
      value (q6Fast d) := by
  apply Rat.cast_injective (α := ℝ)
  rw [q6_eq, actual_q6_eq]
  simp_rw [rawMixedMoment_eq_fast v means upper d s h]
  push_cast
  simp only [← actualMixedPowerExpectation_eq_cast, hupper, htransverse,
    Rat.cast_div, Rat.cast_natCast]

end ImbalancedChen.P2Winner9FastMomentDecoder
