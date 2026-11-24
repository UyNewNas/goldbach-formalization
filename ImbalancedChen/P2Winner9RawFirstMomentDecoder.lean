import ImbalancedChen.P2Winner9FastMomentDecoder
import ImbalancedChen.P2Winner9CanonicalFirstMoment

/-! Nine-vertex evaluators for the raw decoder's gap and affine moments. -/

namespace ImbalancedChen.P2Winner9RawFirstMomentDecoder

open MeasureTheory
open P2Winner9BarycentricMixedDegreeOne
open P2Winner9CanonicalFirstMoment
open P2Winner9CanonicalPolynomialMoment
open P2Winner9CurvatureExactMomentFloor (gapTotal)
open P2Winner9CurvatureFullExactAssembly (SimplexData)
open P2Winner9FastMomentDecoder
open P2Winner9PhysicalAffineTransfer (canonicalSupport)

/-- Exact gap mass over the canonical coordinate simplex. -/
def gapMomentQ (g : Fin 9 → ℚ) : ℚ :=
  (∑ i, g i) / ((9 : ℕ).factorial : ℚ)

/-- Exact normalized affine mean from nine gap and nine affine vertices. -/
def affineMeanQ (g v : Fin 9 → ℚ) : ℚ :=
  let G := ∑ i, g i
  (G * (∑ i, v i) + ∑ i, g i * v i) / (10 * G)

private theorem scaled_sum_gap (g : Fin 9 → ℚ) (d : SimplexData) (s : ℕ)
    (hs : 0 < s) (hg : ∀ i, g i = (d.gaps i : ℚ) / s) :
    (gapTotal d.gaps : ℚ) = (∑ i, g i) * (s : ℚ) := by
  have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [gapTotal, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => ((eq_div_iff hs').mp (hg i)).symm)

theorem gapMomentQ_pos (g : Fin 9 → ℚ) (hg : 0 < ∑ i, g i) :
    0 < gapMomentQ g :=
  div_pos hg (by positivity)

theorem gapMomentQ_eq_polynomialMoment (g : Fin 9 → ℚ) (d : SimplexData) (s : ℕ)
    (hs : 0 < s) (hg : ∀ i, g i = (d.gaps i : ℚ) / s) :
    polynomialMoment (affinePoly g) = gapMomentQ g := by
  have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [gap_polynomialMoment_eq g d s hg, scaled_sum_gap g d s hs hg, gapMomentQ]
  rw [mul_comm (∑ i, g i), mul_div_assoc, mul_div_cancel_left₀ _ hs']

/-- The original sparse-polynomial mean equals a direct nine-vertex calculation. -/
theorem affineMeanQ_eq_polynomialMoment (g v : Fin 9 → ℚ) (d : SimplexData) (s : ℕ)
    (hs : 0 < s) (hg : ∀ i, g i = (d.gaps i : ℚ) / s) :
    polynomialMoment (affinePoly g * affinePoly v) / polynomialMoment (affinePoly g) =
      affineMeanQ g v := by
  apply Rat.cast_injective (α := ℝ)
  rw [weighted_polynomial_cast g d s hs hg (affinePoly v) _ (affinePoly_eval v)]
  rw [canonicalSupport, actualGapWeightedAffine_eq]
  have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hg' (i : Fin 9) : gapVertices d i = (g i : ℝ) * (s : ℝ) := by
    unfold gapVertices
    exact_mod_cast ((eq_div_iff hs').mp (hg i)).symm
  have hsum : (gapTotal d.gaps : ℝ) = (∑ i, (g i : ℝ)) * (s : ℝ) := by
    exact_mod_cast scaled_sum_gap g d s hs hg
  have hv :
      (∑ i, gapVertices d i * (v i : ℝ)) =
        (∑ i, (g i : ℝ) * (v i : ℝ)) * (s : ℝ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [hg']; ring)
  rw [hsum, hv, affineMeanQ]
  push_cast
  calc
    _ = (((∑ i, (g i : ℝ)) * (∑ i, (v i : ℝ)) + ∑ i, (g i : ℝ) * (v i : ℝ)) * (s : ℝ)) /
        ((10 * (∑ i, (g i : ℝ))) * (s : ℝ)) := by ring
    _ = _ := mul_div_mul_right _ _ hsR

/-- The all-row decoder can check factor means from vertex values and one
positive gap sum, using the exact original unnormalized identity. -/
theorem affineMoment_eq_polynomialMoment (g v : Fin 9 → ℚ) (d : SimplexData) (s : ℕ)
    (hs : 0 < s) (hg : ∀ i, g i = (d.gaps i : ℚ) / s) (hpos : 0 < ∑ i, g i) :
    polynomialMoment (affinePoly g * affinePoly v) =
      affineMeanQ g v * gapMomentQ g := by
  rw [← gapMomentQ_eq_polynomialMoment g d s hs hg]
  have hn : polynomialMoment (affinePoly g) ≠ 0 := by
    rw [gapMomentQ_eq_polynomialMoment g d s hs hg]
    exact (gapMomentQ_pos g hpos).ne'
  exact (div_eq_iff hn).mp (affineMeanQ_eq_polynomialMoment g v d s hs hg)

end ImbalancedChen.P2Winner9RawFirstMomentDecoder
