import ImbalancedChen.P2Winner9FastExactAssembly

/-! Exact Q6 evaluation with a common denominator for the seven
degrees of each factor. -/

namespace ImbalancedChen.P2Winner9GroupedQ6

open P2Winner9CurvatureFullExactAssembly
open P2Winner9CurvatureExactMomentFloor (gapTotal)
open P2Winner9MixedDegreeSixExactAssembly (mixedTermDenominator)
open P2Winner9FastExactAssembly

private def degreeDenominator (k : Fin 7) : ℕ := (k.val + 10) * (k.val + 11)

/-- A common multiple of the seven degree denominators. -/
private def degreeCommonDenominator : ℕ := 4084080

private theorem degree_dvd_common : ∀ k : Fin 7, degreeDenominator k ∣ degreeCommonDenominator := by
  decide +kernel

private def degreeScale (d : SimplexData) (k : Fin 7) : ℕ :=
  d.U^(6 - k.val) * (degreeCommonDenominator / degreeDenominator k)

private def factorDenominator (d : SimplexData) (j : Fin 10) : ℕ :=
  2 * gapTotal d.gaps * d.U^16 * (d.maxima j)^2 * degreeCommonDenominator

private theorem factor_denominator_pos (d : SimplexData) (j : Fin 10) : 0 < factorDenominator d j := by
  have hG := d.gapsPos
  have hU := d.UPos
  have hV := d.maximaPos j
  unfold factorDenominator degreeCommonDenominator
  positivity

/-- Only the degree-dependent multipliers are inserted in the signed
numerator. The common `L^10` is included once per factor. -/
def factorMixedFraction (d : SimplexData) (j : Fin 10) : ExactFraction :=
  ⟨(d.L : ℤ)^10 * ∑ k : Fin 7, mixedNumeratorFast d j k.val * (degreeScale d k : ℤ),
    factorDenominator d j, factor_denominator_pos d j⟩

private theorem denominator_scale (d : SimplexData) (j : Fin 10) (k : Fin 7) :
    factorDenominator d j = mixedTermDenominator d j k.val * degreeScale d k := by
  have hpow : d.U^k.val * d.U^10 * d.U^(6 - k.val) = d.U^16 := by
    rw [← pow_add, ← pow_add]
    congr 1
    have hk := k.isLt
    omega
  have hdvd : degreeDenominator k * (degreeCommonDenominator / degreeDenominator k) =
      degreeCommonDenominator := Nat.mul_div_cancel' (degree_dvd_common k)
  unfold factorDenominator
  rw [← hpow, ← hdvd]
  unfold mixedTermDenominator degreeScale degreeDenominator
  ac_rfl

private theorem degree_scale_ne_zero (d : SimplexData) (j : Fin 10) (k : Fin 7) :
    degreeScale d k ≠ 0 := by
  intro h
  have hz := denominator_scale d j k
  rw [h, Nat.mul_zero] at hz
  exact (factor_denominator_pos d j).ne' hz

private theorem scaled_term_value (d : SimplexData) (j : Fin 10) (k : Fin 7) :
    value (mixedTermFast d j k) =
      ((((d.L : ℤ)^10 * mixedNumeratorFast d j k.val) * (degreeScale d k : ℤ) : ℤ) : ℚ) /
        (factorDenominator d j : ℚ) := by
  have hs : (degreeScale d k : ℚ) ≠ 0 := by
    exact_mod_cast degree_scale_ne_zero d j k
  rw [denominator_scale]
  change (((d.L : ℤ)^10 * mixedNumeratorFast d j k.val : ℤ) : ℚ) /
       (mixedTermDenominator d j k.val : ℚ) = _
  push_cast
  rw [mul_div_mul_right _ _ hs]

theorem factor_mixed_value_eq (d : SimplexData) (j : Fin 10) :
    value (factorMixedFraction d j) = ∑ k : Fin 7, value (mixedTermFast d j k) := by
  simp_rw [scaled_term_value]
  unfold value factorMixedFraction
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  simp only [mul_assoc]

/-- Assemble the degree groups before directed rounding. -/
def q6Grouped (d : SimplexData) : ExactFraction :=
  sumFractions (List.ofFn (factorMixedFraction d))

def totalGrouped (d : SimplexData) : ExactFraction := add (t10Fast d) (q6Grouped d)

theorem q6_grouped_eq (d : SimplexData) : value (q6Grouped d) = value (q6Fast d) := by
  unfold q6Grouped q6Fast
  rw [sumFractions_value, sumFractions_value]
  simp only [List.map_flatten, List.map_ofFn, List.sum_flatten,
    List.sum_ofFn, Function.comp_apply, factor_mixed_value_eq]

/-- The grouped evaluator has exactly the source `T10 + Q6` value. -/
theorem total_grouped_eq (d : SimplexData) : value (totalGrouped d) = value (totalFast d) := by
  simp only [totalGrouped, totalFast, add_value, q6_grouped_eq]

end ImbalancedChen.P2Winner9GroupedQ6
