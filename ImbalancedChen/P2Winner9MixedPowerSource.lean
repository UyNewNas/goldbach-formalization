import ImbalancedChen.P2Winner9MixedPowerMoment
import ImbalancedChen.P2Winner9MarkedCoefficient

/-! The measured affine mixed powers in the exact signed source assembly. -/

namespace ImbalancedChen.P2Winner9MixedPowerSource

noncomputable section

open ImbalancedChen.P2Winner9CurvatureExactMomentFloor (gapTotal)
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
open ImbalancedChen.P2Winner9MixedPowerMoment
open ImbalancedChen.P2Winner9MarkedCoefficient

/-- The division-free measured sum is the original signed series coefficient. -/
theorem mixedCompositionNumerator_eq_source (d : SimplexData) (j : Fin 10) (k : ℕ) :
    mixedCompositionNumerator d j k = mixedNumerator d j k :=
  triple_compositions_eq_mixedNumerator d j k

/-- Every measured canonical mixed moment has the exact original signed numerator. -/
theorem actualMixedPowerExpectation_eq_source (d : SimplexData) (j : Fin 10) (k : ℕ) :
    actualMixedPowerExpectation d j k =
      (((9 : ℕ).factorial : ℝ) * (k.factorial : ℝ) / ((k + 11).factorial : ℝ)) *
        ((mixedNumerator d j k : ℝ) /
          ((gapTotal d.gaps : ℝ) * (d.U : ℝ)^k * (d.L : ℝ)^2)) := by
  rw [actualMixedPowerExpectation_eq_compositions, mixedCompositionNumerator_eq_source]

private theorem choose_mul_factorials (k : ℕ) :
    ((9 + k).choose k : ℝ) *
      (((9 : ℕ).factorial : ℝ) * (k.factorial : ℝ) / ((k + 11).factorial : ℝ)) =
      1 / (((k : ℝ) + 10) * ((k : ℝ) + 11)) := by
  have hchoose : ((9 + k).choose k : ℝ) * ((9 : ℕ).factorial : ℝ) * (k.factorial : ℝ) =
      ((9 + k).factorial : ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial 9 k
  have hfact : ((k + 11).factorial : ℝ) =
      ((k : ℝ) + 11) * ((k : ℝ) + 10) * ((9 + k).factorial : ℝ) := by
    have hh : (k + 11).factorial = (k + 11) * (k + 10) * (9 + k).factorial := by
      rw [show k + 11 = (k + 10) + 1 by rfl, Nat.factorial_succ (k + 10),
        show k + 10 = (k + 9) + 1 by rfl, Nat.factorial_succ (k + 9),
        Nat.add_comm k 9, Nat.mul_assoc]
    exact_mod_cast hh
  calc
    _ = (((9 + k).choose k : ℝ) * ((9 : ℕ).factorial : ℝ) * (k.factorial : ℝ)) /
          ((k + 11).factorial : ℝ) := by ring
    _ = _ := by
      rw [hchoose, hfact]
      have hf : ((9 + k).factorial : ℝ) ≠ 0 := by positivity
      field_simp [hf]

/-- Each of the seventy exact source terms equals its measured canonical
weighted contribution before any summation or rounding. -/
theorem actual_mixedTerm_eq (d : SimplexData) (j : Fin 10) (k : Fin 7) :
    ((9 + k.val).choose k.val : ℝ) * actualMixedPowerExpectation d j k.val /
        (2 * ((d.maxima j : ℝ) / d.L)^2 * ((d.U : ℝ) / d.L)^10) =
      (value (mixedTerm d j k) : ℝ) := by
  have hg : (gapTotal d.gaps : ℝ) ≠ 0 := by exact_mod_cast d.gapsPos.ne'
  have hu : (d.U : ℝ) ≠ 0 := by exact_mod_cast d.UPos.ne'
  have hl : (d.L : ℝ) ≠ 0 := by exact_mod_cast d.LPos.ne'
  have hv : (d.maxima j : ℝ) ≠ 0 := by exact_mod_cast (d.maximaPos j).ne'
  rw [actualMixedPowerExpectation_eq_source, ← mul_assoc, choose_mul_factorials]
  unfold value mixedTerm mixedTermNumerator mixedTermDenominator
  push_cast
  simp only [div_pow]
  field_simp [hg, hu, hl, hv]

/-- The full exact degree-six correction is the sum of all seventy measured
terms, scaled using the original per-factor and common upper bounds. -/
theorem actual_q6_eq (d : SimplexData) :
    (value (q6 d) : ℝ) =
      ∑ j : Fin 10, ∑ k : Fin 7,
        ((9 + k.val).choose k.val : ℝ) * actualMixedPowerExpectation d j k.val /
          (2 * ((d.maxima j : ℝ) / d.L)^2 * ((d.U : ℝ) / d.L)^10) := by
  simp_rw [actual_mixedTerm_eq]
  rw [q6_value, Rat.cast_list_sum, mixedTerms]
  simp only [List.map_flatten, List.map_ofFn, List.sum_flatten,
    List.sum_ofFn, Function.comp_apply]

end

end ImbalancedChen.P2Winner9MixedPowerSource
