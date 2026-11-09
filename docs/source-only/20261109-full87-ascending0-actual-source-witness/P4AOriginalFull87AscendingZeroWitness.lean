import ImbalancedChen.P4AOriginalFull87SourceDictionary
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A genuinely ORIGINAL geometric source witness: ascending family ID 0,
the 96 literal affine inequalities, the existing global Cell constructor,
and a closed 8-dimensional neighbourhood with strictly positive row
slack. This is not an archived numerical certificate and does not assert
an N-dependent prime occurrence or actual finite parent.
-/

namespace ImbalancedChen.P4AOriginalFull87AscendingZeroWitness
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

/-- Rational coordinates were obtained by optimization of the ORIGINAL
96 affine rows, then rounded and checked exactly against those rows.
No numerical archive row is redefined. -/
def ascendingZeroQ : Fin 8 → ℚ :=
  ![16649/100000, 9845/100000, 9758/100000, 3185/100000,
    3099/100000, 3012/100000, 2926/100000, 2839/100000]

def ascendingZeroPoint : Point := fun j => (ascendingZeroQ j : ℝ)

private def rationalRowValue (a : Fin 9 → ℚ) : ℚ :=
  a 0 + ∑ j : Fin 8, a j.succ * ascendingZeroQ j

private theorem real_row_eq_rational (a : Fin 9 → ℚ) :
    P4AOriginalRemainingEighthSources.evalRow a ascendingZeroPoint =
      (rationalRowValue a : ℝ) := by
  simp only [P4AOriginalRemainingEighthSources.evalRow,
    rationalRowValue, ascendingZeroPoint]
  push_cast
  rfl

/-- ALL 96 literal inequalities for original ascending ID 0 hold with
at least 1/2000 rational slack at the declared rational point. This is
a kernel-computable finite rational proposition, not a claimed replay
of original archived .witness.json bytes. -/
private theorem literal_zero_rows_rational_margin :
    ∀ k : Fin 96, (1/2000 : ℚ) ≤
      rationalRowValue
        (P4AOriginalAscendingFourteenAffineSource.rows
          (0 : Fin 14) k) := by
  decide

/-- Literal coefficient entries in the SAME original 96 rows have
absolute value at most 5. The exact maximum is 9/2. -/
private theorem literal_zero_rows_rational_coeff_bound :
    ∀ k : Fin 96, ∀ j : Fin 8,
      |P4AOriginalAscendingFourteenAffineSource.rows
          (0 : Fin 14) k j.succ| ≤ (5 : ℚ) := by
  decide

/-- A finite affine perturbation bound; the original row coefficients,
not a substitute source predicate, are used at application time. -/
private theorem original_affine_row_neighbourhood_bound
    (a : Fin 9 → ℚ) (u v : Point)
    (hcoord : ∀ j, |v j - u j| ≤ (1/100000 : ℝ))
    (hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 5) :
    |P4AOriginalRemainingEighthSources.evalRow a v -
      P4AOriginalRemainingEighthSources.evalRow a u| ≤
      (1/2500 : ℝ) := by
  have hdiff :
      P4AOriginalRemainingEighthSources.evalRow a v -
        P4AOriginalRemainingEighthSources.evalRow a u =
      ∑ j : Fin 8, (a j.succ : ℝ) * (v j - u j) := by
    calc
      _ = (∑ j : Fin 8, (a j.succ : ℝ) * v j) -
          (∑ j : Fin 8, (a j.succ : ℝ) * u j) := by
            simp only [P4AOriginalRemainingEighthSources.evalRow]
            ring
      _ = ∑ j : Fin 8,
            ((a j.succ : ℝ) * v j - (a j.succ : ℝ) * u j) := by
              rw [Finset.sum_sub_distrib]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [hdiff]
  calc
    |∑ j : Fin 8, (a j.succ : ℝ) * (v j - u j)| ≤
      ∑ j : Fin 8, |(a j.succ : ℝ) * (v j - u j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 8, (5 : ℝ) * (1/100000 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hcoeff j) (hcoord j)
        (abs_nonneg _) (by norm_num)
    _ = (1/2500 : ℝ) := by norm_num

/-- A CLOSED rational-coordinate box of radius 1/100000 lies strictly
inside the ORIGINAL source for ascending ID 0. Every one of the real
96 affine rows retains at least 1/10000 slack. This is a genuine
geometric interior certificate, not an arithmetic-zero or gain claim. -/
theorem ascending_zero_original_96_rows_box_slack
    (s : Point)
    (hs : ∀ j, |s j - ascendingZeroPoint j| ≤ (1/100000 : ℝ)) :
    ∀ k : Fin 96, (1/10000 : ℝ) ≤
      P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalAscendingFourteenAffineSource.rows
          (0 : Fin 14) k) s := by
  intro k
  let a := P4AOriginalAscendingFourteenAffineSource.rows
    (0 : Fin 14) k
  have hcentre : (1/2000 : ℝ) ≤
      P4AOriginalRemainingEighthSources.evalRow a
        ascendingZeroPoint := by
    rw [real_row_eq_rational]
    exact_mod_cast literal_zero_rows_rational_margin k
  have hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 5 := by
    intro j
    exact_mod_cast literal_zero_rows_rational_coeff_bound k j
  have hdelta :=
    original_affine_row_neighbourhood_bound a ascendingZeroPoint
      s hs hcoeff
  have hleft := (abs_le.mp hdelta).1
  linarith

/-- An authenticated nonempty OPEN affine SOURCE region for exactly
one original Cell constructor; it is not a saved numerical integration
record or an N-dependent actualParent/member certificate. -/
theorem ascending_zero_box_mem_original_source
    (s : Point)
    (hs : ∀ j, |s j - ascendingZeroPoint j| ≤ (1/100000 : ℝ)) :
    Source (.remaining (.ascending (0 : Fin 14))) s := by
  change ∀ k : Fin 96, 0 <
    P4AOriginalRemainingEighthSources.evalRow
      (P4AOriginalAscendingFourteenAffineSource.rows (0 : Fin 14) k) s
  intro k
  have hrow := ascending_zero_original_96_rows_box_slack s hs k
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/10000) hrow

theorem ascending_zero_witness_mem_original_source :
    Source (.remaining (.ascending (0 : Fin 14))) ascendingZeroPoint := by
  apply ascending_zero_box_mem_original_source
  intro j
  simp

end
end ImbalancedChen.P4AOriginalFull87AscendingZeroWitness
