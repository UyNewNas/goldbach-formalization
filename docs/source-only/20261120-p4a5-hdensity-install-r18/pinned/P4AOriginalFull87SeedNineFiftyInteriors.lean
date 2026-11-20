import ImbalancedChen.P4AOriginalFull87SourceDictionary
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Original full-87 Cell IDs 7 and 30..44: one actual seed7, thirteen
actual winner9 cells, and fiftyAsc/fiftyDesc. No surrogate Source guard.
The rational interior points are NEW feasibility reconstructions, not
the saved87 .witness archive. Continuous boxes do not imply arithmetic
prime tuples, dynamic parent admission, signed saving, or asymptotic PP.
-/
namespace ImbalancedChen.P4AOriginalFull87SeedNineFiftyInteriors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

/-- Each entry names an actual original remaining-cell Source,
preserving the original thirteen winner9 variants and both mask50
branches. No new or inherited mask is constructed here. -/
def originalCell : Fin 16 → P4AOriginalRemainingEighthSources.Cell :=
  ![.seed, .nine 0, .nine 1, .nine 2, .nine 3, .nine 4, .nine 5, .nine 6, .nine 7, .nine 8, .nine 9, .nine 10, .nine 11, .nine 12, .fiftyA, .fiftyD]

/-- Sixteen rational feasibility points; denominator 10^8.
Coordinates are in source-history order, not global cell-index order. -/
def originalPointQ : Fin 16 → Fin 8 → ℚ :=
  ![
    ![17232795/100000000, 11396034/100000000, 8482143/100000000, 5836761/100000000, 3339102/100000000, 2922870/100000000, 2506638/100000000, 2090339/100000000],
    ![12870858/100000000, 10147888/100000000, 9518286/100000000, 6435429/100000000, 3172762/100000000, 3082857/100000000, 2992952/100000000, 2902980/100000000],
    ![14621169/100000000, 12131000/100000000, 7669115/100000000, 4461885/100000000, 3386428/100000000, 3207230/100000000, 3028031/100000000, 2848766/100000000],
    ![13227715/100000000, 11071060/100000000, 8920939/100000000, 5535530/100000000, 3692531/100000000, 3385409/100000000, 3078287/100000000, 2771099/100000000],
    ![14854980/100000000, 12638452/100000000, 7213640/100000000, 4141445/100000000, 3713745/100000000, 3499895/100000000, 3286045/100000000, 2644428/100000000],
    ![13423205/100000000, 11823931/100000000, 8295425/100000000, 5127779/100000000, 4343726/100000000, 3951699/100000000, 3559673/100000000, 2383527/100000000],
    ![12754252/100000000, 10038204/100000000, 9602077/100000000, 6595190/100000000, 3443015/100000000, 3006888/100000000, 2934244/100000000, 2861534/100000000],
    ![12514435/100000000, 9911671/100000000, 9794861/100000000, 6724590/100000000, 3303890/100000000, 3187080/100000000, 3070270/100000000, 2836584/100000000],
    ![12828834/100000000, 10690802/100000000, 9210519/100000000, 6085542/100000000, 4605259/100000000, 3124977/100000000, 2878307/100000000, 2631571/100000000],
    ![12893759/100000000, 11184239/100000000, 8795009/100000000, 5890740/100000000, 5293499/100000000, 3501510/100000000, 3202889/100000000, 2306961/100000000],
    ![12228233/100000000, 10190194/100000000, 9850566/100000000, 6453745/100000000, 4076078/100000000, 3736449/100000000, 3057125/100000000, 2717496/100000000],
    ![12380399/100000000, 10845612/100000000, 9117633/100000000, 6430771/100000000, 4702792/100000000, 4414840/100000000, 3645878/100000000, 2110891/100000000],
    ![11553639/100000000, 10453343/100000000, 9903195/100000000, 6602041/100000000, 5501746/100000000, 4951598/100000000, 2750939/100000000, 2200792/100000000],
    ![11101902/100000000, 10279598/100000000, 9868446/100000000, 7401268/100000000, 6578964/100000000, 6167812/100000000, 2096667/100000000, 1644808/100000000],
    ![12538567/100000000, 9162748/100000000, 8198304/100000000, 7716082/100000000, 4822485/100000000, 4340263/100000000, 3703506/100000000, 2411309/100000000],
    ![16075343/100000000, 10930583/100000000, 5946660/100000000, 5305597/100000000, 4823086/100000000, 4340576/100000000, 3377772/100000000, 2895262/100000000]
  ]

def originalPoint (i : Fin 16) : Point :=
  fun j => (originalPointQ i j : ℝ)

private def rowValue (i : Fin 16) (a : Fin 9 → ℚ) : ℚ :=
  a 0 + ∑ j : Fin 8, a j.succ * originalPointQ i j

private theorem real_row_eq_rational (i : Fin 16) (a : Fin 9 → ℚ) :
    P4AOriginalRemainingEighthSources.evalRow a (originalPoint i) =
      (rowValue i a : ℝ) := by
  simp only [P4AOriginalRemainingEighthSources.evalRow,
    rowValue, originalPoint]
  push_cast
  rfl

/-! These finite original-literal computation proofs require Lean
elaboration and kernel evaluation; neither was available in this run.
The proof claims below are deliberately only candidates. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem original_literal_row_margin :
    ∀ i : Fin 16,
    ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
      (7/10000 : ℚ) ≤
        rowValue i (P4AOriginalRemainingEighthSources.row (originalCell i) k) := by
  intro i
  fin_cases i <;> decide

/-- Unlike the previous ascending14 family (max slope 9/2),
these sixteen originals contain slope of absolute value 11/2.
The honest shared coefficient bound is SIX, not FIVE. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem original_literal_slope_bound :
    ∀ i : Fin 16,
    ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
    ∀ j : Fin 8,
      |P4AOriginalRemainingEighthSources.row
          (originalCell i) k j.succ| ≤ (6 : ℚ) := by
  intro i
  fin_cases i <;> decide

private theorem affine_perturbation
    (a : Fin 9 → ℚ) (u v : Point)
    (hcoordinate : ∀ j, |v j - u j| ≤ (1/100000 : ℝ))
    (hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 6) :
    |P4AOriginalRemainingEighthSources.evalRow a v -
      P4AOriginalRemainingEighthSources.evalRow a u| ≤
        (3/6250 : ℝ) := by
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
    _ ≤ ∑ _j : Fin 8, (6 : ℝ) * (1/100000 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hcoeff j) (hcoordinate j)
        (abs_nonneg _) (by norm_num)
    _ = (3/6250 : ℝ) := by norm_num

/-- Actual 96+13*97+95+96 original strict affine inequalities:
at radius 1/100000, each stays >= 7/10000 - 3/6250 =
11/50000 > 0. No geometry-as-prime-count inference is made. -/
theorem all16_original_rows_box_slack
    (i : Fin 16) (s : Point)
    (hs : ∀ j, |s j - originalPoint i j| ≤ (1/100000 : ℝ)) :
    ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
      (11/50000 : ℝ) ≤
        P4AOriginalRemainingEighthSources.evalRow
          (P4AOriginalRemainingEighthSources.row (originalCell i) k) s := by
  intro k
  let a := P4AOriginalRemainingEighthSources.row (originalCell i) k
  have hcentre : (7/10000 : ℝ) ≤
      P4AOriginalRemainingEighthSources.evalRow a (originalPoint i) := by
    rw [real_row_eq_rational]
    exact_mod_cast original_literal_row_margin i k
  have hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 6 := by
    intro j
    exact_mod_cast original_literal_slope_bound i k j
  have hdelta := affine_perturbation a (originalPoint i) s hs hcoeff
  have hleft := (abs_le.mp hdelta).1
  linarith

/-- Genuine source of each remaining seed7/winner9/mask50 cell
in the actual 87-Cell dictionary. This is not actualPrimeSource. -/
theorem all16_box_mem_original_source
    (i : Fin 16) (s : Point)
    (hs : ∀ j, |s j - originalPoint i j| ≤ (1/100000 : ℝ)) :
    Source (.remaining (originalCell i)) s := by
  change ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
      0 < P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalRemainingEighthSources.row (originalCell i) k) s
  intro k
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11/50000)
    (all16_original_rows_box_slack i s hs k)

/-- Strict eight-dimensional nonempty interior for all sixteen
ORIGINAL continuous Sources, without an arithmetic existence claim. -/
theorem all16_witness_mem_original_source (i : Fin 16) :
    Source (.remaining (originalCell i)) (originalPoint i) := by
  apply all16_box_mem_original_source
  intro j
  simp

end
end ImbalancedChen.P4AOriginalFull87SeedNineFiftyInteriors
