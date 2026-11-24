import ImbalancedChen.P4AOriginalFull87SourceDictionary
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
All twelve ORIGINAL H3 first-failure strict affine Source geometries.
No new mask or replacement source; these are fresh rational interior
points, not saved87 numerical witness bytes or prime occurrence claims.
-/
namespace ImbalancedChen.P4AOriginalFull87H3Interiors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

/-- Twelve exact rational centres, denominator 100000000, for the original
    H3 first-failure Source cells (global indices 58..69). -/
def originalH3PointQ : Fin 12 → Fin 8 → ℚ :=
  ![
    ![14252222/100000000, 11619747/100000000, 10169313/100000000, 5276370/100000000, 2637685/100000000, 2636685/100000000, 2635665/100000000, 2634656/100000000],
    ![15173292/100000000, 12724196/100000000, 9351048/100000000, 4355258/100000000, 3179829/100000000, 2640415/100000000, 2639415/100000000, 2451296/100000000],
    ![14681356/100000000, 12284897/100000000, 9704423/100000000, 4847194/100000000, 4020827/100000000, 3220827/100000000, 2860052/100000000, 2398660/100000000],
    ![15416696/100000000, 13168335/100000000, 9050215/100000000, 4111854/100000000, 3542655/100000000, 2821827/100000000, 2820827/100000000, 2250562/100000000],
    ![14693095/100000000, 12315485/100000000, 9684820/100000000, 4835455/100000000, 4074245/100000000, 3274245/100000000, 2822734/100000000, 2379810/100000000],
    ![13800925/100000000, 11277871/100000000, 10606889/100000000, 5727625/100000000, 3198303/100000000, 2527321/100000000, 2526321/100000000, 2525255/100000000],
    ![13606457/100000000, 11242240/100000000, 10651177/100000000, 5922093/100000000, 2960546/100000000, 2959546/100000000, 2958546/100000000, 2366417/100000000],
    ![14434480/100000000, 12057402/100000000, 10047723/100000000, 5094070/100000000, 4391024/100000000, 3078124/100000000, 2704472/100000000, 2379278/100000000],
    ![14477874/100000000, 12144190/100000000, 9991070/100000000, 5050676/100000000, 4491070/100000000, 3208306/100000000, 2624917/100000000, 2335884/100000000],
    ![14192997/100000000, 11839614/100000000, 10354296/100000000, 5335553/100000000, 3843968/100000000, 3842968/100000000, 2562034/100000000, 2355584/100000000],
    ![14288241/100000000, 12003157/100000000, 10283907/100000000, 5240309/100000000, 4009600/100000000, 4008600/100000000, 2436435/100000000, 2287284/100000000],
    ![14201614/100000000, 12183046/100000000, 10238382/100000000, 5012073/100000000, 5010073/100000000, 4389315/100000000, 2021768/100000000, 2020768/100000000]
  ]

def originalH3Point (i : Fin 12) : Point :=
  fun j => (originalH3PointQ i j : ℝ)

private def originalRowValue (i : Fin 12) (a : Fin 9 → ℚ) : ℚ :=
  a 0 + ∑ j : Fin 8, a j.succ * originalH3PointQ i j

private theorem original_eval_eq (i : Fin 12) (a : Fin 9 → ℚ) :
    P4AOriginalFirstFailureH3Literal.evalAffine a (originalH3Point i) =
      (originalRowValue i a : ℝ) := by
  simp only [P4AOriginalFirstFailureH3Literal.evalAffine,
    originalRowValue, originalH3Point]
  push_cast
  rfl

/-- All twelve times 99 ORIGINAL H3 strict affine rows are evaluated.
    Exact external rational audit: 1188/1188 rows >= 9/1000000;
    smallest row is 477/50000000 at cell 0, original row 20. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem original_h3_literal_margin :
    ∀ i : Fin 12, ∀ k : Fin 99,
      (9/1000000 : ℚ) ≤
        originalRowValue i (P4AOriginalFirstFailureH3Literal.sourceAffineRows i k).2 := by
  intro i
  fin_cases i <;> decide

/-- True maximal coordinate slope of these literal rows is 9/2.
    We use a conservative common coefficient bound 6. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem original_h3_literal_slope :
    ∀ i : Fin 12, ∀ k : Fin 99, ∀ j : Fin 8,
      |(P4AOriginalFirstFailureH3Literal.sourceAffineRows i k).2 j.succ| ≤
        (6 : ℚ) := by
  intro i
  fin_cases i <;> decide

private theorem affine_perturbation
    (a : Fin 9 → ℚ) (u v : Point)
    (hc : ∀ j, |v j - u j| ≤ (1/100000000 : ℝ))
    (ha : ∀ j, |(a j.succ : ℝ)| ≤ 6) :
    |P4AOriginalFirstFailureH3Literal.evalAffine a v -
      P4AOriginalFirstFailureH3Literal.evalAffine a u| ≤
        (3/6250000 : ℝ) := by
  have heq :
      P4AOriginalFirstFailureH3Literal.evalAffine a v -
        P4AOriginalFirstFailureH3Literal.evalAffine a u =
        ∑ j : Fin 8, (a j.succ : ℝ) * (v j - u j) := by
    calc
      _ = (∑ j : Fin 8, (a j.succ : ℝ) * v j) -
          (∑ j : Fin 8, (a j.succ : ℝ) * u j) := by
            simp only [P4AOriginalFirstFailureH3Literal.evalAffine]
            ring
      _ = ∑ j : Fin 8,
            ((a j.succ : ℝ) * v j - (a j.succ : ℝ) * u j) := by
              rw [Finset.sum_sub_distrib]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [heq]
  calc
    |∑ j : Fin 8, (a j.succ : ℝ) * (v j - u j)| ≤
      ∑ j : Fin 8, |(a j.succ : ℝ) * (v j - u j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 8, (6 : ℝ) * (1/100000000 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (ha j) (hc j) (abs_nonneg _) (by norm_num)
    _ = (3/6250000 : ℝ) := by norm_num

/-- Original row slack, including H3 first-failure history and priority.
    The Source is the old full87 dictionary, not a relaxed substitute. -/
theorem all12_original_h3_rows_box_slack
    (i : Fin 12) (s : Point)
    (hs : ∀ j, |s j - originalH3Point i j| ≤ (1/100000000 : ℝ)) :
    ∀ k : Fin 99, (1/125000 : ℝ) ≤
      P4AOriginalFirstFailureH3Literal.evalAffine
        (P4AOriginalFirstFailureH3Literal.sourceAffineRows i k).2 s := by
  intro k
  let a := (P4AOriginalFirstFailureH3Literal.sourceAffineRows i k).2
  have hcentre : (9/1000000 : ℝ) ≤
      P4AOriginalFirstFailureH3Literal.evalAffine
        a (originalH3Point i) := by
    rw [original_eval_eq]
    exact_mod_cast original_h3_literal_margin i k
  have hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 6 := by
    intro j
    exact_mod_cast original_h3_literal_slope i k j
  have hdelta := affine_perturbation a (originalH3Point i) s hs hcoeff
  have hleft := (abs_le.mp hdelta).1
  linarith

/-- Direct connection to the same full87 H3 Source, only continuous geometry. -/
theorem all12_box_mem_original_source (i : Fin 12) (s : Point)
    (hs : ∀ j, |s j - originalH3Point i j| ≤ (1/100000000 : ℝ)) :
    Source (.h3 i) s := by
  change ∀ k : Fin 99, 0 <
    P4AOriginalFirstFailureH3Literal.evalAffine
      (P4AOriginalFirstFailureH3Literal.sourceAffineRows i k).2 s
  intro k
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/125000)
    (all12_original_h3_rows_box_slack i s hs k)

theorem all12_centre_mem_original_source (i : Fin 12) :
    Source (.h3 i) (originalH3Point i) := by
  apply all12_box_mem_original_source
  intro j
  simp

end
end ImbalancedChen.P4AOriginalFull87H3Interiors
