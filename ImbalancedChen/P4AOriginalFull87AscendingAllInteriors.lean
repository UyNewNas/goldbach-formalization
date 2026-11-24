import ImbalancedChen.P4AOriginalFull87SourceDictionary
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
All FOURTEEN actual ORIGINAL ascending affine sources (original IDs
0..6 and 8..14), not surrogate masks or archived integration values.
The 14 points are a newly reconstructed rational feasibility table:
all 14 * 96 ORIGINAL inequalities are checked against the exact
P4AOriginalAscendingFourteenAffineSource.literalPool and literalIndex.
A box is continuous geometry, NOT a prime occurrence, an actualParent,
an original saved87 numerical integral, or an asymptotic gain.
-/

namespace ImbalancedChen.P4AOriginalFull87AscendingAllInteriors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

/-- Original ascending family order, including the missing original ID 7
being omitted by the ORIGINAL `originalId` table. Denominator 10^7. -/
def originalAscendingPointQ : Fin 14 → Fin 8 → ℚ :=
  ![
    ![1664897/10000000, 984502/10000000, 975844/10000000, 318538/10000000, 309880/10000000, 301222/10000000, 292564/10000000, 283899/10000000],
    ![1679079/10000000, 1142733/10000000, 831214/10000000, 361475/10000000, 336497/10000000, 311519/10000000, 286541/10000000, 261557/10000000],
    ![1691944/10000000, 1013031/10000000, 973251/10000000, 400421/10000000, 360640/10000000, 320859/10000000, 281078/10000000, 241291/10000000],
    ![1699539/10000000, 1179830/10000000, 788592/10000000, 409587/10000000, 391238/10000000, 281116/10000000, 262767/10000000, 244411/10000000],
    ![1723782/10000000, 1075322/10000000, 901893/10000000, 475030/10000000, 446130/10000000, 272700/10000000, 243800/10000000, 214893/10000000],
    ![1745789/10000000, 1007937/10000000, 973714/10000000, 532488/10000000, 498265/10000000, 258677/10000000, 224454/10000000, 190224/10000000],
    ![1698151/10000000, 1224248/10000000, 750344/10000000, 473903/10000000, 319362/10000000, 293610/10000000, 267857/10000000, 242098/10000000],
    ![1695927/10000000, 1340985/10000000, 649118/10000000, 412480/10000000, 368116/10000000, 323751/10000000, 279387/10000000, 235016/10000000],
    ![1707845/10000000, 1217298/10000000, 781253/10000000, 490547/10000000, 436045/10000000, 381543/10000000, 272531/10000000, 218029/10000000],
    ![1763838/10000000, 1097340/10000000, 885246/10000000, 666498/10000000, 454404/10000000, 242310/10000000, 206966/10000000, 171615/10000000],
    ![1726216/10000000, 1096358/10000000, 882258/10000000, 573664/10000000, 543082/10000000, 359564/10000000, 242200/10000000, 211618/10000000],
    ![1740667/10000000, 1019840/10000000, 972632/10000000, 720827/10000000, 377695/10000000, 330486/10000000, 236062/10000000, 188854/10000000],
    ![1812508/10000000, 1110422/10000000, 868746/10000000, 702086/10000000, 460409/10000000, 429166/10000000, 156239/10000000, 124995/10000000],
    ![1814286/10000000, 995244/10000000, 974868/10000000, 534979/10000000, 514602/10000000, 494226/10000000, 149027/10000000, 128651/10000000]
  ]

def originalAscendingPoint (i : Fin 14) : Point :=
  fun j => (originalAscendingPointQ i j : ℝ)

private def rationalRowValue (i : Fin 14) (a : Fin 9 → ℚ) : ℚ :=
  a 0 + ∑ j : Fin 8, a j.succ * originalAscendingPointQ i j

private theorem real_row_eq_rational (i : Fin 14) (a : Fin 9 → ℚ) :
    P4AOriginalRemainingEighthSources.evalRow a (originalAscendingPoint i) =
      (rationalRowValue i a : ℝ) := by
  simp only [P4AOriginalRemainingEighthSources.evalRow,
    rationalRowValue, originalAscendingPoint]
  push_cast
  rfl

/-- Entire original 14x96 array: strict uniform rational margin >=1/2000.
There are no input assumptions or invented rows. This kernel-computable
candidate is not yet elaborated, and can be computationally expensive. -/
private theorem original_all_ascending_rows_margin :
    ∀ i : Fin 14, ∀ k : Fin 96, (1/2000 : ℚ) ≤
      rationalRowValue i
        (P4AOriginalAscendingFourteenAffineSource.rows i k) := by
  intro i
  fin_cases i <;> decide

/-- Check the 104 ORIGINAL literal rows once, avoiding 14 redundant
per-family coefficient tables. Their maximum absolute slope is 9/2. -/
private theorem original_pool_coeff_bound :
    ∀ r : Fin 104, ∀ j : Fin 8,
      |P4AOriginalAscendingFourteenAffineSource.literalPool r j.succ| ≤
        (5 : ℚ) := by
  decide

/-- The actual 96 rows for each actual ascending Cell are selected by
the ORIGINAL `literalIndex` and inherit the original-pool bound. -/
private theorem original_ascending_row_coeff_bound
    (i : Fin 14) (k : Fin 96) (j : Fin 8) :
    |P4AOriginalAscendingFourteenAffineSource.rows i k j.succ| ≤
      (5 : ℚ) := by
  exact original_pool_coeff_bound
    (P4AOriginalAscendingFourteenAffineSource.literalIndex i k) j

private theorem affine_perturbation
    (a : Fin 9 → ℚ) (u v : Point)
    (hcoordinate : ∀ j, |v j - u j| ≤ (1/100000 : ℝ))
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
      exact mul_le_mul (hcoeff j) (hcoordinate j)
        (abs_nonneg _) (by norm_num)
    _ = (1/2500 : ℝ) := by norm_num

/-- Each of fourteen original affine Sources contains its own
coordinatewise closed radius-1/100000 box. All 96 strict original
rows of EACH cell retain >=1/10000 slack, using the same row and mask. -/
theorem all14_original_96_rows_box_slack
    (i : Fin 14) (s : Point)
    (hs : ∀ j, |s j - originalAscendingPoint i j| ≤ (1/100000 : ℝ)) :
    ∀ k : Fin 96, (1/10000 : ℝ) ≤
      P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalAscendingFourteenAffineSource.rows i k) s := by
  intro k
  let a := P4AOriginalAscendingFourteenAffineSource.rows i k
  have hcentre : (1/2000 : ℝ) ≤
      P4AOriginalRemainingEighthSources.evalRow a
        (originalAscendingPoint i) := by
    rw [real_row_eq_rational]
    exact_mod_cast original_all_ascending_rows_margin i k
  have hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 5 := by
    intro j
    exact_mod_cast original_ascending_row_coeff_bound i k j
  have hdelta :=
    affine_perturbation a (originalAscendingPoint i) s hs hcoeff
  have hleft := (abs_le.mp hdelta).1
  linarith

/-- Actual 87-Cell dictionary source, not a reduced source predicate.
The 14 values of i retain original ascending IDs 0..6, 8..14. -/
theorem all14_box_mem_original_source
    (i : Fin 14) (s : Point)
    (hs : ∀ j, |s j - originalAscendingPoint i j| ≤ (1/100000 : ℝ)) :
    Source (.remaining (.ascending i)) s := by
  change ∀ k : Fin 96, 0 <
    P4AOriginalRemainingEighthSources.evalRow
      (P4AOriginalAscendingFourteenAffineSource.rows i k) s
  intro k
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/10000)
    (all14_original_96_rows_box_slack i s hs k)

/-- A genuine nonempty ORIGINAL continuous source for every ascending
ID, without asserting N-dependent physical prime-tuple realization. -/
theorem all14_witness_mem_original_source (i : Fin 14) :
    Source (.remaining (.ascending i)) (originalAscendingPoint i) := by
  apply all14_box_mem_original_source
  intro j
  simp

end
end ImbalancedChen.P4AOriginalFull87AscendingAllInteriors
