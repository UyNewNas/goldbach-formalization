import ImbalancedChen.P4AOriginalFull87SourceDictionary
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Genuine first-failure original H5 (7 cells, 100 rows each) and H7
(10 cells, 101 rows each), not a new or weakened Source.
The rational points are fresh feasibility reconstructions, NOT the
frozen saved87 witness bytes, an arithmetic prime-state supply,
or a dynamic-parent / signed-gain certificate.
-/
namespace ImbalancedChen.P4AOriginalFull87H5H7Interiors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

/-- Original remaining cells, H5 0..6 followed by H7 0..9;
the original global indices are 70..86. -/
def originalCell : Fin 17 → P4AOriginalRemainingEighthSources.Cell :=
  ![.h5 0, .h5 1, .h5 2, .h5 3, .h5 4, .h5 5, .h5 6,
    .h7 0, .h7 1, .h7 2, .h7 3, .h7 4, .h7 5, .h7 6, .h7 7, .h7 8, .h7 9]

/-- Numerator table for seventeen exact 8D rational points,
each coordinate divided by 100000000. -/
def originalPointQ : Fin 17 → Fin 8 → ℚ :=
  ![
    ![14594371/100000000, 12281926/100000000, 9722958/100000000, 4911679/100000000, 4851413/100000000, 2352711/100000000, 2342711/100000000, 2332644/100000000],
    ![14625012/100000000, 12404097/100000000, 9648276/100000000, 4873480/100000000, 4817638/100000000, 3000000/100000000, 2500000/100000000, 2241115/100000000],
    ![14482559/100000000, 12155678/100000000, 9817943/100000000, 5023491/100000000, 4877465/100000000, 2452907/100000000, 2442907/100000000, 2347081/100000000],
    ![14567637/100000000, 12352545/100000000, 9689667/100000000, 4938413/100000000, 4918237/100000000, 3000000/100000000, 2500000/100000000, 2235292/100000000],
    ![13584607/100000000, 11321892/100000000, 10480703/100000000, 5921443/100000000, 5019988/100000000, 3144171/100000000, 2292915/100000000, 2282915/100000000],
    ![14039382/100000000, 11913442/100000000, 10051003/100000000, 5466669/100000000, 4885113/100000000, 4028645/100000000, 2184064/100000000, 2146140/100000000],
    ![13937008/100000000, 11907318/100000000, 10077155/100000000, 5297763/100000000, 5196408/100000000, 4363179/100000000, 2059891/100000000, 2049891/100000000],
    ![15160335/100000000, 12849309/100000000, 8886760/100000000, 4345715/100000000, 3252675/100000000, 3000901/100000000, 2990901/100000000, 2331226/100000000],
    ![14565260/100000000, 12218919/100000000, 9372181/100000000, 4931800/100000000, 4129070/100000000, 3129070/100000000, 2946618/100000000, 2366540/100000000],
    ![15219975/100000000, 12966706/100000000, 8620308/100000000, 4286075/100000000, 3563251/100000000, 3016416/100000000, 3006416/100000000, 2273469/100000000],
    ![14562264/100000000, 12236335/100000000, 9372181/100000000, 4915603/100000000, 4159688/100000000, 3159688/100000000, 2946618/100000000, 2353339/100000000],
    ![13368621/100000000, 11044151/100000000, 10683000/100000000, 6137429/100000000, 3063714/100000000, 3053714/100000000, 3043714/100000000, 2344670/100000000],
    ![14326769/100000000, 12013510/100000000, 9851239/100000000, 5179282/100000000, 4515796/100000000, 2956744/100000000, 2706632/100000000, 2333458/100000000],
    ![14363398/100000000, 12086770/100000000, 9813487/100000000, 5142652/100000000, 4590178/100000000, 3066634/100000000, 2699901/100000000, 2296828/100000000],
    ![13934353/100000000, 11633438/100000000, 10229900/100000000, 5571697/100000000, 4107893/100000000, 3744719/100000000, 2399070/100000000, 2321114/100000000],
    ![13996598/100000000, 11763190/100000000, 10143984/100000000, 5509452/100000000, 4318301/100000000, 3892882/100000000, 2399070/100000000, 2253608/100000000],
    ![13828893/100000000, 11730638/100000000, 10185315/100000000, 5281276/100000000, 5050816/100000000, 4442146/100000000, 2128454/100000000, 2118454/100000000]
  ]

def originalPoint (i : Fin 17) : Point :=
  fun j => (originalPointQ i j : ℝ)

private def rowValue (i : Fin 17) (a : Fin 9 → ℚ) : ℚ :=
  a 0 + ∑ j : Fin 8, a j.succ * originalPointQ i j

private theorem real_row_eq_rational (i : Fin 17) (a : Fin 9 → ℚ) :
    P4AOriginalRemainingEighthSources.evalRow a (originalPoint i) =
      (rowValue i a : ℝ) := by
  simp only [P4AOriginalRemainingEighthSources.evalRow,
    rowValue, originalPoint]
  push_cast
  rfl

/-- Candidate kernel computation against all 1710 ORIGINAL strict rows.
The external exact-Fraction audit confirms the weaker bound 9/100000;
the minimum is 3999/40000000 at packet index 2, literal row 18.
This proof body has NOT been elaborated or kernel-evaluated. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem original_literal_row_margin :
    ∀ i : Fin 17,
    ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
      (9/100000 : ℚ) ≤
        rowValue i (P4AOriginalRemainingEighthSources.row (originalCell i) k) := by
  intro i
  fin_cases i <;> decide

/-- True maximal absolute coordinate slope in all 1710 rows is 9/2;
conservative 5 is used to avoid an unsound family-independent bound. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem original_literal_slope_bound :
    ∀ i : Fin 17,
    ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
    ∀ j : Fin 8,
      |P4AOriginalRemainingEighthSources.row
          (originalCell i) k j.succ| ≤ (5 : ℚ) := by
  intro i
  fin_cases i <;> decide

private theorem affine_perturbation
    (a : Fin 9 → ℚ) (u v : Point)
    (hcoordinate : ∀ j, |v j - u j| ≤ (1/1000000 : ℝ))
    (hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 5) :
    |P4AOriginalRemainingEighthSources.evalRow a v -
      P4AOriginalRemainingEighthSources.evalRow a u| ≤
        (1/25000 : ℝ) := by
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
    _ ≤ ∑ _j : Fin 8, (5 : ℝ) * (1/1000000 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hcoeff j) (hcoordinate j)
        (abs_nonneg _) (by norm_num)
    _ = (1/25000 : ℝ) := by norm_num

/-- Original 7*100 + 10*101 strict rows retain at least
9/100000 - 1/25000 = 1/20000 under radius 1/1000000.
The original H5/H7 priority/failure rows are NOT discarded. -/
theorem all17_original_rows_box_slack
    (i : Fin 17) (s : Point)
    (hs : ∀ j, |s j - originalPoint i j| ≤ (1/1000000 : ℝ)) :
    ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
      (1/20000 : ℝ) ≤
        P4AOriginalRemainingEighthSources.evalRow
          (P4AOriginalRemainingEighthSources.row (originalCell i) k) s := by
  intro k
  let a := P4AOriginalRemainingEighthSources.row (originalCell i) k
  have hcentre : (9/100000 : ℝ) ≤
      P4AOriginalRemainingEighthSources.evalRow a (originalPoint i) := by
    rw [real_row_eq_rational]
    exact_mod_cast original_literal_row_margin i k
  have hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 5 := by
    intro j
    exact_mod_cast original_literal_slope_bound i k j
  have hdelta := affine_perturbation a (originalPoint i) s hs hcoeff
  have hleft := (abs_le.mp hdelta).1
  linarith

/-- Direct membership in the SAME original full87 Source dictionary,
not physical N-dependent prime membership. -/
theorem all17_box_mem_original_source
    (i : Fin 17) (s : Point)
    (hs : ∀ j, |s j - originalPoint i j| ≤ (1/1000000 : ℝ)) :
    Source (.remaining (originalCell i)) s := by
  change ∀ k : Fin (P4AOriginalRemainingEighthSources.rowCount (originalCell i)),
      0 < P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalRemainingEighthSources.row (originalCell i) k) s
  intro k
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/20000)
    (all17_original_rows_box_slack i s hs k)

theorem all17_witness_mem_original_source (i : Fin 17) :
    Source (.remaining (originalCell i)) (originalPoint i) := by
  apply all17_box_mem_original_source
  intro j
  simp

end
end ImbalancedChen.P4AOriginalFull87H5H7Interiors
