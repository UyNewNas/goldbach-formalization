import ImbalancedChen.P4AOriginalFull87SourceDictionary
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
28 NEW strict continuous-source interiors for the actual original
descending15 and ascendingPair13 cells (global indices 15..29,45..57).
Every row is the existing exported literal source, not a new policy
or an arithmetic N-dependent prime tuple. No saved87 witness claimed.
-/
namespace ImbalancedChen.P4AOriginalFull87DescAscPairInteriors
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

/-- Fresh exact points for all 15 original descending physical Source geometries.
    These are NOT the original numeric archive witness bytes. -/
def originalDescPointQ : Fin 15 → Fin 8 → ℚ :=
  ![
    ![16636967/100000000, 10353800/100000000, 9178917/100000000, 3374883/100000000, 2898483/100000000, 2897283/100000000, 2896083/100000000, 2894883/100000000],
    ![16288548/100000000, 11343880/100000000, 8188836/100000000, 4444956/100000000, 3644956/100000000, 3245702/100000000, 3244502/100000000, 3243302/100000000],
    ![16186639/100000000, 10988349/100000000, 8592507/100000000, 4595841/100000000, 3795841/100000000, 3395017/100000000, 3346411/100000000, 3345211/100000000],
    ![16296634/100000000, 11389699/100000000, 8143017/100000000, 4471909/100000000, 3671909/100000000, 3237616/100000000, 3236416/100000000, 3235216/100000000],
    ![16263443/100000000, 11067190/100000000, 8594035/100000000, 4673154/100000000, 4100000/100000000, 3398582/100000000, 3269607/100000000, 3268407/100000000],
    ![16216824/100000000, 10592332/100000000, 8941117/100000000, 5612493/100000000, 4980639/100000000, 3317426/100000000, 3316226/100000000, 3315026/100000000],
    ![16229845/100000000, 11549342/100000000, 7983375/100000000, 4679770/100000000, 3556901/100000000, 3304405/100000000, 3303205/100000000, 3302005/100000000],
    ![16258771/100000000, 11226467/100000000, 8584692/100000000, 5032305/100000000, 3909470/100000000, 3553188/100000000, 3274279/100000000, 3273079/100000000],
    ![16154967/100000000, 11880618/100000000, 7652098/100000000, 4219454/100000000, 4218254/100000000, 3434645/100000000, 3378083/100000000, 3376883/100000000],
    ![16310633/100000000, 11716251/100000000, 8321568/100000000, 4666501/100000000, 4561184/100000000, 3761184/100000000, 3222417/100000000, 3221217/100000000],
    ![16332965/100000000, 10672794/100000000, 8980534/100000000, 5736797/100000000, 4936797/100000000, 3321164/100000000, 3200085/100000000, 3198885/100000000],
    ![16334668/100000000, 10841358/100000000, 8691358/100000000, 5607536/100000000, 5234623/100000000, 3457536/100000000, 3198382/100000000, 3197182/100000000],
    ![16405671/100000000, 10298890/100000000, 9233826/100000000, 6158879/100000000, 4142011/100000000, 4140811/100000000, 3127379/100000000, 3126179/100000000],
    ![16694827/100000000, 10503709/100000000, 9029008/100000000, 5990205/100000000, 4515504/100000000, 4514304/100000000, 2838223/100000000, 2837023/100000000],
    ![16634243/100000000, 9927462/100000000, 9605255/100000000, 4970582/100000000, 4969382/100000000, 4958879/100000000, 2898807/100000000, 2897607/100000000]
  ]

def originalDescPoint (i : Fin 15) : Point :=
  fun j => (originalDescPointQ i j : ℝ)

/-- Fresh exact points for all 13 original ascending-pair Source geometries. -/
def originalPairPointQ : Fin 13 → Fin 8 → ℚ :=
  ![
    ![13603801/100000000, 10648465/100000000, 8877221/100000000, 5924291/100000000, 2961546/100000000, 2960346/100000000, 2959126/100000000, 2957916/100000000],
    ![14554425/100000000, 11618514/100000000, 7907136/100000000, 4973625/100000000, 3703911/100000000, 2940978/100000000, 2939711/100000000, 2938511/100000000],
    ![14362558/100000000, 11414292/100000000, 8111358/100000000, 5165492/100000000, 4100000/100000000, 3300000/100000000, 2952067/100000000, 2950867/100000000],
    ![14869159/100000000, 12096004/100000000, 7429646/100000000, 4658891/100000000, 4118556/100000000, 3318556/100000000, 2900000/100000000, 2775755/100000000],
    ![14413903/100000000, 11516981/100000000, 8008669/100000000, 5114147/100000000, 4408068/100000000, 3608068/100000000, 2900722/100000000, 2899522/100000000],
    ![13013780/100000000, 10176448/100000000, 9349238/100000000, 6514312/100000000, 3669571/100000000, 2842342/100000000, 2841122/100000000, 2839912/100000000],
    ![12814563/100000000, 10060965/100000000, 9464686/100000000, 6713487/100000000, 3356144/100000000, 3354944/100000000, 2976845/100000000, 2756198/100000000],
    ![13823492/100000000, 10875225/100000000, 8650425/100000000, 5704558/100000000, 5178133/100000000, 3300000/100000000, 2952067/100000000, 2950867/100000000],
    ![13847233/100000000, 10912533/100000000, 8613117/100000000, 5680817/100000000, 5239183/100000000, 3381400/100000000, 2938500/100000000, 2937300/100000000],
    ![13488588/100000000, 10529480/100000000, 8996170/100000000, 6039462/100000000, 4498685/100000000, 4497485/100000000, 2962907/100000000, 2961707/100000000],
    ![13510269/100000000, 10562003/100000000, 8963647/100000000, 6017781/100000000, 4552889/100000000, 4551689/100000000, 2952067/100000000, 2950867/100000000],
    ![13933712/100000000, 10736789/100000000, 8788861/100000000, 5594338/100000000, 5591938/100000000, 5152318/100000000, 3200723/100000000, 3199523/100000000],
    ![12801504/100000000, 10982774/100000000, 8542876/100000000, 6726546/100000000, 6724146/100000000, 6082424/100000000, 2633785/100000000, 1821330/100000000]
  ]

def originalPairPoint (i : Fin 13) : Point :=
  fun j => (originalPairPointQ i j : ℝ)

private def descRowQ (i : Fin 15) (a : Fin 9 → ℚ) : ℚ :=
  a 0 + ∑ j : Fin 8, a j.succ * originalDescPointQ i j

private def pairRowQ (i : Fin 13) (a : Fin 9 → ℚ) : ℚ :=
  a 0 + ∑ j : Fin 8, a j.succ * originalPairPointQ i j

private theorem desc_eval_eq (i : Fin 15) (a : Fin 9 → ℚ) :
    OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients a
      (originalDescPoint i) = (descRowQ i a : ℝ) := by
  simp only [OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
    descRowQ, originalDescPoint]
  push_cast
  rfl

private theorem pair_eval_eq (i : Fin 13) (a : Fin 9 → ℚ) :
    OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients a
      (originalPairPoint i) = (pairRowQ i a : ℝ) := by
  simp only [OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients,
    pairRowQ, originalPairPoint]
  push_cast
  rfl

/-- Exact coefficient checks against ALL 15*96 original exported descending
    literal rows. Smallest global margin of both families is 289/25000000. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem desc_literal_margin :
    ∀ i : Fin 15, ∀ r : Fin 96,
      (9/1000000 : ℚ) ≤
        descRowQ i (OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i r) := by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem pair_literal_margin :
    ∀ i : Fin 13, ∀ r : Fin 97,
      (9/1000000 : ℚ) ≤
        pairRowQ i (OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i r) := by
  intro i
  fin_cases i <;> decide

/-- Original maximum coordinate slope is 11/2, so the safe common bound is 6. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem desc_slope :
    ∀ i : Fin 15, ∀ r : Fin 96, ∀ j : Fin 8,
      |OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients
        i r j.succ| ≤ (6 : ℚ) := by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem pair_slope :
    ∀ i : Fin 13, ∀ r : Fin 97, ∀ j : Fin 8,
      |OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients
        i r j.succ| ≤ (6 : ℚ) := by
  intro i
  fin_cases i <;> decide

/-- Pure manuscript-internal affine perturbation bound, with the
    full original 8-coordinate coefficients and no geometric-to-arithmetic leap. -/
private theorem affine_perturbation
    (a : Fin 9 → ℚ) (u v : Point)
    (hc : ∀ j, |v j - u j| ≤ (1/100000000 : ℝ))
    (ha : ∀ j, |(a j.succ : ℝ)| ≤ 6) :
    |OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients a v -
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients a u| ≤
        (3/6250000 : ℝ) := by
  have heq :
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients a v -
        OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients a u =
        ∑ j : Fin 8, (a j.succ : ℝ) * (v j - u j) := by
    calc
      _ = (∑ j : Fin 8, (a j.succ : ℝ) * v j) -
          (∑ j : Fin 8, (a j.succ : ℝ) * u j) := by
            simp only [OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients]
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

/-- Every original descending row remains strictly above 1/125000
    within the positive-radius exact rational box. -/
theorem all15_original_desc_rows_box_slack (i : Fin 15) (s : Point)
    (hs : ∀ j, |s j - originalDescPoint i j| ≤ (1/100000000 : ℝ)) :
    ∀ r : Fin 96, (1/125000 : ℝ) ≤
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        (OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i r) s := by
  intro r
  let a := OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i r
  have hcentre : (9/1000000 : ℝ) ≤
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        a (originalDescPoint i) := by
    rw [desc_eval_eq]
    exact_mod_cast desc_literal_margin i r
  have hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 6 := by
    intro j
    exact_mod_cast desc_slope i r j
  have hdelta := affine_perturbation a (originalDescPoint i) s hs hcoeff
  have hleft := (abs_le.mp hdelta).1
  linarith

theorem all15_box_mem_original_source (i : Fin 15) (s : Point)
    (hs : ∀ j, |s j - originalDescPoint i j| ≤ (1/100000000 : ℝ)) :
    Source (.descending i) s := by
  change ∀ r : Fin 96, 0 <
    OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
      (OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i r) s
  intro r
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/125000)
    (all15_original_desc_rows_box_slack i s hs r)

theorem all15_centre_mem_original_source (i : Fin 15) :
    Source (.descending i) (originalDescPoint i) := by
  apply all15_box_mem_original_source
  intro j
  simp

/-- Likewise every one of the 13*97 original ascending-pair rows. -/
theorem all13_original_pair_rows_box_slack (i : Fin 13) (s : Point)
    (hs : ∀ j, |s j - originalPairPoint i j| ≤ (1/100000000 : ℝ)) :
    ∀ r : Fin 97, (1/125000 : ℝ) ≤
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        (OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i r) s := by
  intro r
  let a := OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i r
  have hcentre : (9/1000000 : ℝ) ≤
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        a (originalPairPoint i) := by
    rw [pair_eval_eq]
    exact_mod_cast pair_literal_margin i r
  have hcoeff : ∀ j, |(a j.succ : ℝ)| ≤ 6 := by
    intro j
    exact_mod_cast pair_slope i r j
  have hdelta := affine_perturbation a (originalPairPoint i) s hs hcoeff
  have hleft := (abs_le.mp hdelta).1
  linarith

theorem all13_box_mem_original_source (i : Fin 13) (s : Point)
    (hs : ∀ j, |s j - originalPairPoint i j| ≤ (1/100000000 : ℝ)) :
    Source (.ascendingPair i) s := by
  change ∀ r : Fin 97, 0 <
    OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
      (OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i r) s
  intro r
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/125000)
    (all13_original_pair_rows_box_slack i s hs r)

theorem all13_centre_mem_original_source (i : Fin 13) :
    Source (.ascendingPair i) (originalPairPoint i) := by
  apply all13_box_mem_original_source
  intro j
  simp

end
end ImbalancedChen.P4AOriginalFull87DescAscPairInteriors
