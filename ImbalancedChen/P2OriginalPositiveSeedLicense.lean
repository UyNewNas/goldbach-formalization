import ImbalancedChen.P2SimultaneousTableIteration
import MathlibNt.Wu2008DoubleSieve.PositiveGainActual

/-!
SOURCE_ONLY / UNCOMPILED / OPEN30.

The adopted seed 2327/100000 on the first sixty H cells is NOT proved in
this file. The original certificate reads it from the four-round W2 seed
J_(n+1)=20249/1000000+(13/100)J_n, J_0=1/50. Its mathematical license is
second-seed-certified-finite-feedback.tex, with the enhanced stable-ceiling
and switched-product conditions inherited from second-seed-stable-prefix.
An exact rational recurrence check is not a proof of those licenses.

A genuine nonzero source seed IS available: PositiveGainActual proves the
actual Wu first-functional action at (29/10,31/10), including its surviving
fixed-delta switched penalty. It gives H_delta >= 1/5000 on [1,29/10].
Below we turn this into (i) a uniform positive actual source count estimate
on the original [1,11/5] support, with the correct epsilon/threshold order;
(ii) a strictly positive 80-bit integer seed on exactly the original sixty
cells; (iii) nonzero, sound simultaneous ordinary iterations for every finite
round count, including 430; and (iv) a new positive actual H(3) feedback
consequence. The smaller seed is explicitly distinguished from the adopted
2327/100000 seed, rather than substituted for its claimed gain.

The actual source family is `wuSourceBox`, at fixed 0<delta<=1/10. Its
identification with the enhanced stable-prefix family remains open. The
positive W1 witness has t=31/10; it is not misidentified as one of the saved
restricted bank's even-tenth s0 values. Sibling imports require the draft
directory to be staged as a source root. No build or numerical replay ran.
-/

namespace ImbalancedChen.P2OriginalPositiveSeedSourceOnly

noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
open Wu2008DoubleSieve
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open ImbalancedChen.P2TableActionSourceOnly
open ImbalancedChen.P2SimultaneousTableSourceOnly

/-- This is the exact first-functional action, including its delta penalty.
No positive lower bound on H or h is assumed in its proof. -/
theorem actual_w1_positive_seed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (1/5000 : ℝ) ≤ H δ (29/10) := by
  have hp : (1/5000 : ℝ) ≤ firstFunctionalGainPsi δ (29/10) (31/10) := by
    rw [firstFunctionalGainPsi_eq_log δ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    convert positiveGain_explicit_seed hδhi using 1 <;> norm_num
  have hf := wuImprovementLimit_firstFunctionalGain hδ hδhi
    (by norm_num : (2 : ℝ) ≤ 29/10) (by norm_num : (29/10 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) ≤ 31/10) (by norm_num : (31/10 : ℝ) ≤ 5) (by norm_num)
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 31/10) (by norm_num : (31/10 : ℝ) ≤ 10)
  have hi := firstFunctionalGain_integral_nonneg hδ (by linarith : δ < 1/2)
    (by norm_num : (2 : ℝ) ≤ 29/10) (by norm_num : (29/10 : ℝ) ≤ 31/10)
    (by norm_num : (3 : ℝ) ≤ 31/10) (by norm_num : (31/10 : ℝ) ≤ 5)
  change (1/5000 : ℝ) ≤ wuImprovementLimit true δ (29/10)
  linarith

theorem actual_short_support_positive {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hs : 1 ≤ s) (hsS : s ≤ 11/5) :
    (1/5000 : ℝ) ≤ H δ s := by
  exact (actual_w1_positive_seed hδ hδhi).trans
    (wuImprovementLimit_upper_antitone hδ hδhi
      ⟨hs, by linarith⟩ ⟨by norm_num, by norm_num⟩ (by linarith))

/-- A single threshold works over the entire original short support at
every fixed depth. The strict epsilon is removed only in a limit statement,
not silently dropped from finite source comparisons. -/
theorem actual_short_support_uniform_admissible (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℝ, 1 ≤ s → s ≤ 11/5 →
      (1/5000 : ℝ) - ε ∈ wuAdmissibleImprovements true (k+1) δ s T := by
  have hhalf : δ < 1/2 := by linarith
  have hmem := wuImprovementLimit_sub_mem true k hδ hhalf
    (by norm_num : (1 : ℝ) ≤ 29/10) (by norm_num : (29/10 : ℝ) ≤ 10) hε
  have hw := wuEventualImprovements_downward true (k+1) (by omega)
    hδ hhalf (by norm_num : (1 : ℝ) ≤ 29/10)
    (by norm_num : (29/10 : ℝ) ≤ 10)
    (show (1/5000 : ℝ)-ε ≤ wuImprovementLimit true δ (29/10)-ε by
      have hh := actual_w1_positive_seed hδ hδhi
      change (1/5000 : ℝ) ≤ wuImprovementLimit true δ (29/10) at hh
      linarith) hmem
  obtain ⟨T, hT⟩ := hw
  refine ⟨T, ?_⟩
  intro s hs hsS
  have hm := wuAdmissibleImprovements_upper_shift hδ hhalf hs
    (show s ≤ (29/10 : ℝ) by linarith) hT
  have hAs : wuUpperCoefficient s = 1 :=
    jr1965F_normalized_initial (by linarith) (by linarith)
  have hAt : wuUpperCoefficient (29/10) = 1 :=
    jr1965F_normalized_initial (by norm_num) (by norm_num)
  simpa only [hAs, hAt, add_sub_cancel_right] using hm

/-- An actual positive count improvement with its source, normalization,
uniform support, and fixed-depth/common-threshold quantifiers exposed. -/
theorem actual_short_support_uniform_count (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → 4 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox (k+1) δ N i Δ V →
      ∀ s : ℝ, 1 ≤ s → s ≤ 11/5 →
        wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
          (1 - 1/5000 + ε) *
            boxTheta N ((N : ℝ) ^ (1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT⟩ := actual_short_support_uniform_admissible k hδ hδhi hε
  refine ⟨T, ?_⟩
  intro N hN hN4 he i Δ V hb s hs hsS
  have hc := hT s hs hsS N hN hN4 he i Δ V hb
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
    (wuUpperCoefficient s - (1/5000-ε)) *
      boxTheta N ((N : ℝ) ^ (1/2-δ)) (convolutionWuWindows N Δ V) at hc
  have hAs : wuUpperCoefficient s = 1 :=
    jr1965F_normalized_initial (by linarith) (by linarith)
  rw [hAs] at hc
  convert hc using 1 <;> ring

/-- Literal downward 80-bit rounding of the proved positive amount. -/
def positiveSeedNumerator : ℤ := ⌊(tableQ : ℝ) / 5000⌋

theorem positiveSeedNumerator_pos : 0 < positiveSeedNumerator := by
  norm_num [positiveSeedNumerator, tableQ]

theorem positiveSeedNumerator_bound : (positiveSeedNumerator : ℝ) / tableQ ≤ 1/5000 := by
  have hQ : (0 : ℝ) < tableQ := by exact_mod_cast tableQ_pos
  apply (div_le_iff₀ hQ).2
  calc
    (positiveSeedNumerator : ℝ) ≤ (tableQ : ℝ) / 5000 := Int.floor_le _
    _ = (1/5000 : ℝ) * tableQ := by ring

/-- The SAME original sixty-cell support; a smaller, proved nonzero value. -/
def positiveSeed (upper : Bool) (i : Fin 200) : ℤ :=
  if upper then if i.val < 60 then positiveSeedNumerator else 0 else 0

theorem positiveSeed_support_count :
    (Finset.univ.filter (fun p : Bool × Fin 200 => p.1 = true ∧ p.2.val < 60)).card = 60 := by
  decide

theorem positiveSeed_nonnegative : Nonnegative positiveSeed := by
  intro upper i
  cases upper
  · exact le_rfl
  · simp only [positiveSeed, if_true]
    split_ifs
    · exact positiveSeedNumerator_pos.le
    · exact le_rfl

theorem original_short_support_grid {i : Fin 200} (hi : i.val < 60) :
    1 ≤ tableGrid (i.val+1) ∧ tableGrid (i.val+1) ≤ 11/5 := by
  have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
  constructor
  · exact hb.1
  · dsimp [tableGrid]
    rw [Nat.cast_add]
    norm_num
    have hile : (i.val : ℝ) ≤ 59 := by exact_mod_cast (show i.val ≤ 59 by omega)
    linarith

/-- No seed bound is a premise: the actual W1 positive action proves it. -/
theorem positiveSeed_sound {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Sound δ positiveSeed := by
  intro upper i
  have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
  have hz := wuImprovementLimit_nonneg upper hδ (by linarith : δ < 1/2)
    hb.1 (hb.2.trans (by norm_num))
  cases upper
  · simpa only [positiveSeed, Bool.false_eq_true, if_false, Int.cast_zero, zero_div] using hz
  · simp only [positiveSeed, if_true]
    split_ifs with hi
    · have hsupport := original_short_support_grid hi
      exact positiveSeedNumerator_bound.trans
        (actual_short_support_positive hδ hδhi hsupport.1 hsupport.2)
    · simpa only [Int.cast_zero, zero_div] using hz

theorem positiveSeed_strict_on_support (i : Fin 200) (hi : i.val < 60) :
    0 < positiveSeed true i := by
  simpa only [positiveSeed, if_true, if_pos hi] using positiveSeedNumerator_pos

/-- This is strictly smaller than the adopted original seed numerator.
It therefore cannot be used as its missing numerical gain certificate. -/
theorem positiveSeedNumerator_lt_adopted :
    positiveSeedNumerator < ⌊(tableQ : ℝ) * (2327/100000)⌋ := by
  norm_num [positiveSeedNumerator, tableQ]

/-- Sound, genuinely nonzero finite iterations of licensed ordinary actions. -/
theorem positive_seed_iteration_sound (W : LogWeights) (bank : List Action) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (rounds : ℕ) :
    Sound δ (iterateFrom W bank positiveSeed rounds) := by
  exact iterateFrom_sound W bank hδ hδhi positiveSeed_nonnegative
    (positiveSeed_sound hδ hδhi) rounds

theorem positive_seed_iteration_preserves_positive (W : LogWeights) (bank : List Action)
    (rounds : ℕ) (i : Fin 200) (hi : i.val < 60) :
    0 < iterateFrom W bank positiveSeed rounds true i := by
  exact (positiveSeed_strict_on_support i hi).trans_le
    (iterateFrom_mono W bank positiveSeed 0 rounds (Nat.zero_le _) true i)

theorem positive_seed_430_sound (W : LogWeights) (bank : List Action) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Sound δ (iterateFrom W bank positiveSeed 430) ∧
      ∀ i : Fin 200, i.val < 60 → 0 < iterateFrom W bank positiveSeed 430 true i := by
  exact ⟨positive_seed_iteration_sound W bank hδ hδhi 430,
    fun i hi => positive_seed_iteration_preserves_positive W bank 430 i hi⟩

/-- A further genuinely positive actual gain at argument three, obtained
by two Buchstab transfers from the proved W1 seed, with no seed assumption. -/
theorem actual_positive_H_three {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (9/420500 : ℝ) ≤ H δ 3 := by
  have hhalf : δ < 1/2 := by linarith
  have hc := wuImprovementLimit_upper_cross hδ hδhi (by norm_num : (2 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) ≤ 39/10) (by norm_num : (39/10 : ℝ) ≤ 10)
  have hn := wuImprovementLimit_nonneg true hδ hhalf
    (by norm_num : (1 : ℝ) ≤ 39/10) (by norm_num : (39/10 : ℝ) ≤ 10)
  have hm : (∫ u in (2 : ℝ)..(29/10), (1/42050 : ℝ)) ≤
      ∫ u in (2 : ℝ)..(29/10), wuImprovementLimit false δ u / u := by
    apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (wuImprovementLimit_div_intervalIntegrable false hδ hhalf
        (by norm_num) (by norm_num) (by norm_num))
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    apply (le_div_iff₀ hu0).2
    have hl := positiveGain_actual_lower_range hδ hδhi hu.1
      (show u ≤ (39/10 : ℝ) by linarith [hu.2])
    calc
      (1/42050 : ℝ) * u ≤ (1/42050 : ℝ) * (29/10) :=
        mul_le_mul_of_nonneg_left hu.2 (by norm_num)
      _ = 1/14500 := by norm_num
      _ ≤ (39/10-u)/14500 := by linarith [hu.2]
      _ ≤ _ := hl
  have he : (∫ u in (2 : ℝ)..(29/10), (1/42050 : ℝ)) = 9/420500 := by
    norm_num [intervalIntegral.integral_const, smul_eq_mul]
  rw [he] at hm
  norm_num at hc
  change (9/420500 : ℝ) ≤ wuImprovementLimit true δ 3
  linarith

end
end ImbalancedChen.P2OriginalPositiveSeedSourceOnly
