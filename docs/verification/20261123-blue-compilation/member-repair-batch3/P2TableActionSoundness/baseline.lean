import MathlibNt.Wu2008DoubleSieve.ImprovementCrossLower
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / OPEN30.

Semantic lower-enclosure lemmas for the positive actions in the shared table.
`H` and `h` below are the actual Wu source improvement functions, not arrays
defined by a recurrence. In particular `rounded_buchstab_upper_sound` and
`rounded_buchstab_lower_sound` prove ordinary Buchstab action soundness from
previous-generation endpoint enclosures and certified logarithmic weights.
The per-product rounding is exactly floor(v*w/Q)/Q, with Q = 2^80 available
without changing any manuscript constant. Adjacent minima and retention by
maximum are proved against these same actual functions.

These are NOT the full 106-action / 430-round certificate. The positive W1
feedback integral is also connected to the actual h, but the typed enhanced
W1/W2 baseline and switched-cost licenses, the 106 concrete rational action
records, their certified coefficient bounds, and the stronger uniformity in
the manuscript's enhanced stable-prefix family are still missing. The Wu
source family used here is explicitly `wuSourceBox`, at fixed small delta.
No result here identifies that family with the enhanced manuscript family.
There is consequently no seed-to-430 or final 400-entry theorem in this file.

The repository manifest pins goldbach to
09b97db5764ade1246bfb77206baa1b124760958. Read-only suppliers were inspected
under native-packages/goldbach/research/wu2008/src/MathlibNt/Wu2008DoubleSieve.
Their availability under that manifest pin has not been verified by a build.
These imports require that source root; this draft is uncompiled/unreplayed.
-/

namespace ImbalancedChen.P2TableActionSourceOnly

noncomputable section
open Set MeasureTheory
open scoped BigOperators Interval
open Wu2008DoubleSieve

/-- The actual normalized source upper improvement. -/
def H (δ s : ℝ) : ℝ := wuImprovementLimit true δ s

/-- The actual normalized source lower improvement. -/
def h (δ s : ℝ) : ℝ := wuImprovementLimit false δ s

/-- The selected shared-table denominator. No array is generated here. -/
def tableQ : ℕ := 2 ^ 80

theorem tableQ_pos : 0 < tableQ := by norm_num [tableQ]

/-- One product in the integer implementation, normalized back to reals. -/
def roundedProduct (Q : ℕ) (v w : ℤ) : ℝ :=
  (⌊(v : ℝ) * (w : ℝ) / (Q : ℝ)⌋ : ℝ) / (Q : ℝ)

/-- Exact adapter to integer Euclidean division used by the saved replay.
In particular the semantic lemma below does not replace integer floors by
an unrounded product. This identity also covers zero Q algebraically. -/
theorem roundedProduct_eq_ediv (Q : ℕ) (v w : ℤ) :
    roundedProduct Q v w = (((v * w / (Q : ℤ) : ℤ) : ℝ) / (Q : ℝ)) := by
  unfold roundedProduct
  rw [← Int.cast_mul, Int.floor_div_natCast, Int.floor_intCast]

theorem roundedProduct_le (Q : ℕ) (hQ : 0 < Q) (v w : ℤ) :
    roundedProduct Q v w ≤ ((v : ℝ) / Q) * ((w : ℝ) / Q) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc
    roundedProduct Q v w ≤ ((v : ℝ) * (w : ℝ) / Q) / Q :=
      div_le_div_of_nonneg_right (Int.floor_le _) hQr.le
    _ = _ := by ring

theorem roundedProduct_mono {Q : ℕ} (hQ : 0 < Q)
    {v v' w : ℤ} (hvv' : v ≤ v') (hw : 0 ≤ w) :
    roundedProduct Q v w ≤ roundedProduct Q v' w := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  apply div_le_div_of_nonneg_right _ hQr.le
  exact_mod_cast Int.floor_mono
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hvv')
        (by exact_mod_cast hw)) hQr.le)

private theorem actual_antitone (upper : Bool) {δ a b : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : (if upper then 1 else 2 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    wuImprovementLimit upper δ b ≤ wuImprovementLimit upper δ a := by
  cases upper
  · exact wuImprovementLimit_lower_antitone hδ hδhi
      ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
  · exact wuImprovementLimit_upper_antitone hδ hδhi
      ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab

/-- Endpoint enclosure of a real gain gives a genuine enclosure on the cell.
The lower side is used only above two, as required by the source theorem. -/
theorem actual_cell_enclosure (upper : Bool) {δ a b c : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : (if upper then 1 else 2 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 10)
    (hc : c ≤ wuImprovementLimit upper δ b) :
    ∀ u ∈ Icc a b, c ≤ wuImprovementLimit upper δ u := by
  intro u hu
  exact hc.trans (actual_antitone upper hδ hδhi (ha.trans hu.1) hu.2 hb)

/-- A certified rational logarithmic weight and an old endpoint enclosure
soundly pay one rounded feedback contribution to the actual source integral.
Neither a next-generation endpoint bound nor an action-result bound is an
input. Both positivity conditions are on the stored input numerators. -/
theorem rounded_log_cell_sound (upper : Bool) {δ a b : ℝ}
    {Q : ℕ} {v w : ℤ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hQ : 0 < Q) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (ha : (if upper then 1 else 2 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 10)
    (hvbound : (v : ℝ) / Q ≤ wuImprovementLimit upper δ b)
    (hwbound : (w : ℝ) / Q ≤ Real.log (b / a)) :
    roundedProduct Q v w ≤
      ∫ u in a..b, wuImprovementLimit upper δ u / u := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha1 : 1 ≤ a := by cases upper <;> simp_all <;> linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hv0 : 0 ≤ (v : ℝ) / Q := div_nonneg (by exact_mod_cast hv) hQr.le
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    rw [uIcc_of_le hab]
    intro u hu
    exact ne_of_gt (ha0.trans_le hu.1)
  have hconst : IntervalIntegrable (fun u : ℝ => ((v : ℝ) / Q) / u) volume a b := by
    simpa only [div_eq_mul_inv] using hinv.const_mul ((v : ℝ) / Q)
  have hreal := wuImprovementLimit_div_intervalIntegrable upper hδ
    (by linarith : δ < 1 / 2) ha1 hab hb
  have hcmp := intervalIntegral.integral_mono_on hab hconst hreal (fun u hu =>
    div_le_div_of_nonneg_right
      (actual_cell_enclosure upper hδ hδhi ha hab hb hvbound u hu)
      (ha0.trans_le hu.1).le)
  have heval : (∫ u in a..b, ((v : ℝ) / Q) / u) =
      ((v : ℝ) / Q) * Real.log (b / a) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hb0]
  rw [heval] at hcmp
  exact (roundedProduct_le Q hQ v w).trans
    ((mul_le_mul_of_nonneg_left hwbound hv0).trans hcmp)

/-- Sum of the actual per-product floors, using only previous endpoint
enclosures. The partition can be a suffix of the original 200-cell grid. -/
theorem rounded_log_tail_sound (upper : Bool) {δ : ℝ}
    {Q n : ℕ} (x : ℕ → ℝ) (v w : ℕ → ℤ)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hQ : 0 < Q)
    (hcells : ∀ j < n,
      (if upper then 1 else 2 : ℝ) ≤ x j ∧ x j ≤ x (j+1) ∧ x (j+1) ≤ 10)
    (hv : ∀ j < n, 0 ≤ v j) (hw : ∀ j < n, 0 ≤ w j)
    (hvbound : ∀ j < n, (v j : ℝ) / Q ≤ wuImprovementLimit upper δ (x (j+1)))
    (hwbound : ∀ j < n, (w j : ℝ) / Q ≤ Real.log (x (j+1) / x j)) :
    (∑ j ∈ Finset.range n, roundedProduct Q (v j) (w j)) ≤
      ∫ u in x 0..x n, wuImprovementLimit upper δ u / u := by
  have hi (j : ℕ) (hj : j < n) :
      IntervalIntegrable (fun u => wuImprovementLimit upper δ u / u)
        volume (x j) (x (j+1)) := by
    have ha : 1 ≤ x j := by
      have hh := (hcells j hj).1
      cases upper <;> simp_all <;> linarith
    exact wuImprovementLimit_div_intervalIntegrable upper hδ
      (by linarith : δ < 1 / 2) ha (hcells j hj).2.1 (hcells j hj).2.2
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply Finset.sum_le_sum
  intro j hj
  have hjn := Finset.mem_range.mp hj
  exact rounded_log_cell_sound upper hδ hδhi hQ (hv j hjn) (hw j hjn)
    (hcells j hjn).1 (hcells j hjn).2.1 (hcells j hjn).2.2
    (hvbound j hjn) (hwbound j hjn)

/-- The literal 200-cell shared grid: cell j is [grid j, grid (j+1)]. -/
def tableGrid (j : ℕ) : ℝ := 1 + (j : ℝ) / 50

theorem tableGrid_mono : Monotone tableGrid := by
  intro a b hab
  dsimp [tableGrid]
  exact add_le_add_left
    (div_le_div_of_nonneg_right (by exact_mod_cast hab) (by norm_num)) _

theorem tableGrid_bounds {j : ℕ} (hj : j ≤ 200) :
    1 ≤ tableGrid j ∧ tableGrid j ≤ 5 := by
  have hjr : (j : ℝ) ≤ 200 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  dsimp [tableGrid]
  constructor <;> linarith

theorem tableGrid_lower_start {i : ℕ} (hi : 50 ≤ i) :
    tableGrid (i-49) = tableGrid (i+1) - 1 := by
  dsimp [tableGrid]
  rw [Nat.cast_sub (by omega : 49 ≤ i), Nat.cast_add]
  norm_num
  ring

theorem tableGrid_upper_start {i : ℕ} (hi : 50 ≤ i) :
    tableGrid (max 50 (i-49)) = max 2 (tableGrid (i+1) - 1) := by
  have hmax (a b : ℕ) : tableGrid (max a b) = max (tableGrid a) (tableGrid b) := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, max_eq_right (tableGrid_mono hab)]
    · rw [max_eq_left hba, max_eq_left (tableGrid_mono hba)]
  rw [hmax, tableGrid_lower_start hi]
  norm_num [tableGrid]

/-- This is the exact suffix shape in the replay: the lower action starts
at i-49, and the upper action starts at max(50,i-49). Every summand is old
data from the same generation, on indices strictly below 200. -/
theorem rounded_original_grid_tail_sound (upper : Bool) {δ : ℝ}
    {Q k : ℕ} (v w : ℕ → ℤ)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hQ : 0 < Q) (hk : k ≤ 200)
    (hklo : (if upper then 0 else 50 : ℕ) ≤ k)
    (hv : ∀ j < 200, 0 ≤ v j) (hw : ∀ j < 200, 0 ≤ w j)
    (hvbound : ∀ j < 200,
      (v j : ℝ) / Q ≤ wuImprovementLimit upper δ (tableGrid (j+1)))
    (hwbound : ∀ j < 200,
      (w j : ℝ) / Q ≤ Real.log (tableGrid (j+1) / tableGrid j)) :
    (∑ j ∈ Finset.range (200-k), roundedProduct Q (v (k+j)) (w (k+j))) ≤
      ∫ u in tableGrid k..5, wuImprovementLimit upper δ u / u := by
  have hcells (j : ℕ) (hj : j < 200-k) :
      (if upper then 1 else 2 : ℝ) ≤ tableGrid (k+j) ∧
      tableGrid (k+j) ≤ tableGrid (k+(j+1)) ∧ tableGrid (k+(j+1)) ≤ 10 := by
    have hlast : k+(j+1) ≤ 200 := by omega
    have hlo : (if upper then 1 else 2 : ℝ) ≤ tableGrid (k+j) := by
      cases upper
      · have h50 : 50 ≤ k+j := by simp only [Bool.false_eq_true, if_false] at hklo; omega
        have hh := tableGrid_mono h50
        simpa [tableGrid] using hh
      · exact (tableGrid_bounds (show k+j ≤ 200 by omega)).1
    exact ⟨hlo, tableGrid_mono (by omega),
      (tableGrid_bounds hlast).2.trans (by norm_num)⟩
  have ht := rounded_log_tail_sound upper (fun j => tableGrid (k+j))
    (fun j => v (k+j)) (fun j => w (k+j)) hδ hδhi hQ hcells
    (fun j hj => hv (k+j) (by omega)) (fun j hj => hw (k+j) (by omega))
    (fun j hj => by simpa only [Nat.add_assoc] using hvbound (k+j) (by omega))
    (fun j hj => by simpa only [Nat.add_assoc] using hwbound (k+j) (by omega))
  have hend : k + (200-k) = 200 := Nat.add_sub_of_le hk
  have hstart : tableGrid (k+0) = tableGrid k := by rw [Nat.add_zero]
  have hfinish : tableGrid (k+(200-k)) = 5 := by
    rw [hend]
    norm_num [tableGrid]
  simpa only [hstart, hfinish] using ht

/-- The ordinary lower action, with the comparison made at argument six.
Discarding h(6) is licensed by its proved nonnegativity, not an input. -/
theorem buchstab_lower_integral_sound {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs : 2 ≤ s) (hs5 : s ≤ 5) :
    (∫ u in (s-1)..5, H δ u / u) ≤ h δ s := by
  have hc := wuImprovementLimit_lower_cross hδ hδhi hs
    (show s ≤ 6 by linarith) (show (6 : ℝ) ≤ 10 by norm_num)
  have hn := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1 / 2)
    (show (1 : ℝ) ≤ 6 by norm_num) (show (6 : ℝ) ≤ 10 by norm_num)
  norm_num at hc
  change (∫ u in (s-1)..5, wuImprovementLimit true δ u / u) ≤
    wuImprovementLimit false δ s
  linarith

/-- The ordinary upper action has the required lower-child clamp at two. -/
theorem buchstab_upper_integral_sound {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hs : 2 ≤ s) (hs5 : s ≤ 5) :
    (∫ u in (max 2 (s-1))..5, h δ u / u) ≤ H δ s := by
  let r : ℝ := max 3 s
  have hr3 : 3 ≤ r := le_max_left _ _
  have hsr : s ≤ r := le_max_right _ _
  have hr5 : r ≤ 5 := max_le (by norm_num) hs5
  have hrshift : r - 1 = max 2 (s-1) := by
    dsimp [r]
    by_cases h3 : 3 ≤ s
    · rw [max_eq_right h3, max_eq_right (by linarith)]
    · have hs3 : s ≤ 3 := by linarith
      rw [max_eq_left hs3, max_eq_left (by linarith)]
  have hc := wuImprovementLimit_upper_cross hδ hδhi (by linarith : 2 ≤ r)
    (show r ≤ 6 by linarith) (show (6 : ℝ) ≤ 10 by norm_num)
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1 / 2)
    (show (1 : ℝ) ≤ 6 by norm_num) (show (6 : ℝ) ≤ 10 by norm_num)
  have hm := wuImprovementLimit_upper_antitone hδ hδhi
    ⟨by linarith : 1 ≤ s, by linarith : s ≤ 10⟩
    ⟨by linarith : 1 ≤ r, by linarith : r ≤ 10⟩ hsr
  norm_num at hc
  rw [hrshift] at hc
  change (∫ u in (max 2 (s-1))..5, wuImprovementLimit false δ u / u) ≤
    wuImprovementLimit true δ s
  linarith

/-- Full soundness of one rounded ordinary upper action. -/
theorem rounded_buchstab_upper_sound {δ s : ℝ} {Q n : ℕ}
    (x : ℕ → ℝ) (v w : ℕ → ℤ)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hQ : 0 < Q)
    (hs : 2 ≤ s) (hs5 : s ≤ 5)
    (hx0 : x 0 = max 2 (s-1)) (hxn : x n = 5)
    (hcells : ∀ j < n, 2 ≤ x j ∧ x j ≤ x (j+1) ∧ x (j+1) ≤ 10)
    (hv : ∀ j < n, 0 ≤ v j) (hw : ∀ j < n, 0 ≤ w j)
    (hvbound : ∀ j < n, (v j : ℝ) / Q ≤ h δ (x (j+1)))
    (hwbound : ∀ j < n, (w j : ℝ) / Q ≤ Real.log (x (j+1) / x j)) :
    (∑ j ∈ Finset.range n, roundedProduct Q (v j) (w j)) ≤ H δ s := by
  have ht := rounded_log_tail_sound false x v w hδ hδhi hQ hcells hv hw hvbound hwbound
  rw [hx0, hxn] at ht
  exact ht.trans (buchstab_upper_integral_sound hδ hδhi hs hs5)

/-- Full soundness of one rounded ordinary lower action. Upper children in
the physical range [1,2) are admitted rather than silently discarded. -/
theorem rounded_buchstab_lower_sound {δ s : ℝ} {Q n : ℕ}
    (x : ℕ → ℝ) (v w : ℕ → ℤ)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hQ : 0 < Q)
    (hs : 2 ≤ s) (hs5 : s ≤ 5) (hx0 : x 0 = s-1) (hxn : x n = 5)
    (hcells : ∀ j < n, 1 ≤ x j ∧ x j ≤ x (j+1) ∧ x (j+1) ≤ 10)
    (hv : ∀ j < n, 0 ≤ v j) (hw : ∀ j < n, 0 ≤ w j)
    (hvbound : ∀ j < n, (v j : ℝ) / Q ≤ H δ (x (j+1)))
    (hwbound : ∀ j < n, (w j : ℝ) / Q ≤ Real.log (x (j+1) / x j)) :
    (∑ j ∈ Finset.range n, roundedProduct Q (v j) (w j)) ≤ h δ s := by
  have ht := rounded_log_tail_sound true x v w hδ hδhi hQ hcells hv hw hvbound hwbound
  rw [hx0, hxn] at ht
  exact ht.trans (buchstab_lower_integral_sound hδ hδhi hs hs5)

/-- Positive W1 feedback on one cell, after the exact change of variables
u = c*v in the supplier. This proves the rounded feedback contribution
against the actual h integral. It does not assert the missing W1 switched
cost inequality, nor the license of an enhanced-prefix W1 action. -/
theorem rounded_w1_feedback_cell_sound {δ a b c : ℝ}
    {Q : ℕ} {v w : ℤ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hQ : 0 < Q) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) (hbc : b < c)
    (hvbound : (v : ℝ) / Q ≤ h δ b)
    (hwbound : (w : ℝ) / Q ≤
      Real.log (b * (c-a) / (a * (c-b)))) :
    roundedProduct Q v w ≤
      ∫ u in a..b, h δ u * firstFeedbackWeightedKernel c u := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha0 : 0 < a := by linarith
  have hv0 : 0 ≤ (v : ℝ) / Q := div_nonneg (by exact_mod_cast hv) hQr.le
  have hk := firstFeedbackWeightedKernel_continuousOn ha0 hab hbc
  have hi : IntervalIntegrable (fun u => h δ u * firstFeedbackWeightedKernel c u)
      volume a b := by
    exact (wuImprovementLimit_intervalIntegrable false hδ
      (by linarith : δ < 1 / 2) (by linarith : 1 ≤ a) hab hb).mul_continuousOn hk
  have hi0 : IntervalIntegrable (fun u => ((v : ℝ) / Q) *
      firstFeedbackWeightedKernel c u) volume a b :=
    hk.intervalIntegrable.const_mul ((v : ℝ) / Q)
  have hcmp := intervalIntegral.integral_mono_on hab hi0 hi (fun u hu =>
    mul_le_mul_of_nonneg_right
      (actual_cell_enclosure false hδ hδhi ha hab hb hvbound u hu)
      (firstFeedbackWeightedKernel_nonneg (ha0.trans_le hu.1) (hu.2.trans_lt hbc)))
  have heval : (∫ u in a..b, ((v : ℝ) / Q) * firstFeedbackWeightedKernel c u) =
      ((v : ℝ) / Q) * Real.log (b * (c-a) / (a * (c-b))) := by
    rw [intervalIntegral.integral_const_mul,
      firstFeedbackWeightedKernel_integral ha0 hab hbc]
  rw [heval] at hcmp
  exact (roundedProduct_le Q hQ v w).trans
    ((mul_le_mul_of_nonneg_left hwbound hv0).trans hcmp)

/-- An adjacent minimum is a lower enclosure on the whole actual cell. -/
theorem adjacent_min_sound (upper : Bool) {δ a b l r : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (ha : (if upper then 1 else 2 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 10)
    (hr : r ≤ wuImprovementLimit upper δ b) :
    ∀ u ∈ Icc a b, min l r ≤ wuImprovementLimit upper δ u := by
  exact actual_cell_enclosure upper hδ hδhi ha hab hb ((min_le_right l r).trans hr)

/-- Retention by maximum preserves a proved actual enclosure. This is the
causal step used after both candidates have been obtained from old inputs. -/
theorem retain_max_sound (upper : Bool) {δ s old candidate : ℝ}
    (hold : old ≤ wuImprovementLimit upper δ s)
    (hcandidate : candidate ≤ wuImprovementLimit upper δ s) :
    max old candidate ≤ wuImprovementLimit upper δ s := by
  exact max_le hold hcandidate

end
end ImbalancedChen.P2TableActionSourceOnly
