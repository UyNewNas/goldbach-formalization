import ImbalancedChen.ActualSieveGapTailBounds
import ImbalancedChen.ActualThirdOriginalLocalCurvature

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

Rational enclosures for the literal, amplitude-normalized Suzuki F, f and D.
The first-strip suppliers below are finite rational expressions, proved from
mathlib's logarithm inequalities and the genuine source formulas.  The tail
supplier improves the previously available coefficient 3 to 920559/1000000.
No target node, final integral, or currentK/currentC endpoint bound is assumed.

This does not close the manuscript numerical certificate.  Beyond the first
strip a sharp table still needs the stored-node/chord recurrence checks; the
quadratic tail alone does not replace those checks or the final quadratures.
-/

namespace ImbalancedChen.P2ContinuousSieveRational

noncomputable section

open scoped BigOperators
open OriginalU2CoupledRecurrenceSourceOnly
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

/-- Rational lower Taylor approximation to log(q-1), for q >= 2. -/
def logLower (n : ℕ) (q : ℚ) : ℚ :=
  2 * ∑ k ∈ Finset.range n, ((q - 2) / q) ^ (2 * k + 1) / (2 * k + 1)

/-- Rational upper approximation with the proved geometric remainder. -/
def logUpper (n : ℕ) (q : ℚ) : ℚ :=
  logLower n q + 2 * ((q - 2) / q) ^ (2 * n + 1) /
    (1 - ((q - 2) / q) ^ 2)

/-- The exact original normalized gap, sharing the original factors. -/
def D (s : ℝ) : ℝ := actualSieveGap s / A

theorem D_eq_upper_sub_lower (s : ℝ) : D s = upper s - lower s := by
  unfold D actualSieveGap upper lower thirdTailLowerFactor
  rw [sub_div]

/-- A rational Taylor calculation encloses the actual logarithm, including q=2. -/
theorem log_bounds (n : ℕ) (q : ℚ) (hq : 2 ≤ q) :
    (logLower n q : ℝ) ≤ Real.log ((q : ℝ) - 1) ∧
      Real.log ((q : ℝ) - 1) ≤ (logUpper n q : ℝ) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  let z : ℝ := ((q : ℝ) - 2) / (q : ℝ)
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hqpos.le
  have hz1 : z < 1 := by
    apply (div_lt_iff₀ hqpos).2
    linarith
  have hratio : (1 + z) / (1 - z) = (q : ℝ) - 1 := by
    apply (div_eq_iff (by linarith : 1 - z ≠ 0)).2
    dsimp [z]
    field_simp [ne_of_gt hqpos]
    <;> ring
  have hl := Real.sum_range_le_log_div hz0 hz1 n
  have hu := Real.log_div_le_sum_range_add hz0 hz1 n
  rw [hratio] at hl hu
  have hlcast : (logLower n q : ℝ) =
      2 * ∑ k ∈ Finset.range n, z ^ (2 * k + 1) / (2 * k + 1) := by
    dsimp [logLower, z]
    push_cast
    <;> rfl
  have hucast : (logUpper n q : ℝ) =
      (logLower n q : ℝ) + 2 * z ^ (2 * n + 1) / (1 - z ^ 2) := by
    dsimp [logUpper, z]
    push_cast
    <;> rfl
  constructor
  · rw [hlcast]
    linarith only [hl]
  · rw [hucast, hlcast]
    linarith only [hu]

/-- The first-strip f-node is enclosed by finite rational expressions. -/
theorem lower_rational_node_bounds (n : ℕ) (q : ℚ)
    (hq2 : 2 ≤ q) (hq4 : q ≤ 4) :
    ((logLower n q / q : ℚ) : ℝ) ≤ lower (q : ℝ) ∧
      lower (q : ℝ) ≤ ((logUpper n q / q : ℚ) : ℝ) := by
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq4R : (q : ℝ) ≤ 4 := by exact_mod_cast hq4
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  obtain ⟨hl, hu⟩ := log_bounds n q hq2
  rw [lower_eq_log hq2R hq4R]
  constructor
  · simpa only [Rat.cast_div] using div_le_div_of_nonneg_right hl hqpos.le
  · simpa only [Rat.cast_div] using div_le_div_of_nonneg_right hu hqpos.le

/-- Literal F-node on its exact first strip. -/
theorem upper_rational_node_eq (q : ℚ) (hq1 : 1 < q) (hq3 : q ≤ 3) :
    upper (q : ℝ) = ((1 / q : ℚ) : ℝ) := by
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq3R : (q : ℝ) ≤ 3 := by exact_mod_cast hq3
  simpa only [Rat.cast_div, Rat.cast_one] using upper_eq_inv hq1R hq3R

/-- Literal D-node on [2,3], with the direction of the f bounds reversed. -/
theorem D_rational_node_bounds (n : ℕ) (q : ℚ)
    (hq2 : 2 ≤ q) (hq3 : q ≤ 3) :
    (((1 - logUpper n q) / q : ℚ) : ℝ) ≤ D (q : ℝ) ∧
      D (q : ℝ) ≤ (((1 - logLower n q) / q : ℚ) : ℝ) := by
  obtain ⟨hl, hu⟩ := lower_rational_node_bounds n q hq2 (by linarith)
  have hF := upper_rational_node_eq q (by linarith) hq3
  rw [D_eq_upper_sub_lower, hF]
  push_cast at hl hu ⊢
  constructor <;> linarith only [hl, hu]

/-- Endpoint rational calculations enclose the actual f throughout a cell.
The cell endpoints may extend as far as 4, matching the genuine log strip. -/
theorem lower_rational_cell_bounds (n : ℕ) (a b : ℚ) (s : ℝ)
    (ha : 2 ≤ a) (hb : b ≤ 4) (has : (a : ℝ) ≤ s) (hsb : s ≤ (b : ℝ)) :
    ((logLower n a / a : ℚ) : ℝ) ≤ lower s ∧
      lower s ≤ ((logUpper n b / b : ℚ) : ℝ) := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ 4 := by exact_mod_cast hb
  have hab : a ≤ b := by exact_mod_cast (has.trans hsb)
  have hla := (lower_rational_node_bounds n a ha (hab.trans hb)).1
  have hub := (lower_rational_node_bounds n b (ha.trans hab) hb).2
  exact ⟨hla.trans (lower_monotone haR (haR.trans has) has),
    (lower_monotone (haR.trans has) (haR.trans (has.trans hsb)) hsb).trans hub⟩

/-- Rational endpoint calculations enclose D on a full first-strip cell. -/
theorem D_rational_cell_bounds (n : ℕ) (a b : ℚ) (s : ℝ)
    (ha : 2 ≤ a) (hb : b ≤ 3) (has : (a : ℝ) ≤ s) (hsb : s ≤ (b : ℝ)) :
    (((1 - logUpper n b) / b : ℚ) : ℝ) ≤ D s ∧
      D s ≤ (((1 - logLower n a) / a : ℚ) : ℝ) := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hab : a ≤ b := by exact_mod_cast (has.trans hsb)
  have hDb := (D_rational_node_bounds n b (ha.trans hab) hb).1
  have hDa := (D_rational_node_bounds n a ha (hab.trans hb)).2
  have hleft : D s ≤ D (a : ℝ) :=
    div_le_div_of_nonneg_right
      (antitoneOn_actualSieveGap haR (haR.trans has) has) A_pos.le
  have hright : D (b : ℝ) ≤ D s :=
    div_le_div_of_nonneg_right
      (antitoneOn_actualSieveGap (haR.trans has) (haR.trans (has.trans hsb)) hsb)
      A_pos.le
  exact ⟨hDb.trans hright, hleft.trans hDa⟩

/-- Seven exact Taylor terms suffice for this rational seed interval. -/
theorem log_two_bounds : (693147 : ℝ) / 1000000 ≤ Real.log 2 ∧
    Real.log 2 ≤ (693148 : ℝ) / 1000000 := by
  have hl := Real.sum_range_le_log_div
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 7
  have hu := Real.log_div_le_sum_range_add
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hl hu
  constructor <;> linarith only [hl, hu]

/-- The literal normalized D seed has an exact rational two-sided enclosure. -/
theorem D_three_bounds : (306852 : ℝ) / 3000000 ≤ D 3 ∧
    D 3 ≤ (306853 : ℝ) / 3000000 := by
  have heq : D 3 = (1 - Real.log 2) / 3 := actualSieveGap_normalized_at_three
  rw [heq]
  obtain ⟨hl, hu⟩ := log_two_bounds
  constructor <;> linarith only [hl, hu]

/-- A genuine rational tail supplier, without a numerical tail premise. -/
theorem D_le_rational_quadratic_tail {s : ℝ} (hs : 3 ≤ s) :
    D s ≤ (920559 : ℝ) / (1000000 * s ^ 2) := by
  have htail := actualSieveGap_normalized_le_quadratic_tail
    (s0 := (3 : ℝ)) (by norm_num) hs
  change D s ≤ D 3 * (3 / s) ^ 2 at htail
  have hseed := D_three_bounds.2
  have hspos : 0 < s := by linarith
  calc
    D s ≤ D 3 * (3 / s) ^ 2 := htail
    _ ≤ ((306853 : ℝ) / 3000000) * (3 / s) ^ 2 :=
      mul_le_mul_of_nonneg_right hseed (sq_nonneg _)
    _ = (920559 : ℝ) / (1000000 * s ^ 2) := by
      field_simp [ne_of_gt hspos]
      <;> ring

/-- A rational cell left endpoint supplies a uniform tail enclosure for D. -/
theorem D_rational_tail_cell_bounds (a : ℚ) (s : ℝ)
    (ha : 3 ≤ a) (has : (a : ℝ) ≤ s) :
    0 ≤ D s ∧ D s ≤ ((920559 / (1000000 * a ^ 2) : ℚ) : ℝ) := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha2 : (2 : ℝ) ≤ (a : ℝ) := by linarith
  have hs2 : 2 ≤ s := ha2.trans has
  constructor
  · exact div_nonneg (actualSieveGap_nonneg hs2) A_pos.le
  · have hmono : D s ≤ D (a : ℝ) :=
      div_le_div_of_nonneg_right (antitoneOn_actualSieveGap ha2 hs2 has) A_pos.le
    have htail := hmono.trans (D_le_rational_quadratic_tail haR)
    convert htail using 1 <;> push_cast <;> rfl

/-- The same literal tail controls the F/f separation, with the exact
normalization used by the original continuous-sieve recurrence. -/
theorem upper_le_lower_add_rational_tail {s : ℝ} (hs : 3 ≤ s) :
    upper s ≤ lower s + (920559 : ℝ) / (1000000 * s ^ 2) := by
  have h := D_le_rational_quadratic_tail hs
  rw [D_eq_upper_sub_lower] at h
  linarith only [h]

end

end ImbalancedChen.P2ContinuousSieveRational
