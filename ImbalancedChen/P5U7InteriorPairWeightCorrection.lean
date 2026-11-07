import ImbalancedChen.P5U7InteriorDoublePrimeTest
import ImbalancedChen.P5U7OriginalOmegaFubini

/-!
SOURCE_ONLY / UNCOMPILED. The fixed-interior U7 prime-pair sum arising from
the original Buchstab main has raw weight 1/(p₁p₂). The double-test transport
uses the actual prime-box weight 1/((p₁-1)(p₂-1)). This file keeps the original
labelled selector and Buchstab test and bounds their exact finite difference.
No rough-count error or ordinary-eight allowance is used.
-/

namespace ImbalancedChen

noncomputable section

open LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7InteriorRawTestSum (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    (1 / ((t.1 : ℝ) * (t.2 : ℝ))) *
      p5U7InteriorTest (actualPrimeTupleLog N ![t.1, t.2])

/-- Exact correction for one ordered pair, with no asymptotic replacement. -/
theorem p5U7_pair_weight_identity {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (1 / (a - 1)) * (1 / (b - 1)) - 1 / (a * b) =
      ((1 / (a - 1)) * (1 / (b - 1))) *
        (1 / a + 1 / b - 1 / (a * b)) := by
  have ha0 : a ≠ 0 := ne_of_gt (by linarith : 0 < a)
  have hb0 : b ≠ 0 := ne_of_gt (by linarith : 0 < b)
  have ha1 : a - 1 ≠ 0 := ne_of_gt (by linarith : 0 < a - 1)
  have hb1 : b - 1 ≠ 0 := ne_of_gt (by linarith : 0 < b - 1)
  field_simp [ha0, hb0, ha1, hb1]
  <;> ring

/-- The actual-vs-raw reciprocal correction is nonnegative and at most
`2/D` of the actual prime-box weight whenever both primes exceed `D`. -/
theorem p5U7_pair_weight_correction_bound {D a b : ℝ}
    (hD : 0 < D) (ha : 1 < a) (hb : 1 < b)
    (hDa : D ≤ a) (hDb : D ≤ b) :
    0 ≤ (1 / (a - 1)) * (1 / (b - 1)) - 1 / (a * b) ∧
      (1 / (a - 1)) * (1 / (b - 1)) - 1 / (a * b) ≤
        (2 / D) * ((1 / (a - 1)) * (1 / (b - 1))) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hs : 0 ≤ (1 / (a - 1)) * (1 / (b - 1)) := by positivity
  have hraw : 0 ≤ 1 / (a * b) := by positivity
  have hraw_a : 1 / (a * b) ≤ 1 / a := by
    apply (div_le_div_iff₀ (mul_pos ha0 hb0) ha0).mpr
    nlinarith
  have hinva : 1 / a ≤ 1 / D := one_div_le_one_div_of_le hD hDa
  have hinvb : 1 / b ≤ 1 / D := one_div_le_one_div_of_le hD hDb
  have hlow : 0 ≤ 1 / a + 1 / b - 1 / (a * b) := by linarith
  have hupp : 1 / a + 1 / b - 1 / (a * b) ≤ 2 / D := by
    have htwo : 1 / D + 1 / D = 2 / D := by ring
    linarith
  rw [p5U7_pair_weight_identity ha hb]
  exact ⟨mul_nonneg hs hlow, mul_le_mul_of_nonneg_left hupp hs⟩

/-- A bound directly in terms of the original unshifted source weight. -/
theorem p5U7_pair_weight_correction_le_raw {D a b : ℝ}
    (hD : 0 < D) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hDa : D ≤ a) (hDb : D ≤ b) :
    (1 / (a - 1)) * (1 / (b - 1)) - 1 / (a * b) ≤
      (8 / D) * (1 / (a * b)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hainv : 1 / (a - 1) ≤ 2 / a := by
    apply (div_le_div_iff₀ ha1 ha0).mpr
    nlinarith
  have hbinv : 1 / (b - 1) ≤ 2 / b := by
    apply (div_le_div_iff₀ hb1 hb0).mpr
    nlinarith
  have hfour : (1 / (a - 1)) * (1 / (b - 1)) ≤
      4 * (1 / (a * b)) := by
    calc
      _ ≤ (2 / a) * (1 / (b - 1)) :=
        mul_le_mul_of_nonneg_right hainv (by positivity)
      _ ≤ (2 / a) * (2 / b) :=
        mul_le_mul_of_nonneg_left hbinv (by positivity)
      _ = 4 * (1 / (a * b)) := by
        field_simp [ne_of_gt ha0, ne_of_gt hb0]
        <;> ring
  have htwo := (p5U7_pair_weight_correction_bound hD
    (by linarith : 1 < a) (by linarith : 1 < b) hDa hDb).2
  have hcoef : 0 ≤ 2 / D := by positivity
  have hh := mul_le_mul_of_nonneg_left hfour hcoef
  calc
    _ ≤ (2 / D) * ((1 / (a - 1)) * (1 / (b - 1))) := htwo
    _ ≤ (2 / D) * (4 * (1 / (a * b))) := hh
    _ = (8 / D) * (1 / (a * b)) := by ring

private theorem p5U7Interior_pair_geometry {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} {t : ℕ × ℕ} (ht : t ∈ p5U7InteriorSelector N eta) :
    2 ≤ (t.1 : ℝ) ∧ 2 ≤ (t.2 : ℝ) ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (t.1 : ℝ) ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (t.2 : ℝ) := by
  obtain ⟨hsel, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc, hD, horder, _⟩ := Finset.mem_filter.mp hsel
  obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hc
  have hp1 := (mem_chenAdditivePrimeCarrier.mp hc1).2.1
  have hp2 := (mem_chenAdditivePrimeCarrier.mp hc2).2.1
  have hp1two : 2 ≤ t.1 := hp1.two_le
  have hp2two : 2 ≤ t.2 := hp2.two_le
  have horderR : (t.1 : ℝ) ≤ (t.2 : ℝ) := by
    exact_mod_cast horder.le
  exact ⟨by exact_mod_cast hp1two,
    by exact_mod_cast hp2two, hD, hD.trans horderR⟩

private theorem p5U7Interior_test_nonneg {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) {t : ℕ × ℕ}
    (ht : t ∈ p5U7InteriorSelector N eta) :
    0 ≤ p5U7InteriorTest (actualPrimeTupleLog N ![t.1, t.2]) := by
  have hp := (p5U7Interior_selector_iff_box hN heta ![t.1, t.2]).mp ht
  obtain ⟨hbox, hint⟩ := Finset.mem_filter.mp hp
  have hlogbox := ((mem_actualPrimeBoxTuples_log_iff
    (show 1 < N by omega) _ _ ![t.1, t.2]).mp hbox).2
  have hs := p5U7Interior_subset_original heta hlogbox hint
  have hc : p5U7OmegaClosedSupport
      (actualPrimeTupleLog N ![t.1, t.2] 0)
      (actualPrimeTupleLog N ![t.1, t.2] 1) :=
    ⟨hs.1, hs.2.1, hs.2.2.le⟩
  have hb := (p5U7Omega_buchstab_zero_one hc).1
  have hu := (p5U7Omega_closed_geometry hc).2.1
  change 0 ≤ buchstab (p5U7OmegaArgument
    (actualPrimeTupleLog N ![t.1, t.2] 0)
    (actualPrimeTupleLog N ![t.1, t.2] 1)) /
    (actualPrimeTupleLog N ![t.1, t.2] 1)
  exact div_nonneg hb hu.le

/-- Finite original-source correction on exactly the same labelled prime
pair and strict fixed-eta Omega interior. -/
theorem p5U7Interior_raw_to_shifted_bound {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ p5U7InteriorLabelledTestSum N eta - p5U7InteriorRawTestSum N eta ∧
      p5U7InteriorLabelledTestSum N eta - p5U7InteriorRawTestSum N eta ≤
        (2 / ((N : ℝ) ^ (59 / 250 : ℝ))) *
          p5U7InteriorLabelledTestSum N eta := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hD : 0 < (N : ℝ) ^ (59 / 250 : ℝ) := Real.rpow_pos_of_pos hNpos _
  let S := p5U7InteriorSelector N eta
  let H : ℕ × ℕ → ℝ := fun t =>
    p5U7InteriorTest (actualPrimeTupleLog N ![t.1, t.2])
  let A : ℕ × ℕ → ℝ := fun t =>
    (1 / ((t.1 : ℝ) - 1)) * (1 / ((t.2 : ℝ) - 1))
  let R : ℕ × ℕ → ℝ := fun t => 1 / ((t.1 : ℝ) * (t.2 : ℝ))
  have hrow (t : ℕ × ℕ) (ht : t ∈ S) :
      0 ≤ A t * H t - R t * H t ∧
        A t * H t - R t * H t ≤ (2 / ((N : ℝ) ^ (59 / 250 : ℝ))) * (A t * H t) := by
    obtain ⟨ha, hb, hDa, hDb⟩ := p5U7Interior_pair_geometry hN ht
    have hw := p5U7_pair_weight_correction_bound hD
      (by linarith : 1 < (t.1 : ℝ)) (by linarith : 1 < (t.2 : ℝ)) hDa hDb
    have hH : 0 ≤ H t := p5U7Interior_test_nonneg hN heta ht
    dsimp [A, R, H] at hw hH ⊢
    constructor
    · nlinarith [mul_nonneg hw.1 hH]
    · have hh := mul_le_mul_of_nonneg_right hw.2 hH
      nlinarith only [hh]
  change 0 ≤ (∑ t ∈ S, A t * H t) - (∑ t ∈ S, R t * H t) ∧
    (∑ t ∈ S, A t * H t) - (∑ t ∈ S, R t * H t) ≤
      (2 / ((N : ℝ) ^ (59 / 250 : ℝ))) * (∑ t ∈ S, A t * H t)
  rw [← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg fun t ht => (hrow t ht).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht => (hrow t ht).2

/-- The same correction is bounded against the *raw* original source sum,
which makes explicit that no ordinary-eight error budget absorbs it. -/
theorem p5U7Interior_raw_to_shifted_bound_by_raw {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 ≤ eta) :
    p5U7InteriorLabelledTestSum N eta - p5U7InteriorRawTestSum N eta ≤
      (8 / ((N : ℝ) ^ (59 / 250 : ℝ))) *
        p5U7InteriorRawTestSum N eta := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hD : 0 < (N : ℝ) ^ (59 / 250 : ℝ) := Real.rpow_pos_of_pos hNpos _
  let S := p5U7InteriorSelector N eta
  let H : ℕ × ℕ → ℝ := fun t =>
    p5U7InteriorTest (actualPrimeTupleLog N ![t.1, t.2])
  let A : ℕ × ℕ → ℝ := fun t =>
    (1 / ((t.1 : ℝ) - 1)) * (1 / ((t.2 : ℝ) - 1))
  let R : ℕ × ℕ → ℝ := fun t => 1 / ((t.1 : ℝ) * (t.2 : ℝ))
  have hrow (t : ℕ × ℕ) (ht : t ∈ S) :
      A t * H t - R t * H t ≤
        (8 / ((N : ℝ) ^ (59 / 250 : ℝ))) * (R t * H t) := by
    obtain ⟨ha, hb, hDa, hDb⟩ := p5U7Interior_pair_geometry hN ht
    have hw := p5U7_pair_weight_correction_le_raw hD ha hb hDa hDb
    have hH : 0 ≤ H t := p5U7Interior_test_nonneg hN heta ht
    have hh := mul_le_mul_of_nonneg_right hw hH
    dsimp [A, R, H] at hh ⊢
    nlinarith only [hh]
  change (∑ t ∈ S, A t * H t) - (∑ t ∈ S, R t * H t) ≤
    (8 / ((N : ℝ) ^ (59 / 250 : ℝ))) * (∑ t ∈ S, R t * H t)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun t ht => hrow t ht

end

end ImbalancedChen
