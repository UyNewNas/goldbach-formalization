import ImbalancedChen.P5U7ActualRoughRowReconstruction
import ImbalancedChen.P5U7OriginalInteriorCompatibility
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The genuine rough-mother minus ACTUAL target-excluding U7 source mass is
o(N/log N), on the matched strict interior. The explicit payment retains
the actual marked pair and both prime/ordered-semiprime branches.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7ActualInteriorSourceMass (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta, p5U7OriginalRowMass N t

def p5U7ActualInteriorRoughMass (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    (roughCount ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ)

def p5U7ActualTargetLossCoefficient (N : ℕ) : ℝ :=
  25 * (Real.log (N : ℝ) / Real.log 2 + 2) *
    (Real.log (N : ℝ) / (N : ℝ) ^ (59 / 250 : ℝ))

theorem p5U7ActualInterior_pair_mass_le {N : ℕ} (hN : 2 ≤ N) (eta : ℝ)
    (houter : p5U7BoundaryOuterReciprocalMass N ≤ 5) :
    (∑ t ∈ p5U7InteriorSelector N eta, 1 / ((t.1 * t.2 : ℕ) : ℝ)) ≤ 25 := by
  have hsub := p5U7InteriorSelector_subset_band hN eta
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (show ∀ t ∈ p5U7InteriorPairs N eta, t ∉ p5U7InteriorSelector N eta →
      (0 : ℝ) ≤ 1 / ((t.1 * t.2 : ℕ) : ℝ) by intros; positivity)
  have hweak := p5U7Interior_pair_mass_le_outer_square N eta
  have houter0 : 0 ≤ p5U7BoundaryOuterReciprocalMass N := by
    unfold p5U7BoundaryOuterReciprocalMass
    exact Finset.sum_nonneg (by intros; positivity)
  exact hh.trans (hweak.trans (by nlinarith only [houter0, houter]))

theorem p5U7ActualInterior_loss_le {N : ℕ} (hN : 2 ≤ N) (eta : ℝ)
    (houter : p5U7BoundaryOuterReciprocalMass N ≤ 5) :
    0 ≤ p5U7ActualInteriorRoughMass N eta - p5U7ActualInteriorSourceMass N eta ∧
      p5U7ActualInteriorRoughMass N eta - p5U7ActualInteriorSourceMass N eta ≤
        25 * (Real.log (N : ℝ) / Real.log 2 + 2) *
          ((N : ℝ) / (N : ℝ) ^ (59 / 250 : ℝ)) := by
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hA : 0 < (N : ℝ) ^ (59 / 250 : ℝ) := Real.rpow_pos_of_pos hNR _
  have hL : 0 ≤ Real.log (N : ℝ) / Real.log 2 := div_nonneg
    (Real.log_natCast_nonneg N) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hRows : ∀ t ∈ p5U7InteriorSelector N eta,
      0 ≤ (roughCount ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) - p5U7OriginalRowMass N t ∧
      (roughCount ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) - p5U7OriginalRowMass N t ≤
        (Real.log (N : ℝ) / Real.log 2 + 2) * ((N : ℝ) / (N : ℝ) ^ (59 / 250 : ℝ)) *
          (1 / ((t.1 * t.2 : ℕ) : ℝ)) := by
    intro t ht
    have hto := (Finset.mem_filter.mp ht).1
    have hg := p5U7Mass_outer_geometry hto
    have hc := (Finset.mem_filter.mp hto).1
    have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
    have hz : (0 : ℝ) < t.2 := by exact_mod_cast hp.pos
    have hx : (0 : ℝ) < (N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ) := hz.trans hg.2.2.1
    have hratio1 : 1 ≤ ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) / (t.2 : ℝ) :=
      (one_le_div hz).mpr hg.2.2.1.le
    have hratio : ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) / (t.2 : ℝ) ≤
        ((N : ℝ) / (N : ℝ) ^ (59 / 250 : ℝ)) * (1 / ((t.1 * t.2 : ℕ) : ℝ)) := by
      have hh := div_le_div_of_nonneg_left hx.le hA hg.2.1
      convert hh using 1 <;> ring
    have hgap := p5U7Actual_rough_row_gap_le hN0 hto
    refine ⟨hgap.1, ?_⟩
    have hunit : (2 : ℝ) ≤ 2 * (((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) / (t.2 : ℝ)) := by
      linarith only [hratio1]
    have hbound := mul_le_mul_of_nonneg_left hratio (show 0 ≤ Real.log (N : ℝ) / Real.log 2 + 2 by linarith only [hL])
    dsimp only [p5U7OriginalRowMass]
    nlinarith only [hgap.2, hunit, hbound]
  unfold p5U7ActualInteriorRoughMass p5U7ActualInteriorSourceMass
  rw [← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_nonneg (fun t ht => (hRows t ht).1), ?_⟩
  have hh := Finset.sum_le_sum (fun t ht => (hRows t ht).2)
  have hmass := p5U7ActualInterior_pair_mass_le hN eta houter
  have hfactor : 0 ≤ (Real.log (N : ℝ) / Real.log 2 + 2) *
      ((N : ℝ) / (N : ℝ) ^ (59 / 250 : ℝ)) := by positivity
  have htotal := mul_le_mul_of_nonneg_left hmass hfactor
  rw [← Finset.mul_sum] at hh
  nlinarith only [hh, htotal]

theorem p5U7ActualTargetLossCoefficient_tendsto_zero :
    Tendsto p5U7ActualTargetLossCoefficient atTop (𝓝 0) := by
  have h2 := (tendsto_nat_log_pow_div_rpow 2 (by norm_num : (0 : ℝ) < 59 / 250)).const_mul
    ((25 : ℝ) / Real.log 2)
  have h1 := (tendsto_nat_log_pow_div_rpow 1 (by norm_num : (0 : ℝ) < 59 / 250)).const_mul (50 : ℝ)
  have hh := h2.add h1
  convert hh using 1
  · funext N
    dsimp only [p5U7ActualTargetLossCoefficient]
    ring
  · simp only [mul_zero, zero_add]

theorem tendsto_p5U7ActualInterior_target_loss (eta : ℝ) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      (p5U7ActualInteriorRoughMass N eta - p5U7ActualInteriorSourceMass N eta)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ p5U7ActualTargetLossCoefficient_tendsto_zero
  · filter_upwards [eventually_ge_atTop (2 : ℕ), p5U7Boundary_eventually_outer_mass_le_five] with N hN houter
    have hgap := (p5U7ActualInterior_loss_le hN eta houter).1
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (Nat.cast_nonneg N)) hgap
  · filter_upwards [eventually_ge_atTop (2 : ℕ), p5U7Boundary_eventually_outer_mass_le_five] with N hN houter
    have hgap := (p5U7ActualInterior_loss_le hN eta houter).2
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hh := mul_le_mul_of_nonneg_left hgap
      (div_nonneg (Real.log_natCast_nonneg N) (Nat.cast_nonneg N))
    convert hh using 1 <;> dsimp only [p5U7ActualTargetLossCoefficient] <;>
      field_simp [hNR.ne'] <;> ring

end

end ImbalancedChen
