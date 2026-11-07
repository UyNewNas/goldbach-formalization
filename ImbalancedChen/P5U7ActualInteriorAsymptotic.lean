import ImbalancedChen.P5U7ActualInteriorTargetLoss
import ImbalancedChen.P5U7OriginalRawMean

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual original U7 strict-interior source asymptotic. The marked-pair
rough count is compared BOTH ways with the actual target-excluding prime
and ordered-semiprime source; all divisor/unit/endpoint losses are paid.
The existing genuine band3 error and matched double-prime PNT main are
then used. No desired source/main limit or coefficient supplier is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

/-- The strict selector's actual band3 error is dominated by the existing
weak-selector reserve. Their two gates are not identified or interchanged. -/
theorem p5U7ActualInterior_strict_rough_error_le {N : ℕ} (hN : 2 ≤ N) (eta : ℝ)
    (hstart : primeErrorStart ≤ (N : ℝ) ^ (59 / 250 : ℝ)) :
    |p5U7ActualInteriorRoughMass N eta - p5U7MassBuchstabInteriorMain N eta| ≤
      p5U7InteriorBandError N eta := by
  unfold p5U7ActualInteriorRoughMass p5U7MassBuchstabInteriorMain
  rw [← Finset.sum_sub_distrib]
  have hRows : (∑ t ∈ p5U7InteriorSelector N eta,
      |(roughCount ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) -
        ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) *
          buchstab (Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) / Real.log (t.2 : ℝ)) /
            Real.log (t.2 : ℝ)|) ≤
      ∑ t ∈ p5U7InteriorSelector N eta, p5U7InteriorBandRowError N t := by
    apply Finset.sum_le_sum
    intro t ht
    have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
    exact roughCount_buchstab_band_error 3 (by norm_num)
      (hstart.trans hg.2.1) hg.2.2.1.le hg.2.2.2
  have hReserve : (∑ t ∈ p5U7InteriorSelector N eta, p5U7InteriorBandRowError N t) ≤
      p5U7InteriorBandError N eta := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (p5U7InteriorSelector_subset_band hN eta)
    intro t ht _
    exact p5U7Interior_row_error_nonneg hstart ht
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hRows.trans hReserve)

theorem tendsto_p5U7ActualInterior_rough_main_difference (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      (p5U7ActualInteriorRoughMass N eta - p5U7MassBuchstabInteriorMain N eta)) atTop (𝓝 0) := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ) ^ (59 / 250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' ?_ (p5U7Interior_band_error_normalized_tendsto_zero eta heta)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hgrowth.eventually (eventually_ge_atTop primeErrorStart)]
    with N hN hstart
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 ≤ Real.log (N : ℝ) / (N : ℝ) := div_nonneg hLog.le hNR.le
  have hh := mul_le_mul_of_nonneg_left (p5U7ActualInterior_strict_rough_error_le hN eta hstart) hscale
  have heq : (Real.log (N : ℝ) / (N : ℝ)) * p5U7InteriorBandError N eta =
      p5U7InteriorBandError N eta / ((N : ℝ) / Real.log (N : ℝ)) := by
    field_simp [hNR.ne', hLog.ne']
    <;> ring
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hscale, heq] using hh

/-- Actual finite rough-mother transport on the MATCHED strict eta gate.
The double-prime main limit is the proved PNT test-integral theorem. -/
theorem tendsto_p5U7ActualInteriorRoughMass_normalized (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) * p5U7ActualInteriorRoughMass N eta)
      atTop (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  have hh := (tendsto_p5U7ActualInterior_rough_main_difference eta heta).add
    (tendsto_p5U7MassBuchstabInteriorMain_normalized heta.le)
  convert hh using 1
  · funext N
    ring
  · simp only [zero_add]

/-- The ACTUAL target-excluding prime plus ordered-semiprime U7 source
has the genuine K=1 Buchstab interior integral as its leading coefficient.
All outer labels, repeated terminal prime factors, and both branches are
retained. Eta is fixed first; no boundary collar is declared negligible. -/
theorem tendsto_p5U7ActualInteriorSourceMass_normalized (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) * p5U7ActualInteriorSourceMass N eta)
      atTop (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  have hh := (tendsto_p5U7ActualInteriorRoughMass_normalized eta heta).sub
    (tendsto_p5U7ActualInterior_target_loss eta)
  convert hh using 1
  · funext N
    ring
  · simp only [sub_zero]

end

end ImbalancedChen
