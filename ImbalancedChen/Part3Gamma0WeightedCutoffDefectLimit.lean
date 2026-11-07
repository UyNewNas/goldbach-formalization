import ImbalancedChen.Part3ActualModularCutoffEnergyBudget
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For the actual modular cutoff on Gamma0(N), the mass weighted by ANY
integrable nonnegative density tends to its full mass, while the actual
gradient-cutoff error tends to zero. The integer-matrix height bound
proves pointwise eventual constancy; no boundedness of the defect vector
is assumed. Thus the unweighted cutoff energy O(index/Y), by itself
insufficient for an arbitrary L2 vector, is not used as a weighted bound.
The missing adjoint L2 -> local H1 and legal cutoff-square test join
remain separate. No essential self-adjointness is concluded here.
-/

namespace ImbalancedChen.Part3.Gamma0WeightedCutoffDefectLimit20261026a
noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a
open Gamma0ParabolicCosetRows20261025a
open Gamma0ActualParabolicUnfolding20261025a
open Gamma0ActualHighCuspTail20261025a
open GammaInfinityTranslationStrip20261025a
open ActualParabolicHighSeedLocalFinite20261025a
open ActualCuspStripCutoff20261025a
open ActualModularSmoothCuspCutoff20261025a
open ActualModularSmoothCutoffL2Tail20261025a
open ActualModularCutoffGradient20261025a
open ActualModularCutoffEnergyBudget20261025a

def cutoffHeight (n : ℕ) : ℝ := (n : ℝ) + 2

theorem cutoffHeight_gt_one (n : ℕ) : 1 < cutoffHeight n := by
  unfold cutoffHeight
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem cutoffHeight_pos (n : ℕ) : 0 < cutoffHeight n :=
  lt_trans (by norm_num) (cutoffHeight_gt_one n)

theorem cutoffHeight_tendsto : Tendsto cutoffHeight atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
    (fun n => by dsimp [cutoffHeight]; linarith)
  exact tendsto_natCast_atTop_atTop

/-- A uniform bound for the actual gradient density, derived from its
single transformed height germ rather than from its total integral. -/
theorem cutoffEnergyH_uniform (Y : ℝ) (hY : 1 < Y) (z : UpperHalfPlane) :
    cutoffEnergyH Y z ≤ cutoffEnergyConstant := by
  rcases cutoffEnergyH_zero_or_height Y hY z with hz | ⟨q, hq⟩
  · rw [hz]
    exact cutoffEnergyConstant_nonneg
  · rw [hq]
    let w := parabolicRepresentative 1 q • z
    obtain ⟨k, hk, _⟩ := unique_translate_mem_strip w
    have hb := cutoff_vertical_energy_pointwise (w := 1)
      (lt_trans (by norm_num) hY) (translate k w) hk
    simp only [translate_im] at hb
    exact hb.trans (by
      by_cases ht : translate k w ∈ highWidthStrip 1 Y
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht]
        exact cutoffEnergyConstant_nonneg)

theorem cutoffEnergyH_zero_above_height (Y : ℝ) (hY : 1 < Y)
    (z : UpperHalfPlane) (hz : max z.im (1 / z.im) < Y) :
    cutoffEnergyH Y z = 0 := by
  have htrace : parabolicTraceNN 1 (highSeed Y) z = 0 := by
    apply tsum_eq_zero.mpr
    intro q
    apply indicator_of_notMem
    change ¬ Y ≤ (parabolicRepresentative 1 q • z).im
    exact not_le.mpr ((integral_smul_im_le _ z).trans_lt hz)
  have hb := cutoffEnergyH_le_high_trace Y hY z
  rw [htrace, mul_zero] at hb
  have hz' : ENNReal.ofReal (cutoffEnergyH Y z) = 0 := le_antisymm hb bot_le
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz') (cutoffEnergyH_nonneg Y z)

theorem globalCutoff_one_above_height (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) (hz : max z.im (1 / z.im) < Y) :
    globalCutoff Y z = 1 := by
  have hh : highTrace 1 Y z = 0 := by
    apply tsum_eq_zero.mpr
    intro q
    exact highProfile_eq_zero Y hY _ (parabolicRepresentative 1 q • z).im_pos.le
      ((integral_smul_im_le _ z).trans_lt hz).le
  simp [globalCutoff, hh]

theorem quotient_cutoff_eventually_one (N : ℕ) (q : Gamma0OrbitSpace N) :
    ∀ᶠ n in atTop, quotientCutoff N (cutoffHeight n) q = 1 := by
  refine Quotient.inductionOn q (fun z => ?_)
  filter_upwards [cutoffHeight_tendsto.eventually
    (eventually_gt_atTop (max z.im (1 / z.im)))] with n hn
  exact globalCutoff_one_above_height _ (cutoffHeight_pos n) z hn

theorem quotient_energy_eventually_zero (N : ℕ) (q : Gamma0OrbitSpace N) :
    ∀ᶠ n in atTop,
      quotientCutoffEnergy N (cutoffHeight n) (cutoffHeight_pos n) q = 0 := by
  refine Quotient.inductionOn q (fun z => ?_)
  filter_upwards [cutoffHeight_tendsto.eventually
    (eventually_gt_atTop (max z.im (1 / z.im)))] with n hn
  exact cutoffEnergyH_zero_above_height _ (cutoffHeight_gt_one n) z hn

theorem quotient_energy_uniform (N : ℕ) (n : ℕ) (q : Gamma0OrbitSpace N) :
    quotientCutoffEnergy N (cutoffHeight n) (cutoffHeight_pos n) q ≤
      cutoffEnergyConstant := by
  refine Quotient.inductionOn q (fun z => ?_)
  exact cutoffEnergyH_uniform _ (cutoffHeight_gt_one n) z

theorem quotient_energy_measurable (N : ℕ) (n : ℕ) :
    Measurable (quotientCutoffEnergy N (cutoffHeight n) (cutoffHeight_pos n)) :=
  (quotientModularEnergy_measurable _ (cutoffHeight_pos n)).comp
    (Gamma0ModularFiniteCoverMeasure20261025a.forgetLevel_measurable N)

/-- Genuine weighted cutoff error vanishing. This applies to density
`‖f(q)‖²` for an arbitrary quotient L2 vector, even an unbounded one. -/
theorem weighted_cutoff_error_tendsto (N : ℕ) (w : Gamma0OrbitSpace N → ℝ)
    (hw : Integrable w (carrierPushforward N))
    (hw0 : ∀ᵐ q ∂carrierPushforward N, 0 ≤ w q) :
    Tendsto (fun n => ∫ q,
      quotientCutoffEnergy N (cutoffHeight n) (cutoffHeight_pos n) q * w q
        ∂carrierPushforward N) atTop (𝓝 0) := by
  have hb : ∀ n, ∀ᵐ q ∂carrierPushforward N,
      ‖quotientCutoffEnergy N (cutoffHeight n) (cutoffHeight_pos n) q * w q‖ ≤
        cutoffEnergyConstant * w q := by
    intro n
    filter_upwards [hw0] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (quotientCutoffEnergy_nonneg N _ _ q) hq)]
    exact mul_le_mul_of_nonneg_right (quotient_energy_uniform N n q) hq
  have hl : ∀ᵐ q ∂carrierPushforward N,
      Tendsto (fun n =>
        quotientCutoffEnergy N (cutoffHeight n) (cutoffHeight_pos n) q * w q)
        atTop (𝓝 (0 : ℝ)) :=
    Eventually.of_forall (fun q =>
      tendsto_const_nhds.congr' ((quotient_energy_eventually_zero N q).mono
        (fun n hn => by simp [hn])))
  simpa using (tendsto_integral_of_dominated_convergence
    (fun q => cutoffEnergyConstant * w q)
    (fun n => (quotient_energy_measurable N n).aestronglyMeasurable.mul
      hw.aestronglyMeasurable) (hw.const_mul cutoffEnergyConstant) hb hl)

theorem weighted_cutoff_mass_tendsto (N : ℕ) (w : Gamma0OrbitSpace N → ℝ)
    (hw : Integrable w (carrierPushforward N))
    (hw0 : ∀ᵐ q ∂carrierPushforward N, 0 ≤ w q) :
    Tendsto (fun n => ∫ q, (quotientCutoff N (cutoffHeight n) q)^2 * w q
      ∂carrierPushforward N) atTop (𝓝 (∫ q, w q ∂carrierPushforward N)) := by
  apply tendsto_integral_of_dominated_convergence w
  · intro n
    exact ((quotientCutoff_measurable N _ (cutoffHeight_pos n)).pow_const 2)
      .aestronglyMeasurable.mul hw.aestronglyMeasurable
  · exact hw
  · intro n
    filter_upwards [hw0] with q hq
    have hb := quotientCutoff_bounds N _ (cutoffHeight_gt_one n).le q
    have hs : (quotientCutoff N (cutoffHeight n) q)^2 ≤ 1 := by
      nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hq)]
    simpa using mul_le_mul_of_nonneg_right hs hq
  · exact Eventually.of_forall (fun q =>
      tendsto_const_nhds.congr' ((quotient_cutoff_eventually_one N q).mono
        (fun n hn => by simp [hn])))

end
end ImbalancedChen.Part3.Gamma0WeightedCutoffDefectLimit20261026a
