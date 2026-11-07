import ImbalancedChen.Part3GammaActualDefectQuotientCaccioppoli
import ImbalancedChen.Part3Gamma0WeightedCutoffDefectLimit
import ImbalancedChen.Part3Gamma0ActualMinimalAdjointDefect

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual native negative-one adjoint defect vanishes. Its quotient
cutoff mass is bounded by the ORIGINAL weighted cutoff derivative error;
the proved arbitrary-L2 dominated convergence kills that error and
recovers the full original mass. This identifies the actual minimal
closure with the actual Friedrichs operator and proves native
self-adjointness of that minimal closure. No spectral decomposition,
gap, cusp completeness, or arithmetic theorem is inferred.
-/

namespace ImbalancedChen.Part3.GammaActualMinimalDefectVanishes20261026b
noncomputable section
open Set Filter MeasureTheory
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0ActualMinimalAdjointDefect20261025a Gamma0ActualFriedrichsOperator20261025a
open GammaActualQuotientCutoffMultiplier20261026b GammaActualDefectSupportedFormTesting20261026b
open GammaActualDefectQuotientCaccioppoli20261026b Gamma0WeightedCutoffDefectLimit20261026a
open GammaCompactSeedH1EnergyTransfer20261026b ActualModularSmoothCutoffL2Tail20261025a

theorem actual_quotient_cutoff_norm_sq_mass (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    ‖actualQuotientCutoffMultiplier N Y hY f‖^2 =
      ∫ q, (quotientCutoff N Y q)^2 * ‖f q‖^2 ∂carrierPushforward N := by
  rw [← scalar_L2_integral_sq (carrierPushforward N)
    (actualQuotientCutoffMultiplier N Y hY f)]
  apply integral_congr_ae
  filter_upwards [actual_cutoff_product_literal_ae N Y hY f] with q hq
  rw [hq,norm_mul,mul_pow]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- No regularity, form-domain, weak-equation, spectral or cutoff-energy
premise is supplied: every analytic obligation was proved in this chain. -/
theorem actual_minimalShiftDefect_eq_zero (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) : f = 0 := by
  have hw : Integrable (fun q : Gamma0OrbitSpace N => ‖f q‖^2) (carrierPushforward N) :=
    (Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hw0 : ∀ᵐ q ∂carrierPushforward N, 0 ≤ ‖f q‖^2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hE := weighted_cutoff_error_tendsto N (fun q => ‖f q‖^2) hw hw0
  have hmass := weighted_cutoff_mass_tendsto N (fun q => ‖f q‖^2) hw hw0
  have hfull : (∫ q, ‖f q‖^2 ∂carrierPushforward N) = ‖f‖^2 :=
    scalar_L2_integral_sq (carrierPushforward N) f
  have hM : Tendsto (fun n =>
      ‖actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) f‖^2)
      atTop (𝓝 (‖f‖^2)) := by
    simp_rw [actual_quotient_cutoff_norm_sq_mass]
    rw [← hfull]
    exact hmass
  have hM0 : Tendsto (fun n =>
      ‖actualQuotientCutoffMultiplier N (cutoffHeight n) (cutoffHeight_gt_one n) f‖^2)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun n => sq_nonneg _)
      (fun n => actual_defect_cutoff_norm_sq_le_error N f hf (cutoffHeight n) (cutoffHeight_gt_one n))
    exact hE
  have hsq : ‖f‖^2 = 0 := tendsto_nhds_unique hM hM0
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

theorem actual_minimalShiftDefect_eq_bot (N : ℕ) [NeZero N] : minimalShiftDefect N = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  exact actual_minimalShiftDefect_eq_zero N f hf

theorem actual_minimal_shift_range_eq_top (N : ℕ) [NeZero N] : minimalShiftRange N = ⊤ :=
  (minimalShiftRange_eq_top_iff_defect_eq_bot N).mpr (actual_minimalShiftDefect_eq_bot N)

/-- Equality of the ACTUAL native minimal closure with its ACTUAL
Friedrichs extension, through the previously proved exact defect criterion. -/
theorem actual_minimal_closure_eq_friedrichs (N : ℕ) [NeZero N] :
    actualClosedGammaMaass N = actualGammaFriedrichs N :=
  (actualMinimal_eq_friedrichs_iff_defect_eq_bot N).mpr (actual_minimalShiftDefect_eq_bot N)

/-- Native self-adjointness of the closure of the original smooth
Gamma0 quotient core: the concrete essential-self-adjointness endpoint. -/
theorem actual_minimal_closure_isSelfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (actualClosedGammaMaass N) := by
  rw [actual_minimal_closure_eq_friedrichs N]
  exact actualGammaFriedrichs_isSelfAdjoint N

end
end ImbalancedChen.Part3.GammaActualMinimalDefectVanishes20261026b
