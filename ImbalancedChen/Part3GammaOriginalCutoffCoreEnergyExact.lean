import ImbalancedChen.Part3GammaSmoothCoreMultiplierEnergyLift

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual first-power cutoff is the multiplier needed for form-domain
approximation. This derives its exact core action from the proved actual
cutoff-square equality and genuine 0<=chi<=1 bounds. Its completed energy
lift and global carrier gradient therefore become exactly the original
ones above one uniform compact-seed threshold; no support invariance or
form-convergence premise is used.
-/

namespace ImbalancedChen.Part3.GammaOriginalCutoffCoreEnergyExact20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0CarrierGradientHilbertMap20261026b
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaCompactSeedCutoffPlateau20261026a GammaOriginalCoreCutoffEventualExact20261026b
open GammaSmoothCoreMultiplierEnergyLift20261026b Gamma0WeightedCutoffDefectLimit20261026a
open ActualModularSmoothCutoffL2Tail20261025a

private theorem real_multiplier_fixed_of_square_fixed (c : ℝ) (hc : 0 ≤ c) (a : ℂ)
    (h : (c : ℂ)^2 * a = a) : (c : ℂ)*a = a := by
  by_cases ha : a = 0
  · simp only [ha,mul_zero]
  · have hsq : (c : ℂ)^2 = 1 := mul_right_cancel₀ ha (by simpa only [one_mul] using h)
    have hreal : c^2 = (1 : ℝ)^2 := by exact_mod_cast hsq
    have hc1 : c = 1 := (sq_eq_sq₀ hc (by norm_num : (0 : ℝ) ≤ 1)).mp hreal
    simp only [hc1,Complex.ofReal_one,one_mul]

/-- The threshold was fixed from the compact original seed. The actual
quotient cutoff has its true nonnegative range, hence its square fixing
the original input forces its first power to fix that same input. -/
theorem exists_actualCutoffCoreEnergy_eventual_exact
    (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ Y : ℝ, ∀ hY : plateauThreshold a b ≤ Y,
        actualCutoffCoreEnergy N Y ((plateauThreshold_pos a b).trans_le hY) u = coreEmbedding N u := by
  obtain ⟨a,b,ha,hab,hfixed⟩ := exists_original_core_eventual_fixed N u
  refine ⟨a,b,ha,hab,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := by
    have hm := le_max_left (2 : ℝ) (max (b+1) (2/a))
    unfold plateauThreshold at hY
    linarith
  have hsquare := (hfixed Y hY).2.2
  rw [actualCutoff_square_quotientMultiplier N Y] at hsquare
  have hfirst : quotientMultiplier N
      (ActualModularCutoffMaassBudget20261025a.complexGlobalH Y)
      (actualCutoff_isGammaInvariant N Y) * (u : QuotientL2 N)
      =ᵐ[carrierPushforward N] (u : QuotientL2 N) := by
    rw [actualCutoff_quotientMultiplier N Y]
    filter_upwards [hsquare] with q hq
    exact real_multiplier_fixed_of_square_fixed (quotientCutoff N Y q)
      (quotientCutoff_bounds N Y hY1 q).1 (u q) hq
  apply physicalProjection_injective N
  rw [physicalProjection_core]
  apply Lp.ext
  exact (coreMultiplierEnergyLift_physical_ae N u _ (actualCutoff_isGammaInvariant N Y)
    (actualCutoff_cinfty Y ((plateauThreshold_pos a b).trans_le hY))).trans hfirst

theorem actualCutoffCoreEnergy_tendsto
    (N : ℕ) [NeZero N] (u : EnergyCore N) :
    Tendsto (fun n => actualCutoffCoreEnergy N (cutoffHeight n) (cutoffHeight_pos n) u)
      atTop (𝓝 (coreEmbedding N u)) := by
  obtain ⟨a,b,ha,hab,hexact⟩ := exists_actualCutoffCoreEnergy_eventual_exact N u
  have heventual : ∀ᶠ n in atTop,
      actualCutoffCoreEnergy N (cutoffHeight n) (cutoffHeight_pos n) u = coreEmbedding N u := by
    filter_upwards [cutoffHeight_tendsto.eventually (eventually_ge_atTop (plateauThreshold a b))]
      with n hn
    exact hexact (cutoffHeight n) hn
  exact tendsto_const_nhds.congr' heventual

/-- This is the genuine GLOBAL physical-carrier gradient in its native
L2 norm, obtained by continuity of the already constructed Hilbert map. -/
theorem actualCutoffCoreEnergy_carrier_gradient_tendsto
    (N : ℕ) [NeZero N] (u : EnergyCore N) :
    Tendsto (fun n => completedCarrierGradient N
        (actualCutoffCoreEnergy N (cutoffHeight n) (cutoffHeight_pos n) u))
      atTop (𝓝 (carrierCoreGradient N u)) := by
  simpa only [completedCarrierGradient_core] using
    ((completedCarrierGradient N).continuous.tendsto (coreEmbedding N u)).comp
      (actualCutoffCoreEnergy_tendsto N u)

end
end ImbalancedChen.Part3.GammaOriginalCutoffCoreEnergyExact20261026b
