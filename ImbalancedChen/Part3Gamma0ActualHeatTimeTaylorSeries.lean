import ImbalancedChen.Part3HeatOperatorNormTaylorSeries
import ImbalancedChen.Part3Gamma0ActualHeatAllPowersAnalyticCore

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The ACTUAL Gamma0 physical heat family has the genuine operator-norm
time Taylor series. Every vector coefficient is additionally identified
with its true native actual Friedrichs power on the actual smoothed
domain vector. No Taylor or derivative hypothesis is supplied.
-/

namespace ImbalancedChen.Part3.Gamma0ActualHeatTimeTaylorSeries20261025a
noncomputable section
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualHeatGenerator20261025a
open ImbalancedChen.Part3.Gamma0ActualHeatAllPowersAnalyticCore20261025a
open ImbalancedChen.Part3.NativeOperatorPowersHeatSmoothing20261025a
open ImbalancedChen.Part3.HeatOperatorNormTaylorSeries20261025a

/-- Convergence here is in the actual quotient-Hilbert operator norm. -/
theorem actualGammaHeat_hasSum_operator_timeTaylor (N : ℕ) [NeZero N]
    {s h : ℝ} (hs : 0 < s) (hh : |h| < s / 2) :
    HasSum (fun n : ℕ => ((-h) ^ n / (n.factorial : ℝ)) • actualGammaHeatPowerMultiplier N s n)
      (actualGammaHeat N (s + h)) :=
  hasSum_heatOperator_timeTaylor (actualGammaHeatData N) hs hh

/-- Exact actual native-power Taylor coefficients on EVERY physical
forcing; all coefficient domain memberships were genuinely proved. -/
theorem actualGammaHeat_hasSum_nativePower_timeTaylor (N : ℕ) [NeZero N]
    {s h : ℝ} (hs : 0 < s) (hh : |h| < s / 2) (f : QuotientL2 N) :
    HasSum (fun n : ℕ => ((-h) ^ n / (n.factorial : ℝ)) •
      nativePower (actualGammaFriedrichs N) n (actualGammaHeatPowerPoint N s hs n f))
      (actualGammaHeat N (s + h) f) := by
  have heval := (actualGammaHeat_hasSum_operator_timeTaylor N hs hh).mapL
    (ContinuousLinearMap.apply ℂ (QuotientL2 N) f)
  simpa only [ContinuousLinearMap.smul_apply, actualGammaNativePower_heat_apply] using heval

end
end ImbalancedChen.Part3.Gamma0ActualHeatTimeTaylorSeries20261025a
