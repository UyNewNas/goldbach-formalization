import ImbalancedChen.Part3HeatDenseAnalyticCore
import ImbalancedChen.Part3Gamma0ActualHeatGenerator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

ALL powers smoothing and a dense analytic graph core on the ACTUAL Gamma0
quotient Hilbert space. The real physical completed-energy R supplies every
primitive; the native powers are genuine iterated graphs of the actual
Friedrichs operator. Positive-time actual heat vectors lie in all domains,
with exact continuous spectral multipliers lambda^n exp(-s lambda) and
internally proved n!s^-n norm bounds. No smoothing, analytic-vector or
density premise is assumed. The analytic graph closure equals the actual
native operator graph, not merely the ambient Hilbert space.
-/

namespace ImbalancedChen.Part3.Gamma0ActualHeatAllPowersAnalyticCore20261025a
noncomputable section
open Set
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualHeatGenerator20261025a
open ImbalancedChen.Part3.GenericHeatAllPowersCalculus20261025a
open ImbalancedChen.Part3.NativeOperatorPowersHeatSmoothing20261025a
open ImbalancedChen.Part3.HeatDenseAnalyticCore20261025a

def actualGammaHeatPowerMultiplier (N : ℕ) [NeZero N] (s : ℝ) (n : ℕ) :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  heatPowerOperator (actualGammaHeatData N) s n

theorem actualGammaHeat_mem_all_nativePower_domains (N : ℕ) [NeZero N]
    {s : ℝ} (hs : 0 < s) (f : QuotientL2 N) (n : ℕ) :
    actualGammaHeat N s f ∈ (nativePower (actualGammaFriedrichs N) n).domain :=
  heat_mem_all_nativePower_domains (actualGammaHeatData N) hs f n

def actualGammaHeatPowerPoint (N : ℕ) [NeZero N] (s : ℝ) (hs : 0 < s)
    (n : ℕ) (f : QuotientL2 N) : (nativePower (actualGammaFriedrichs N) n).domain :=
  ⟨actualGammaHeat N s f, actualGammaHeat_mem_all_nativePower_domains N hs f n⟩

/-- Exact native actual A^n output, with the genuine spectral multiplier.
The output is not an asserted domain or smoothing supplier. -/
theorem actualGammaNativePower_heat_apply (N : ℕ) [NeZero N]
    (s : ℝ) (hs : 0 < s) (n : ℕ) (f : QuotientL2 N) :
    nativePower (actualGammaFriedrichs N) n (actualGammaHeatPowerPoint N s hs n f) =
      actualGammaHeatPowerMultiplier N s n f :=
  nativePower_heat_apply (actualGammaHeatData N) s hs n f

theorem actualGammaHeatPowerMultiplier_norm_le (N : ℕ) [NeZero N]
    {s : ℝ} (hs : 0 < s) (n : ℕ) (f : QuotientL2 N) :
    ‖actualGammaHeatPowerMultiplier N s n f‖ ≤ ((n.factorial : ℝ) / s ^ n) * ‖f‖ :=
  heatPowerOperator_norm_le (actualGammaHeatData N) hs n f

theorem actualGammaNativePower_heat_norm_le (N : ℕ) [NeZero N]
    (s : ℝ) (hs : 0 < s) (n : ℕ) (f : QuotientL2 N) :
    ‖nativePower (actualGammaFriedrichs N) n (actualGammaHeatPowerPoint N s hs n f)‖ ≤
      ((n.factorial : ℝ) / s ^ n) * ‖f‖ := by
  rw [actualGammaNativePower_heat_apply]
  exact actualGammaHeatPowerMultiplier_norm_le N hs n f

theorem actualGammaHeat_factorial_series_summable (N : ℕ) [NeZero N]
    {s : ℝ} (hs : 0 < s) (f : QuotientL2 N) :
    Summable (fun n : ℕ =>
      (s / 2) ^ n * ‖actualGammaHeatPowerMultiplier N s n f‖ / (n.factorial : ℝ)) :=
  heat_factorial_series_summable (actualGammaHeatData N) hs f

theorem actualGammaHeat_isAnalyticVector (N : ℕ) [NeZero N]
    {s : ℝ} (hs : 0 < s) (f : QuotientL2 N) :
    IsAnalyticVector (actualGammaFriedrichs N) (actualGammaHeat N s f) :=
  heat_isAnalyticVector (actualGammaHeatData N) hs f

theorem actualGamma_dense_all_nativePower_domains (N : ℕ) [NeZero N] (n : ℕ) :
    Dense ((nativePower (actualGammaFriedrichs N) n).domain : Set (QuotientL2 N)) :=
  dense_nativePower_domain (actualGammaHeatData N) n

theorem actualGamma_dense_analyticVectors (N : ℕ) [NeZero N] :
    Dense {u : QuotientL2 N | IsAnalyticVector (actualGammaFriedrichs N) u} :=
  dense_analyticVectors (actualGammaHeatData N)

/-- Genuine core equality for the actual native Gamma0 operator graph. -/
theorem actualGamma_closure_analyticGraph_eq (N : ℕ) [NeZero N] :
    closure (analyticGraph (actualGammaFriedrichs N)) =
      ((actualGammaFriedrichs N).graph : Set (QuotientL2 N × QuotientL2 N)) :=
  closure_analyticGraph_eq_nativeGraph (actualGammaHeatData N)

end
end ImbalancedChen.Part3.Gamma0ActualHeatAllPowersAnalyticCore20261025a
