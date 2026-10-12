import ImbalancedChen.RosserEvenLayerIntegral
import ImbalancedChen.RosserGlobalSourceIdentity

/-!
# Exact identification of every even Rosser layer

The largest-coordinate decomposition of the genuine even-region integral is
transported by the proved reciprocal change of variables. The predecessor
source identity is used on its full positive domain. Finite support then
identifies the improper odd-layer tail with Suzuki's even recursion for every
`s >= 2`, including its endpoints and levels above a layer's support.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Interval
open MeasureTheory Set
open MathlibNt.SieveTheory.LinearSieve
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

/-- The full even recursion as an improper tail of the preceding odd layer.
The lower parity threshold is two; no upper residual bound is imposed. -/
theorem suzukiLayer_even_eq_inv_mul_odd_tail (k : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    suzukiLayer 1 2 (2 * (k + 1)) s =
      s⁻¹ * ∫ v in Ioi s, suzukiLayer 1 2 (2 * k + 1) (v - 1) := by
  let B : ℝ := 2 + (2 * k + 2 : ℕ)
  have hzero (v : ℝ) (hv : B ≤ v) :
      suzukiLayer 1 2 (2 * k + 1) (v - 1) = 0 := by
    apply suzukiLayer_eq_zero_of_le
    dsimp [B] at hv
    push_cast at hv ⊢
    linarith
  by_cases hsB : s ≤ B
  · have htail : (∫ v in Ioi s, suzukiLayer 1 2 (2 * k + 1) (v - 1)) =
        ∫ v in Ioo s B, suzukiLayer 1 2 (2 * k + 1) (v - 1) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun _ hv => hv.1)
      intro v hv
      apply hzero
      exact le_of_not_gt (fun hvB => hv.2 ⟨hv.1, hvB⟩)
    have heps : sourceEpsilon (2 * k + 2) = 0 := by
      unfold sourceEpsilon
      omega
    have hlower : recursionLower 2 s (2 * k + 2) = s := by
      unfold recursionLower
      rw [heps]
      norm_num only [Nat.cast_zero, add_zero]
      rw [max_eq_left hs]
      exact min_eq_left hsB
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, suzukiLayer_succ_succ,
      hlower, htail]
    simp only [Real.rpow_one, dPowDensity, sub_self, Real.rpow_zero, mul_one]
    rw [(show (2 : ℝ) + ((2 * k : ℕ) + 2) = B by simp [B])]
    rw [intervalIntegral.integral_of_le hsB, integral_Ioc_eq_integral_Ioo]
  · have hBs : B ≤ s := le_of_not_ge hsB
    have htail : (∫ v in Ioi s, suzukiLayer 1 2 (2 * k + 1) (v - 1)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact hzero v (hBs.trans hv.le)
    rw [suzukiLayer_eq_zero_of_le 1 2 (2 * (k + 1)) (by
      simpa only [show 2 * (k + 1) = 2 * k + 2 by omega] using hBs), htail, mul_zero]

/-- The actual even-dimensional boundary integral is the genuine even
Suzuki layer for all legal lower-parity residuals, including `s=2`. -/
theorem rosserEvenLayerIntegral_eq_suzukiLayer (k : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    rosserEvenLayerIntegral k s = suzukiLayer 1 2 (2 * (k + 1)) s := by
  rw [rosserEvenLayerIntegral_eq_boundarySource k s (by linarith),
    integral_inv_mul_upperRosserBoundarySourceIntegral_change_variables k
      (by linarith : 0 < s) (by norm_num : (0 : ℝ) < 1), div_one,
    suzukiLayer_even_eq_inv_mul_odd_tail k s hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact upperRosserBoundarySourceIntegral_eq_suzukiLayer_of_pos k (v - 1) (by
    have hv' : s < v := hv
    linarith)

end

end ImbalancedChen
