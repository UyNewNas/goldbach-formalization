import ImbalancedChen.P4ASameRhoCompact
import ImbalancedChen.RosserContinuousSourceUniformity

/-!
The exact floor-grid baseline tends to the literal original ordinary root.
The original rho=19/96 and theta=299/500 are preserved. The upper factor
is the canonical Suzuki factor, with the exact root denominator rho.
No bound against currentK and no full22 hypothesis is used.

Draft import mapping: sibling P4ASameRhoCompact.lean.txt is to be staged as
ImbalancedChen/P4ASameRhoCompact.lean. No source is installed by this draft.
-/

namespace ImbalancedChen.P4ASameRhoCompact

noncomputable section
open Filter Topology
open MathlibNt.SieveTheory

def originalOrdinaryRoot : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / thirdPrefixRho) *
    suzukiContinuousUpperFactor (thirdPrefixTheta / thirdPrefixRho)

theorem initial_stop_floor_error {e : ℝ} (he0 : 0 < e) (he : e ≤ 1 / 384) (m : ℕ) :
    0 ≤ thirdPrefixRho - 4 * e - actualExtendedThirdInitialStopExponent e m ∧
      thirdPrefixRho - 4 * e - actualExtendedThirdInitialStopExponent e m <
        actualExtendedThirdDyadicStep m := by
  have hb := actualExtendedThirdInitialStopExponent_bounds he0 he m
  exact ⟨sub_nonneg.mpr hb.2.1, by linarith [hb.2.2.1]⟩

theorem initial_stop_abs_error {e : ℝ} (he0 : 0 < e) (he : e ≤ 1 / 384) (m : ℕ) :
    |actualExtendedThirdInitialStopExponent e m - thirdPrefixRho| ≤
      4 * e + actualExtendedThirdDyadicStep m := by
  have hb := actualExtendedThirdInitialStopExponent_bounds he0 he m
  rw [abs_of_neg (sub_neg.mpr hb.2.2.2)]
  linarith [hb.2.2.1]

/-- Joint buffer and mesh convergence controls the actual floor stop.
No monotonicity or prescribed relationship between the two nets is assumed. -/
theorem tendsto_initial_stop {α : Type*} {l : Filter α}
    (e : α → ℝ) (m : α → ℕ)
    (he : Tendsto e l (𝓝 0))
    (hmesh : Tendsto (fun a => actualExtendedThirdDyadicStep (m a)) l (𝓝 0))
    (hlegal : ∀ᶠ a in l, 0 < e a ∧ e a ≤ 1 / 384) :
    Tendsto (fun a => actualExtendedThirdInitialStopExponent (e a) (m a))
      l (𝓝 thirdPrefixRho) := by
  have hbudget : Tendsto (fun a => 4 * e a + actualExtendedThirdDyadicStep (m a))
      l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (he.const_mul 4).add hmesh
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  filter_upwards [hlegal, hbudget.eventually (gt_mem_nhds heta)] with a ha hsmall
  simpa only [Real.dist_eq] using
    (initial_stop_abs_error ha.1 ha.2 (m a)).trans_lt hsmall

/-- Continuity uses the actual global upper factor at theta/rho>1. -/
theorem tendsto_baselineLimit_original_root {α : Type*} {l : Filter α}
    (e : α → ℝ) (m : α → ℕ)
    (he : Tendsto e l (𝓝 0))
    (hmesh : Tendsto (fun a => actualExtendedThirdDyadicStep (m a)) l (𝓝 0))
    (hlegal : ∀ᶠ a in l, 0 < e a ∧ e a ≤ 1 / 384) :
    Tendsto (fun a => baselineLimit (e a) (m a)) l (𝓝 originalOrdinaryRoot) := by
  have hu := tendsto_initial_stop e m he hmesh hlegal
  have hrho : thirdPrefixRho ≠ 0 := by norm_num [thirdPrefixRho]
  have hresidual : 1 < thirdPrefixTheta / thirdPrefixRho := by
    norm_num [thirdPrefixTheta, thirdPrefixRho]
  have hlevel : Tendsto (fun a => thirdPrefixTheta - 2 * e a) l (𝓝 thirdPrefixTheta) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (he.const_mul 2)
  have hratio := hlevel.div hu hrho
  have hfactor : ContinuousAt suzukiContinuousUpperFactor (thirdPrefixTheta / thirdPrefixRho) :=
    continuousOn_suzukiContinuousUpperFactor.continuousAt (Ioi_mem_nhds hresidual)
  have hleading : Tendsto
      (fun a => 2 * Real.exp (-Real.eulerMascheroniConstant) /
        actualExtendedThirdInitialStopExponent (e a) (m a)) l
      (𝓝 (2 * Real.exp (-Real.eulerMascheroniConstant) / thirdPrefixRho)) :=
    tendsto_const_nhds.div hu hrho
  simpa only [baselineLimit, originalOrdinaryRoot] using
    hleading.mul (hfactor.tendsto.comp hratio)

def baselineBuffer (k : ℕ) : ℝ := actualExtendedThirdDyadicStep k / 8
def baselineMesh (k : ℕ) : ℕ := k + 4

theorem baselineMesh_step (k : ℕ) :
    actualExtendedThirdDyadicStep (baselineMesh k) = baselineBuffer k / 2 := by
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  dsimp [baselineMesh, baselineBuffer, actualExtendedThirdDyadicStep]
  rw [pow_add, show (2 : ℝ) ^ 4 = 16 by norm_num]
  field_simp [hp] <;> ring

theorem tendsto_baselineBuffer : Tendsto baselineBuffer atTop (𝓝 0) := by
  simpa only [baselineBuffer, zero_div] using tendsto_actualExtendedThirdDyadicStep.div_const 8

theorem eventually_baselineBuffer_legal :
    ∀ᶠ k : ℕ in atTop, 0 < baselineBuffer k ∧ baselineBuffer k ≤ 1 / 384 := by
  have hsmall := tendsto_baselineBuffer.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 384))
  filter_upwards [hsmall] with k hk
  exact ⟨div_pos (actualExtendedThirdDyadicStep_pos k) (by norm_num), hk.le⟩

theorem tendsto_baselineLimit_legal_sequence :
    Tendsto (fun k => baselineLimit (baselineBuffer k) (baselineMesh k)) atTop
      (𝓝 originalOrdinaryRoot) := by
  apply tendsto_baselineLimit_original_root baselineBuffer baselineMesh tendsto_baselineBuffer
  · simpa only [baselineMesh_step, zero_div] using tendsto_baselineBuffer.div_const 2
  · exact eventually_baselineBuffer_legal

/-- Both extra bounds are available for synchronizing other compact choices:
the buffer may be arbitrarily small and the actual mesh index arbitrarily large. -/
theorem exists_legal_baseline_le_original_root_add
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) (M : ℕ) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ e < eMax ∧ ∃ m : ℕ, M ≤ m ∧
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
      baselineLimit e m ≤ originalOrdinaryRoot + eta := by
  have hbound := tendsto_baselineLimit_legal_sequence.eventually
    (gt_mem_nhds (show originalOrdinaryRoot < originalOrdinaryRoot + eta by linarith))
  have hsmall := tendsto_baselineBuffer.eventually (gt_mem_nhds heMax)
  obtain ⟨k, hlegal, hboundK, hsmallK, hkM⟩ :=
    (eventually_baselineBuffer_legal.and (hbound.and (hsmall.and (eventually_ge_atTop M)))).exists
  refine ⟨baselineBuffer k, hlegal.1, hlegal.2, hsmallK, baselineMesh k, ?_, ?_, hboundK.le⟩
  · dsimp [baselineMesh]
    omega
  · exact (baselineMesh_step k).le

end
end ImbalancedChen.P4ASameRhoCompact
