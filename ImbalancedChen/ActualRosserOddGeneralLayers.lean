import ImbalancedChen.ActualRosserOddFiniteLayers
import ImbalancedChen.RosserGlobalSourceIdentity
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
# Genuine odd layers at every fixed residual greater than one

Collapsed support regions have zero integral, so finite-layer selection needs
no artificial cutoff restriction. The concrete source contract supplies the
summable series of these actual integrals. A finite prefix is selected before
the target threshold, yielding the lower bound for the actual upper density.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem rosserOddLayerIntegral_eq_zero_of_cutoff_ge_one
    (k : ℕ) (s : ℝ) (hs : 0 < s) (hcut : 1 ≤ s / 3 ^ (k + 1)) :
    rosserOddLayerIntegral k s = 0 := by
  have hempty : rosserOddLogRegion k s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hb := rosserOddLogRegion_bounds hs hx 0
    linarith
  simp only [rosserOddLayerIntegral, hempty, MeasureTheory.setIntegral_empty]

/-- All finite rank sets, including collapsed regions, contribute to one
actual boundary expansion. The base term is counted exactly once. -/
theorem exists_actualSmallRosserPlusDensity_oddFiniteLayers_general_lower_threshold
    (K : Finset ℕ) (s : ℝ) (hs : 1 ≤ s)
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        1 + (∑ k ∈ K, rosserOddLayerIntegral k s) - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  let K' := K.filter (fun k => s / 3 ^ (k + 1) < 1)
  have hcut (k : ℕ) (hk : k ∈ K') : s / 3 ^ (k + 1) < 1 :=
    (Finset.mem_filter.mp hk).2
  have hsum : (∑ k ∈ K', rosserOddLayerIntegral k s) =
      ∑ k ∈ K, rosserOddLayerIntegral k s := by
    dsimp [K']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs with hk
    · rfl
    · exact (rosserOddLayerIntegral_eq_zero_of_cutoff_ge_one k s
        (zero_lt_one.trans_le hs) (le_of_not_gt hk)).symm
  simpa only [hsum] using
    exists_actualSmallRosserPlusDensity_oddFiniteLayers_lower_threshold
      K' s hs hcut u hu eta heta

/-- Summability is proved for the genuine geometric layers using the
fixed concrete source, with no summability premise on the caller. -/
theorem summable_rosserOddLayerIntegral (s : ℝ) (hs : 1 < s) :
    Summable (fun k : ℕ => rosserOddLayerIntegral k s) := by
  simpa only [rosserOddLayerIntegral_eq_suzukiLayer_of_pos _ s
    (zero_lt_one.trans hs)] using
    summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract hs

theorem tsum_rosserOddLayerIntegral_eq_upperFactor_sub_one
    (s : ℝ) (hs : 1 < s) :
    (∑' k : ℕ, rosserOddLayerIntegral k s) = suzukiContinuousUpperFactor s - 1 := by
  change _ = (1 + ∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) s) - 1
  rw [add_sub_cancel_left]
  exact tsum_congr (fun k => rosserOddLayerIntegral_eq_suzukiLayer_of_pos k s
    (zero_lt_one.trans hs))

/-- The limit uses the canonical source factor on its full domain, without
extending an initial-interval closed formula beyond its proved range. -/
theorem tendsto_one_add_rosserOddLayerIntegral_partialSum
    (s : ℝ) (hs : 1 < s) :
    Tendsto (fun m : ℕ => 1 + ∑ k ∈ Finset.range m, rosserOddLayerIntegral k s)
      atTop (nhds (suzukiContinuousUpperFactor s)) := by
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).add
    (summable_rosserOddLayerIntegral s hs).hasSum.tendsto_sum_nat
  simpa only [tsum_rosserOddLayerIntegral_eq_upperFactor_sub_one s hs,
    show 1 + (suzukiContinuousUpperFactor s - 1) = suzukiContinuousUpperFactor s by ring]
    using hlim

/-- Fixed exponent and residual precede the threshold; all later even
targets and complete enumeration caps share it. -/
theorem exists_actualSmallRosserPlusDensity_general_lower_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 1 < s) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        suzukiContinuousUpperFactor s - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hnear := (tendsto_one_add_rosserOddLayerIntegral_partialSum s hs).eventually
    (lt_mem_nhds (show suzukiContinuousUpperFactor s - eta / 2 <
        suzukiContinuousUpperFactor s by linarith))
  obtain ⟨m, hm⟩ := hnear.exists
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddFiniteLayers_general_lower_threshold
      (Finset.range m) s hs.le u hu (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  linarith

end

end ImbalancedChen
