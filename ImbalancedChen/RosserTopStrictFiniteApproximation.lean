import ImbalancedChen.RosserTopStrictMeshes
import ImbalancedChen.ActualRosserOddGeneralLayers
import ImbalancedChen.ActualRosserEvenFiniteLayers
import ImbalancedChen.ActualRosserEvenSourceSeries

/-!
# Finite strict-margin boxes approximate the complete continuous factors

The source series chooses a finite prefix; collapsed regions are discarded
using their proved zero integrals. A common top-strict mesh then approximates
all retained ranks. All choices depend only on the fixed residual and error,
before any target integer or varying exponent is introduced.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory

theorem exists_rosserOddTopStrictFiniteApproximation
    (s : ℝ) (hs : 1 < s) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : Finset ℕ, ∃ n : ℕ,
      (∀ k ∈ K, s / 3 ^ (k + 1) < 1) ∧
      suzukiContinuousUpperFactor s - eta <
        1 + ∑ k ∈ K, rosserOddTopStrictMeshLowerSum k s n := by
  have hnear := (tendsto_one_add_rosserOddLayerIntegral_partialSum s hs).eventually
    (lt_mem_nhds (show suzukiContinuousUpperFactor s - eta / 2 <
      suzukiContinuousUpperFactor s by linarith))
  obtain ⟨m, hm⟩ := hnear.exists
  let K := (Finset.range m).filter (fun k => s / 3 ^ (k + 1) < 1)
  have hcut (k : ℕ) (hk : k ∈ K) : s / 3 ^ (k + 1) < 1 :=
    (Finset.mem_filter.mp hk).2
  have hsum : (∑ k ∈ K, rosserOddLayerIntegral k s) =
      ∑ k ∈ Finset.range m, rosserOddLayerIntegral k s := by
    dsimp [K]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs with hk
    · rfl
    · exact (rosserOddLayerIntegral_eq_zero_of_cutoff_ge_one k s
        (zero_lt_one.trans hs) (le_of_not_gt hk)).symm
  have hlim : Tendsto (fun n => ∑ k ∈ K, rosserOddTopStrictMeshLowerSum k s n) atTop
      (nhds (∑ k ∈ K, rosserOddLayerIntegral k s)) :=
    tendsto_finsetSum K (fun k hk =>
      tendsto_rosserOddTopStrictMeshLowerSum (zero_lt_one.trans hs) (hcut k hk))
  obtain ⟨n, hn⟩ := (hlim.eventually
    (lt_mem_nhds (show (∑ k ∈ K, rosserOddLayerIntegral k s) - eta / 2 <
      ∑ k ∈ K, rosserOddLayerIntegral k s by linarith))).exists
  refine ⟨K, n, hcut, ?_⟩
  rw [hsum] at hn
  linarith

theorem exists_rosserEvenTopStrictFiniteApproximation
    (s : ℝ) (hs : 2 ≤ s) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : Finset ℕ, ∃ n : ℕ,
      (∀ k ∈ K, (s - 1) / 3 ^ (k + 1) < 1) ∧
      1 - (∑ k ∈ K, rosserEvenTopStrictMeshLowerSum k s n) <
        suzukiContinuousLowerFactor s + eta := by
  have hs1 : 1 < s := by linarith
  have hnear := (tendsto_rosserEvenLayerIntegral_partialSum s hs).eventually
    (lt_mem_nhds (show 1 - suzukiContinuousLowerFactor s - eta / 2 <
      1 - suzukiContinuousLowerFactor s by linarith))
  obtain ⟨m, hm⟩ := hnear.exists
  let K := (Finset.range m).filter (fun k => (s - 1) / 3 ^ (k + 1) < 1)
  have hcut (k : ℕ) (hk : k ∈ K) : (s - 1) / 3 ^ (k + 1) < 1 :=
    (Finset.mem_filter.mp hk).2
  have hsum : (∑ k ∈ K, rosserEvenLayerIntegral k s) =
      ∑ k ∈ Finset.range m, rosserEvenLayerIntegral k s := by
    dsimp [K]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _hk
    split_ifs with hk
    · rfl
    · exact (rosserEvenLayerIntegral_eq_zero_of_cutoff_ge_one k s hs1
        (le_of_not_gt hk)).symm
  have hlim : Tendsto (fun n => ∑ k ∈ K, rosserEvenTopStrictMeshLowerSum k s n) atTop
      (nhds (∑ k ∈ K, rosserEvenLayerIntegral k s)) :=
    tendsto_finsetSum K (fun k hk =>
      tendsto_rosserEvenTopStrictMeshLowerSum hs1 (hcut k hk))
  obtain ⟨n, hn⟩ := (hlim.eventually
    (lt_mem_nhds (show (∑ k ∈ K, rosserEvenLayerIntegral k s) - eta / 2 <
      ∑ k ∈ K, rosserEvenLayerIntegral k s by linarith))).exists
  refine ⟨K, n, hcut, ?_⟩
  rw [hsum] at hn
  linarith

end

end ImbalancedChen
