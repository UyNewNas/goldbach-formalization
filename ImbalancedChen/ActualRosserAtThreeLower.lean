import ImbalancedChen.ActualRosserOddFiniteLayers
import ImbalancedChen.RosserOddLayerIdentity
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveAmplitudeLimit
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityProducer
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
# Sharp lower threshold for the actual upper Rosser density at residual three

The genuine continuous odd layers form a convergent series whose normalized
sum is `F(3) = 2 exp(γ) / 3`. A finite prefix is chosen first, then its actual
prime-box threshold. The constant term is counted once, and the zero-depth
layer vanishes. The result concerns the same raw coefficients at level
`N^(3*u)` and cutoff `N^u`; it does not assume a sharp upper bound or a limit
for the remaining discrete boundary layers.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The genuine continuous finite prefixes tend to the exact upper
linear-sieve factor at three. The source contract is a proved theorem. -/
theorem tendsto_one_add_rosserOddLayerIntegral_partialSum_at_three :
    Tendsto (fun m : ℕ => 1 + ∑ k ∈ Finset.range m, rosserOddLayerIntegral k 3)
      atTop (nhds (2 * Real.exp Real.eulerMascheroniConstant / 3)) := by
  have hfactor :
      1 + (∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) 3) =
        2 * Real.exp Real.eulerMascheroniConstant / 3 := by
    change suzukiContinuousUpperFactor 3 = _
    rw [SwitchingPrinciple.suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
        jr1965Section13HatLayers jr1965Section13HatSourceContract
        (by norm_num) (by norm_num)]
    norm_num [SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor]
  have hlim : Tendsto (fun m : ℕ => 1 + suzukiOddSourceUpperPartialSum m 3)
      atTop (nhds (2 * Real.exp Real.eulerMascheroniConstant / 3)) := by
    rw [← hfactor]
    exact tendsto_const_nhds.add
      (tendsto_suzukiOddSourceUpperPartialSum jr1965Section13HatSourceContract)
  simpa only [suzukiOddSourceUpperPartialSum,
    rosserOddLayerIntegral_at_three_eq_suzukiLayer] using hlim

/-- A sharp lower threshold for the actual coefficient density at `s = 3`.
The exponent and error are fixed before the threshold, target, and cap. -/
theorem exists_actualSmallRosserPlusDensity_at_three_sharp_lower_threshold
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        2 * Real.exp Real.eulerMascheroniConstant / 3 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hnear := tendsto_one_add_rosserOddLayerIntegral_partialSum_at_three.eventually
    (lt_mem_nhds (show 2 * Real.exp Real.eulerMascheroniConstant / 3 - eta / 2 <
        2 * Real.exp Real.eulerMascheroniConstant / 3 by linarith))
  obtain ⟨m, hm⟩ := hnear.exists
  let K := (Finset.range m).erase 0
  have hK : ∀ k ∈ K, 1 ≤ k := by
    intro k hk
    have hk0 := (Finset.mem_erase.mp hk).1
    omega
  have hsum : (∑ k ∈ K, rosserOddLayerIntegral k 3) =
      ∑ k ∈ Finset.range m, rosserOddLayerIntegral k 3 :=
    Finset.sum_erase _ rosserOddLayerIntegral_zero_at_three
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddFiniteLayers_at_three_lower_threshold
      K hK u hu (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  rw [hsum] at h
  linarith

/-- The same actual lower threshold stated using the canonical
Jurkat--Richert factor, for subsequent sieve normalization. -/
theorem exists_actualSmallRosserPlusDensity_at_three_factor_lower_threshold
    (u : ℝ) (hu : 0 < u) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor 3 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (3 * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  simpa only [SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor,
    show (3 : ℝ) ≤ 3 by norm_num, if_true] using
    exists_actualSmallRosserPlusDensity_at_three_sharp_lower_threshold u hu eta heta

/-- Original level `R = N`, with the complete cutoff `N^(1/3)`. -/
theorem exists_actualSmallRosserPlusDensity_oneThird_sharp_lower_threshold
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (cap : ℝ) →
        2 * Real.exp Real.eulerMascheroniConstant / 3 - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (1 / 3 : ℝ)) (N : ℝ) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  simpa only [show (3 * (1 / 3 : ℝ)) = 1 by norm_num, Real.rpow_one] using
    exists_actualSmallRosserPlusDensity_at_three_sharp_lower_threshold
      (1 / 3) (by norm_num) eta heta

end

end ImbalancedChen
