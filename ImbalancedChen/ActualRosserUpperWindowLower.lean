import ImbalancedChen.ActualRosserAtThreeLower

/-!
# Actual upper Rosser density from below on the fixed residual window `[3,4]`

At each fixed residual in this window, the genuine continuous odd-layer
series sums to the Jurkat--Richert upper factor. Its zero-depth layer is
zero. A positive finite prefix is selected before applying the single-base
actual boundary lower bound. The resulting target threshold is uniform in
every cap covering the original power cutoff, with no discrete-tail limit
assumed. The residual and the power exponent remain fixed parameters.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The actual zero-depth region contributes nothing throughout the window. -/
theorem rosserOddLayerIntegral_zero_upperWindow (s : ℝ) (hs3 : 3 ≤ s) (hs4 : s ≤ 4) :
    rosserOddLayerIntegral 0 s = 0 := by
  rw [rosserOddLayerIntegral_eq_suzukiLayer 0 s (by linarith) hs4]
  simpa only [Nat.mul_zero, Nat.zero_add] using
    suzukiLayer_one_one_two_eq_zero_of_three_le hs3

/-- The genuine odd-region partial sums converge to the standard upper
sieve factor at each fixed residual in `[3,4]`. -/
theorem tendsto_one_add_rosserOddLayerIntegral_partialSum_upperWindow
    (s : ℝ) (hs3 : 3 ≤ s) (hs4 : s ≤ 4) :
    Tendsto (fun m : ℕ => 1 + ∑ k ∈ Finset.range m, rosserOddLayerIntegral k s)
      atTop (nhds (SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor s)) := by
  have hslo : 3 / 2 ≤ s := by linarith
  have hfactor :
      1 + (∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) s) =
        SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor s := by
    change suzukiContinuousUpperFactor s = _
    exact SwitchingPrinciple.suzukiContinuousUpperFactor_eq_jurkatRichertUpperLinearSieveFactor_of_sourceContract
      jr1965Section13HatLayers jr1965Section13HatSourceContract hslo hs4
  have hsum :=
    (summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract (show 1 < s by linarith)).hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun m : ℕ => 1 + ∑ k ∈ Finset.range m,
      suzukiLayer 1 2 (2 * k + 1) s) atTop
      (nhds (SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor s)) := by
    rw [← hfactor]
    exact tendsto_const_nhds.add hsum
  simpa only [rosserOddLayerIntegral_eq_suzukiLayer _ s hslo hs4] using hlim

/-- A sharp lower threshold for the same actual upper coefficient density.
The fixed exponent, residual, and error precede the threshold; the later
target and every complete enumeration cap share that threshold. -/
theorem exists_actualSmallRosserPlusDensity_upperWindow_lower_threshold
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs3 : 3 ≤ s) (hs4 : s ≤ 4)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
        SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor s - eta ≤
          actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ u) := by
  have hnear := (tendsto_one_add_rosserOddLayerIntegral_partialSum_upperWindow s hs3 hs4).eventually
    (lt_mem_nhds (show SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor s - eta / 2 <
        SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor s by linarith))
  obtain ⟨m, hm⟩ := hnear.exists
  let K := (Finset.range m).erase 0
  have hK : ∀ k ∈ K, 1 ≤ k := by
    intro k hk
    have hk0 := (Finset.mem_erase.mp hk).1
    omega
  have hcut : ∀ k ∈ K, s / 3 ^ (k + 1) < 1 := by
    intro k hk
    have hpow : (3 : ℝ) ^ 2 ≤ 3 ^ (k + 1) :=
      pow_le_pow_right₀ (by norm_num) (by have := hK k hk; omega)
    apply (div_lt_one (by positivity)).mpr
    norm_num at hpow
    linarith
  have hsum : (∑ k ∈ K, rosserOddLayerIntegral k s) =
      ∑ k ∈ Finset.range m, rosserOddLayerIntegral k s :=
    Finset.sum_erase _ (rosserOddLayerIntegral_zero_upperWindow s hs3 hs4)
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_oddFiniteLayers_lower_threshold
      K s (by linarith) hcut u hu (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven cap hcap
  have h := hbound N hN hEven cap hcap
  rw [hsum] at h
  linarith

end

end ImbalancedChen
