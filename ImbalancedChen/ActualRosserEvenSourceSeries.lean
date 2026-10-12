import ImbalancedChen.RosserEvenLayerIdentity
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiContinuousLowerFactorSecondInterval
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
# The genuine even-region series and the continuous lower factor

Every summand is the actual even-region Lebesgue integral. Its source identity
and the proved JR source contract supply nonnegativity, summability, and the
real finite-prefix limit at every fixed `s >= 2`. No discrete-box estimate or
summability hypothesis is imposed on the caller.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem rosserEvenLayerIntegral_nonneg (k : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    0 ≤ rosserEvenLayerIntegral k s := by
  rw [rosserEvenLayerIntegral_eq_suzukiLayer k s hs]
  exact suzukiLayer_one_two_even_nonneg hs k

/-- Summability of the genuine integrals, supplied by the proved concrete
source contract rather than assumed as an analytic input. -/
theorem summable_rosserEvenLayerIntegral (s : ℝ) (hs : 2 ≤ s) :
    Summable (fun k : ℕ => rosserEvenLayerIntegral k s) := by
  simpa only [rosserEvenLayerIntegral_eq_suzukiLayer _ s hs] using
    summable_suzukiLayer_one_two_even_of_sourceContract jr1965Section13HatSourceContract hs

/-- The actual total continuous even-boundary loss is one minus the
canonical continuous lower factor. -/
theorem tsum_rosserEvenLayerIntegral_eq_one_sub_lowerFactor (s : ℝ) (hs : 2 ≤ s) :
    (∑' k : ℕ, rosserEvenLayerIntegral k s) = 1 - suzukiContinuousLowerFactor s := by
  simp only [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    suzukiProposition118SourceTMinus_eq, sub_sub_cancel]
  exact tsum_congr (fun k => rosserEvenLayerIntegral_eq_suzukiLayer k s hs)

/-- Real finite-prefix convergence of the actual even-region integrals. -/
theorem tendsto_rosserEvenLayerIntegral_partialSum (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, rosserEvenLayerIntegral k s)
      atTop (nhds (1 - suzukiContinuousLowerFactor s)) := by
  rw [← tsum_rosserEvenLayerIntegral_eq_one_sub_lowerFactor s hs]
  exact (summable_rosserEvenLayerIntegral s hs).hasSum.tendsto_sum_nat

/-- Subtracting the genuine finite losses from a single base term tends
to the continuous lower factor, for the later actual-density comparison. -/
theorem tendsto_one_sub_rosserEvenLayerIntegral_partialSum (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun m : ℕ => 1 - ∑ k ∈ Finset.range m, rosserEvenLayerIntegral k s)
      atTop (nhds (suzukiContinuousLowerFactor s)) := by
  simpa only [sub_sub_cancel] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_rosserEvenLayerIntegral_partialSum s hs)

end

end ImbalancedChen
