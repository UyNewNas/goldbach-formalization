import ImbalancedChen.CurrentChenUpsilon6KernelBuffer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiContinuousLowerFactorSecondInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePTail
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource

/-!
# The same buffer limit for the actual normalized continuous lower factor

The pinned first-interval source identities and concrete JR source contract
identify the literal logarithmic kernel with its normalized sieve kernel.
This identity is used only on the corrected product domain, including s=2.
The arithmetic mask, arithmetic mean and causal improvement remain separate.
-/

namespace ImbalancedChen

noncomputable section

open scoped Topology
open MeasureTheory Filter Set
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

private theorem sixthCanonicalLowerFactor_firstInterval (s : ℝ)
    (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    suzukiContinuousLowerFactor s =
      2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract hs hs4,
    suzukiLowerSieveFactorFirstInterval_eq_log hs hs4,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract]

def currentChenUpsilon6NormalizedSieveKernel (x : Fin 2 → ℝ) : ℝ :=
  ((2 * Real.exp (-Real.eulerMascheroniConstant) / (417 / 5000 : ℝ)) *
    suzukiContinuousLowerFactor (currentChenUpsilon6OrdinaryProfile x)) *
      (1 / (x 0 * x 1))

theorem currentChenUpsilon6NormalizedSieveKernel_eq_ordinary
    {eta : ℝ} (heta : 0 ≤ eta) {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    currentChenUpsilon6NormalizedSieveKernel x = currentChenUpsilon6OrdinaryKernel x := by
  have hp := currentChenUpsilon6OrdinaryProfile_mem_firstInterval heta hx
  have hfactor :
      (2 * Real.exp (-Real.eulerMascheroniConstant) / (417 / 5000 : ℝ)) *
        suzukiContinuousLowerFactor (currentChenUpsilon6OrdinaryProfile x) =
      4 * Real.log (currentChenUpsilon6OrdinaryProfile x - 1) /
        (currentChenUpsilon6OrdinaryProfile x * (417 / 5000)) := by
    rw [sixthCanonicalLowerFactor_firstInterval _ hp.1 hp.2, Real.exp_neg]
    field_simp
    ring
  exact congrArg (fun t : ℝ => t * (1 / (x 0 * x 1))) hfactor

private theorem measurableSet_sixthDomain (eta : ℝ) :
    MeasurableSet (currentChenUpsilon6LogDomain eta) :=
  measurableSet_currentChenUpsilon6LogRectangle.inter
    ((isClosed_le ((continuous_apply 0).add (continuous_apply 1))
      continuous_const).measurableSet)

theorem integral_currentChenUpsilon6NormalizedSieveKernel_eq_ordinary
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6NormalizedSieveKernel x) =
      ∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x := by
  apply setIntegral_congr_fun (measurableSet_sixthDomain eta)
  intro x hx
  exact currentChenUpsilon6NormalizedSieveKernel_eq_ordinary heta hx

theorem tendsto_integral_currentChenUpsilon6NormalizedSieveKernel_buffer :
    Tendsto (fun eta : ℝ => ∫ x in currentChenUpsilon6LogDomain eta,
      currentChenUpsilon6NormalizedSieveKernel x) (𝓝[>] 0)
      (𝓝 (∫ x in currentChenUpsilon6LogDomain 0,
        currentChenUpsilon6NormalizedSieveKernel x)) := by
  rw [integral_currentChenUpsilon6NormalizedSieveKernel_eq_ordinary (le_refl 0)]
  apply (tendsto_integral_currentChenUpsilon6OrdinaryKernel_buffer.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact (integral_currentChenUpsilon6NormalizedSieveKernel_eq_ordinary heta.le).symm

end

end ImbalancedChen
