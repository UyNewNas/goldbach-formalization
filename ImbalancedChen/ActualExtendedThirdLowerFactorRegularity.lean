import ImbalancedChen.ActualExtendedThirdOrderedIntegral
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Actual lower-factor regularity for the extended-third kernel

The even source layers are bounded by their summable actual values at two.
The M-test proves continuity on the closed domain, including its endpoint.
Composing with `max 2 s` gives continuity of the manuscript's zero extension.

The layer proof is the same proved argument as the private supplier in
`CurrentChenOrdinaryInitialMean`; that broad arithmetic module is not imported
here. The scalar bounds and continuity concern the genuine canonical factor,
not an abstract continuous replacement.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem continuousOn_actualExtendedThirdCanonicalLowerFactor :
    ContinuousOn suzukiContinuousLowerFactor (Set.Ici 2) := by
  have hbound (k : ℕ) (s : ℝ) (hs : s ∈ Set.Ici (2 : ℝ)) :
      ‖suzukiLayer 1 2 (2 * (k + 1)) s‖ ≤
        suzukiLayer 1 2 (2 * (k + 1)) 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (suzukiLayer_one_two_even_nonneg hs k)]
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * (k + 1))
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain])
      (by simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hs) hs
  have hcont (k : ℕ) :
      ContinuousOn (suzukiLayer 1 2 (2 * (k + 1))) (Set.Ici 2) := by
    apply (suzukiLayer_one_continuousOn_parityDomain (by norm_num) (2 * (k + 1))).mono
    intro s hs
    simpa [suzukiParityDomainOne, KappaOneModel.parityDomain] using hs
  exact continuousOn_const.sub (continuousOn_tsum hcont
    (summable_suzukiProposition118SourceTMinus_of_sourceContract
      jr1965Section13HatSourceContract (by norm_num : (2 : ℝ) ≤ 2)) hbound)

theorem continuousOn_thirdTailLowerFactor : ContinuousOn thirdTailLowerFactor (Set.Ici 2) :=
  continuousOn_actualExtendedThirdCanonicalLowerFactor.div_const _

theorem continuous_actualExtendedThirdLowerFactor : Continuous actualExtendedThirdLowerFactor := by
  exact continuousOn_thirdTailLowerFactor.comp_continuous
    (continuous_const.max continuous_id) (fun s => le_max_left 2 s)

theorem actualExtendedThirdLowerFactor_nonneg (s : ℝ) : 0 ≤ actualExtendedThirdLowerFactor s := by
  by_cases hs : s ≤ 2
  · exact (actualExtendedThirdLowerFactor_of_le_two hs).symm.le
  · have hm := monotone_actualExtendedThirdLowerFactor (le_of_not_ge hs)
    simpa only [actualExtendedThirdLowerFactor_of_le_two (s := 2) le_rfl] using hm

theorem actualExtendedThirdLowerFactor_le_normalization (s : ℝ) :
    actualExtendedThirdLowerFactor s ≤ 1 / (2 * Real.exp Real.eulerMascheroniConstant) := by
  have hs : 2 ≤ max (2 : ℝ) s := le_max_left 2 s
  have hminus : 0 ≤ suzukiProposition118SourceTMinus (max (2 : ℝ) s) :=
    tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg hs k)
  unfold actualExtendedThirdLowerFactor thirdTailLowerFactor suzukiContinuousLowerFactor
    suzukiContinuousLowerTail
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end

end ImbalancedChen
