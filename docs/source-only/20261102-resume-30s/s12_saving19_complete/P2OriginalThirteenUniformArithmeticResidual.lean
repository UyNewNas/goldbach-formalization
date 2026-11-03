import ImbalancedChen.P4AOriginalThirteenLocalizedContinuation
import ImbalancedChen.OriginalAscendingNineteenArithmeticResidual

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing production OriginalAscendingNineteenArithmeticResidual already
supplies the uniform actual ordinary residual theorem.  This file directly
instantiates it with the actual original13 bank and the same current sixth
parent after14, discharging the original source and parent upper premises.
No duplicate compact residual proof, target mean or licence field is added.
The integrated ordinary/positive-w saving remains a separate obligation.
-/
namespace ImbalancedChen.P2OriginalThirteenUniformArithmeticResidual
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P2OriginalThirdMinorantLogDictionarySourceOnly
open OriginalAscendingThirteenCellOwnership
open P5OriginalCommonRefinedConstructor
open P4AOriginalArchiveFourteenPositivePresieve
open P4AOriginalFourteenThirteenCurrentSource
open P4AOriginalLive171819PrimeBank P4AOriginalLive171819CommonParent
/-- No desired parent licence or historical bound is supplied here.
The actual original bank/frontier and common constructor supply both. -/
theorem original_selected_parent_dictionary
    (i : Fin 13) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (omega : ℝ)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.ascending19 i) (data e q omega).e (data e q omega).chi
      (data e q omega).m (data e q omega).omega N cap w z (fourteenPolicy e q omega (N : ℝ))) :
    StrictRows i (point8 (N : ℝ) s.selectedPrefix) ∧
      history7 (point8 (N : ℝ) s.selectedPrefix) <
        lambda6 (data e q omega) (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∧
      lambda6 (data e q omega) (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ≤
        comparisonCap (point8 (N : ℝ) s.selectedPrefix) := by
  have hs6 := hs
  rw [original_thirteen_selected_list_preserved] at hs6
  have hs8 : s ∈ selected (.ascending19 i) (data e q omega).e (data e q omega).chi
      (data e q omega).m (data e q omega).omega N cap w z
      (policy8 (data e q omega) (N : ℝ)) := by
    unfold selected at hs6 ⊢
    rwa [P5OriginalCommonRefinedAncestry.policy8_frontier_eight_eq_six]
  have hd : 0 ≤ (data e q omega).e := he
  obtain ⟨hrows, _hstop, hhistory, hcap⟩ :=
    shared_frontier_live_guard (.ascending19 i) (data e q omega) hd N cap hN w z s hs8
  exact ⟨P4AOriginalLive171819Atlas.source19_guard i _ hrows, hhistory, hcap⟩

/-- Uniform arithmetic error for every original13 bank occurrence on the
actual after14 tree.  N0 precedes e,q,omega,cap,z and the selected state.
The raw inherited parent, its genuine H7 and the original cap are retained.
No parent licence, source rows, residual range or target mean is assumed. -/
theorem exists_original_bank_residual_error (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (e : ℚ), 0 ≤ e → ∀ (q : ℕ) (omega : ℝ) (cap : ℕ) (z : ℝ)
        (i : Fin 13) (state : FirstExitDepthState ℕ),
      state ∈ selected (.ascending19 i) (data e q omega).e (data e q omega).chi
        (data e q omega).m (data e q omega).omega N cap 0 z
        (fourteenPolicy e q omega (N : ℝ)) →
      let pre := state.selectedPrefix
      let t := point8 (N : ℝ) pre
      let current := lambda6 (data e q omega) (N : ℝ) (rosserAncestor 6 pre)
      |(actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
          ((N : ℝ) ^ current / (pre.prod : ℝ)) -
        actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
          ((N : ℝ) ^ newCap t / (pre.prod : ℝ))) *
          Real.log (N : ℝ) / singularSeries N -
        (4 / (current - total t) - 4 / (newCap t - total t))| < epsilon := by
  obtain ⟨N0, hN0, herror⟩ :=
    OriginalAscendingNineteenArithmeticResidual.exists_original_ascending_frontier_residual_error
      mu epsilon hepsilon
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven e he q omega cap z i state hs
  have hN' : 1 < N := by omega
  obtain ⟨hrows, _hhistory, hupper⟩ :=
    original_selected_parent_dictionary i e he q omega N cap hN' 0 z state hs
  have hs6 := hs
  rw [original_thirteen_selected_list_preserved] at hs6
  have hf : state ∈ firstExitDepthFrontier 8 (policy6 (data e q omega) (N : ℝ))
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) :=
    (List.mem_filter.mp hs6).1
  have hr := rows_physical hrows
  exact herror N hN hEven (lambda6 (data e q omega) (N : ℝ))
    (policy5 (data e q omega) (N : ℝ)) cap z state hf hr hupper
    ((hr.ordered (by decide : (0 : Fin 8) ≤ 7)).trans hr.largestBelowMu)


end
end ImbalancedChen.P2OriginalThirteenUniformArithmeticResidual
