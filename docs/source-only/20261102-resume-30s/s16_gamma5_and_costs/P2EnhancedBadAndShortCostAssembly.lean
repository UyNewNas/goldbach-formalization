import ImbalancedChen.P2EnhancedBadGamma5CostTheta
import ImbalancedChen.P2EnhancedGroupedTripleCostTheta

/-! SOURCE ONLY / UNCOMPILED.
Complete ordinary inclusive cost assembly for bad Gamma5 and Gamma9--19.
All fourteen triple occurrences, four four-prime occurrences, and eighteen
short arithmetic unit occurrences are paid exactly once. Gamma20 and
Gamma21 retain their distinct existing nonunit and unit suppliers. -/
namespace ImbalancedChen.P2EnhancedBadAndShortCostAssembly
noncomputable section
open Real Finset Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization P2EnhancedNonunitMarkedMass
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2EnhancedBadGamma5CostTheta
open P2EnhancedGroupedTripleCostTheta
open P2EnhancedShortWordUnitTheta P2EnhancedShortWordInclusiveMass
open P2EnhancedFourWordCostTheta (fourWords)
open P2SeedOmegaLiteralFunctional (switchedMass)
open scoped Classical BigOperators

def originalCost : ℝ := badRawCost+
  ∑ j : Fin 11, switchedMass ⟨j.val,by omega⟩

theorem original_short_nonunit_split (F : List ℕ → ℝ) :
    (∑ j : Fin 11, ((secondFunctionalMotherGammaWords (9+j.val)).map F).sum) =
      (∑ j : Fin 7, ((P2EnhancedGroupedTripleDictionary.words j).map F).sum)+
      ∑ j : Fin 4, F (fourWords j) := by
  norm_num [Fin.sum_univ_succ,P2EnhancedGroupedTripleDictionary.words,
    secondFunctionalMotherGammaWords,fourWords]
  ring

theorem original_cost_split : originalCost = badRawCost+tripleCost+
    ∑ j : Fin 4, switchedMass (P2EnhancedFourWordCostTheta.costIndex j) := by
  norm_num [originalCost,tripleCost,P2EnhancedGroupedTripleDictionary.costIndex,
    P2EnhancedFourWordCostTheta.costIndex,Fin.sum_univ_succ]
  ring

/-- Source-complete terminal for the previously missing Gamma5 and
Gamma9--15 costs, composed with the supplied R12 four-word and unit costs.
The result is an ordinary mass statement; PP/K/4 count licensing is external.
-/
theorem original_badGamma5_Gamma9_to_19_cost_theta {eta epsilon : ℝ}
    (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      convertedBad N Q D sigma+originalShortOrdinary N Q D sigma ≤
        originalCost*Theta N Q D sigma+epsilon*Theta N Q D sigma := by
  have he4 : 0 < epsilon/4 := by positivity
  obtain ⟨Tb,hTb,hb⟩ := original_badGamma5_cost_theta heta he4
  obtain ⟨Tt,hTt,ht⟩ := original_Gamma9_to_15_nonunit_cost_theta heta he4
  obtain ⟨Tf,hTf,hf⟩ :=
    P2EnhancedFourWordCostTheta.original_Gamma16_to_19_nonunit_cost_theta heta he4
  obtain ⟨Tu,hTu,hu⟩ := original_Gamma9_to_19_unit_theta_payment heta he4
  let T := max (max Tb Tt) (max Tf Tu)
  refine ⟨T,hTb.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  have hb' := hb N (((le_max_left Tb Tt).trans (le_max_left _ _)).trans hN)
    Q D sigma hd hsigma hscale ha
  have ht' := ht N (((le_max_right Tb Tt).trans (le_max_left _ _)).trans hN)
    Q D sigma hd hsigma hscale ha
  have hf' := hf N (((le_max_left Tf Tu).trans (le_max_right _ _)).trans hN)
    Q D sigma hd hsigma hscale ha
  have hu' := hu N (((le_max_right Tf Tu).trans (le_max_right _ _)).trans hN)
    Q D sigma hd hsigma hscale ha
  rw [originalShortOrdinary_eq N Q D sigma hd,original_short_nonunit_split,original_cost_split]
  change convertedBad N Q D sigma+
    (originalShortUnits N Q D sigma+(convertedTriples N Q D sigma+
      ∑ j : Fin 4, convertedWord N Q D sigma (fourWords j))) ≤ _
  nlinarith

end
end ImbalancedChen.P2EnhancedBadAndShortCostAssembly
