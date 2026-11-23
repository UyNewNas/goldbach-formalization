import ImbalancedChen.P2EnhancedBadAndShortCostAssembly
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! The seven Gamma9--15 rows of the adopted seed have separate arithmetic
prices. Each price includes the original quotient-one atoms and counts list
occurrences with multiplicity. The row allowances and bad Gamma5 share one
error budget on exactly the input marked family. -/

namespace ImbalancedChen.P2OriginalSeedGammaRowPrices

noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization (trueAlpha thetaPayload)
open P2EnhancedNonunitMarkedMass (nonunitIntegral
  all_original_word_theta_upper)
open P2EnhancedGroupedTripleDictionary (words costIndex)
open P2EnhancedGroupedTripleCostTheta (literal_group_payload_cap original_triple_occurrence_count)
open P2EnhancedShortWordUnitBound (original_short_arity)
open P2EnhancedShortWordUnitTheta (short_word_theta_upper)
open P2EnhancedShortWordInclusiveMass (convertedOrdinary convertedOrdinary_eq_unit_add_nonunit)
open P2EnhancedBadGamma5CostTheta (convertedBad badRawCost original_badGamma5_cost_theta)
open P2SeedOmegaLiteralFunctional (switchedMass)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open scoped Classical BigOperators

theorem original_seed_gamma_row_prices {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ),
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ σ d) →
      (∀ d ∈ D, (N : ℝ)^η ≤ Q/d) → (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      convertedBad N Q D σ ≤ badRawCost * Theta N Q D σ + (ε/2)*Theta N Q D σ ∧
      ∀ j : Fin 7, ((words j).map (convertedOrdinary N Q D σ)).sum ≤
        switchedMass (costIndex j) * Theta N Q D σ +
          ((words j).length : ℝ) * ((ε/28)*Theta N Q D σ) := by
  obtain ⟨Tb, hTb, hb⟩ := original_badGamma5_cost_theta hη (half_pos hε)
  obtain ⟨Tu, _, hu⟩ := short_word_theta_upper hη (show 0 < ε/56 by positivity)
  obtain ⟨Tn, _, hn⟩ := all_original_word_theta_upper hη
    (show 0 < 20*(ε/56) by positivity)
  refine ⟨max Tb (max Tu Tn), hTb.trans (le_max_left _ _), ?_⟩
  intro N hN Q D σ hd hσ hscale hα
  have hNb := (le_max_left Tb (max Tu Tn)).trans hN
  have hNun := (le_max_right Tb (max Tu Tn)).trans hN
  have hNu := (le_max_left Tu Tn).trans hNun
  have hNn := (le_max_right Tu Tn).trans hNun
  have hN4 := hTb.trans hNb
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) hη).trans_le (hscale d hm)
  refine ⟨hb N hNb Q D σ hd hσ hscale hα, ?_⟩
  intro j
  let I (w : List ℕ) := thetaPayload N Q D σ (nonunitIntegral w)
  let E := (ε/28)*Theta N Q D σ
  have each (w : List ℕ) (hw : w ∈ words j) : convertedOrdinary N Q D σ w ≤ I w + E := by
    have hunit := hu N hNu Q D σ hd hσ hscale hα w
      (original_short_arity (⟨j.val, by omega⟩ : Fin 11) hw)
    have hnon := hn N hNn Q D σ hd hσ hscale hα (⟨j.val, by omega⟩ : Fin 13) w hw
    rw [convertedOrdinary_eq_unit_add_nonunit N Q D σ hd]
    dsimp [I,E]
    linarith only [hunit, hnon]
  have hsum := List.sum_le_sum (l := words j) each
  have hsumE : ((words j).map (fun w => I w + E)).sum =
      ((words j).map I).sum + ((words j).length : ℝ)*E := by
    fin_cases j <;> simp [words, secondFunctionalMotherGammaWords] <;> ring
  rw [hsumE] at hsum
  exact hsum.trans (add_le_add (literal_group_payload_cap hN4 hd hσ hR hα j) le_rfl)

/-- The displayed allowances sum to precisely epsilon times the parent
normalizer, even when that normalizer is zero. -/
theorem original_seed_gamma_row_allowances (ε θ : ℝ) :
    (ε/2)*θ + (∑ j : Fin 7, ((words j).length : ℝ)*((ε/28)*θ)) = ε*θ := by
  rw [← sum_mul, original_triple_occurrence_count]
  ring

end
end ImbalancedChen.P2OriginalSeedGammaRowPrices
