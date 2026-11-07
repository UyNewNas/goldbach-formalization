import ImbalancedChen.P2EnhancedGroupedTripleDictionary
import ImbalancedChen.P2EnhancedFourWordCostTheta
import ImbalancedChen.P2EnhancedShortWordInclusiveMass

/-! SOURCE ONLY / UNCOMPILED.
Original Gamma9--15 contains fourteen triple-word occurrences. Its seven
grouped costs are paid only after the a.e. closed-box dictionary. The
same positive marks, Q, true alpha, and original Theta are retained. -/
namespace ImbalancedChen.P2EnhancedGroupedTripleCostTheta
noncomputable section
open Real Finset Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization P2EnhancedNonunitMarkedMass
open P2EnhancedGroupedTripleDictionary
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2SeedOmegaLiteralFunctional (switchedMass)
open scoped Classical BigOperators

def convertedTriples (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ j : Fin 7, ((words j).map (convertedWord N Q D sigma)).sum

def tripleCost : ℝ := ∑ j : Fin 7, switchedMass (costIndex j)

theorem original_triple_occurrence_count :
    (∑ j : Fin 7, ((words j).length : ℝ)) = 14 := by
  norm_num [Fin.sum_univ_succ,words,secondFunctionalMotherGammaWords]

theorem payload_list (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (ws : List (List ℕ)) :
    (ws.map (fun w => thetaPayload N Q D sigma (nonunitIntegral w))).sum =
      ∑ d ∈ D, sigma d*thetaAtom N Q d*
        (ws.map (fun w => nonunitIntegral w (trueAlpha N Q d))).sum := by
  induction ws with
  | nil => simp [thetaPayload]
  | cons w ws ih =>
    simp only [List.map_cons,List.sum_cons,ih,thetaPayload,mul_add,sum_add_distrib]

theorem literal_group_payload_cap {N : ℕ} {Q : ℝ} {D : Finset ℕ} {sigma : ℕ → ℝ}
    (hN : 4 ≤ N) (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q/d) (ha : ∀ d ∈ D, 2 ≤ trueAlpha N Q d) (j : Fin 7) :
    ((words j).map (fun w => thetaPayload N Q D sigma (nonunitIntegral w))).sum ≤
      switchedMass (costIndex j)*Theta N Q D sigma := by
  rw [payload_list]
  have hp (d : ℕ) (hm : d ∈ D) := mul_le_mul_of_nonneg_left
    (original_Gamma9_to_15_literal_cap (ha d hm) j)
    (mul_nonneg (hsigma d hm)
      (P2OriginalPositiveSameQMassLift.thetaAtom_nonneg hN (hd d hm) (hR d hm)))
  have hs := sum_le_sum (s := D) hp
  simpa only [← sum_mul,← Theta_eq_sum_atoms,mul_comm] using hs

private theorem list_error (ws : List (List ℕ)) (F I : List ℕ → ℝ) (E : ℝ)
    (h : ∀ w ∈ ws, F w ≤ I w+E) :
    (ws.map F).sum ≤ (ws.map I).sum+(ws.length : ℝ)*E := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw := h w (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

/-- One threshold before N,Q,d and every positive finite marked family.
No integral/cost/count estimate or positivity of total Theta is assumed. -/
theorem original_Gamma9_to_15_nonunit_cost_theta {eta epsilon : ℝ}
    (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      convertedTriples N Q D sigma ≤
        tripleCost*Theta N Q D sigma+epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,h⟩ := all_original_word_theta_upper heta
    (show 0 < (10/7 : ℝ)*epsilon by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  have hN4 := hT.trans hN
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le (hscale d hm)
  let E := (epsilon/14)*Theta N Q D sigma
  have hwords (j : Fin 7) (w : List ℕ) (hw : w ∈ words j) :
      convertedWord N Q D sigma w ≤
        thetaPayload N Q D sigma (nonunitIntegral w)+E := by
    have hh := h N hN Q D sigma hd hsigma hscale ha
      (⟨j.val,by omega⟩ : Fin 13) w hw
    convert hh using 1 <;> dsimp [E] <;> ring
  have hj (j : Fin 7) : ((words j).map (convertedWord N Q D sigma)).sum ≤
      switchedMass (costIndex j)*Theta N Q D sigma+((words j).length : ℝ)*E :=
    (list_error (words j) _ _ E (hwords j)).trans
      (add_le_add_right (literal_group_payload_cap hN4 hd hsigma hR ha j) _)
  have hs := sum_le_sum (s := (univ : Finset (Fin 7))) (fun j _ => hj j)
  rw [sum_add_distrib,← sum_mul,← sum_mul,original_triple_occurrence_count] at hs
  change convertedTriples N Q D sigma ≤ tripleCost*Theta N Q D sigma+14*E at hs
  convert hs using 1 <;> dsimp [E] <;> ring

end
end ImbalancedChen.P2EnhancedGroupedTripleCostTheta
