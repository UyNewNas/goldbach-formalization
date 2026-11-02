import ImbalancedChen.P2EnhancedFourWordDictionary

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Moving enhanced-Q arithmetic nonunit masses 16--19 receive their ORIGINAL
literal log costs by reusing Q's mass theorem and the existing hidden cap.
This is thetaConversion of raw mass, with no density or K/4 count claim.
-/
namespace ImbalancedChen.P2EnhancedFourWordCostTheta
noncomputable section
open Real Finset Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization P2EnhancedNonunitMarkedMass
open P2EnhancedFourWordDictionary
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2SeedOmegaLiteralFunctional (switchedMass)
open scoped Classical BigOperators

def fourWords : Fin 4 → List ℕ := ![[2,2,2,2],[2,2,2,3],[2,2,3,3],[1,3,3,3]]
def costIndex : Fin 4 → Fin 13 := ![7,8,9,10]

theorem four_word_literal_cap (alpha : ℝ) (j : Fin 4) :
    nonunitIntegral (fourWords j) alpha ≤ switchedMass (costIndex j) := by
  have h := original_four_word_log_caps alpha
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem four_word_occurrence (j : Fin 4) :
    fourWords j ∈ secondFunctionalMotherGammaWords (9+(⟨7+j.val,by omega⟩ : Fin 13).val) := by
  fin_cases j <;> simp [fourWords,secondFunctionalMotherGammaWords]

theorem literal_four_payload_cap {N : ℕ} {Q : ℝ} {D : Finset ℕ} {sigma : ℕ → ℝ}
    (hN : 4 ≤ N) (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q/d) (j : Fin 4) :
    thetaPayload N Q D sigma (nonunitIntegral (fourWords j)) ≤
      switchedMass (costIndex j)*Theta N Q D sigma := by
  have hp (d : ℕ) (hm : d ∈ D) :
      sigma d*thetaAtom N Q d*nonunitIntegral (fourWords j) (trueAlpha N Q d) ≤
        sigma d*thetaAtom N Q d*switchedMass (costIndex j) :=
    mul_le_mul_of_nonneg_left (four_word_literal_cap (trueAlpha N Q d) j)
      (mul_nonneg (hsigma d hm)
        (P2OriginalPositiveSameQMassLift.thetaAtom_nonneg hN (hd d hm) (hR d hm)))
  have hs := sum_le_sum (s := D) hp
  simpa only [thetaPayload,← sum_mul,← Theta_eq_sum_atoms,mul_comm] using hs

/-- One epsilon budget for the FOUR distinct occurrences, at the same
Q and d-dependent alpha. This composes existing analytic suppliers. -/
theorem original_Gamma16_to_19_nonunit_cost_theta {eta epsilon : ℝ}
    (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      (∑ j : Fin 4, convertedWord N Q D sigma (fourWords j)) ≤
        (∑ j : Fin 4, switchedMass (costIndex j))*Theta N Q D sigma+
          epsilon*Theta N Q D sigma := by
  obtain ⟨T,hT,h⟩ := all_original_word_theta_upper heta (show 0 < 5*epsilon by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN Q D sigma hd hsigma hscale ha
  have hN4 := hT.trans hN
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le (hscale d hm)
  have hj (j : Fin 4) : convertedWord N Q D sigma (fourWords j) ≤
      switchedMass (costIndex j)*Theta N Q D sigma+(epsilon/4)*Theta N Q D sigma := by
    have hm := h N hN Q D sigma hd hsigma hscale ha
      (⟨7+j.val,by omega⟩ : Fin 13) (fourWords j) (four_word_occurrence j)
    have hc := literal_four_payload_cap hN4 hd hsigma hR j
    have heq : (5*epsilon)/20 = epsilon/4 := by ring
    rw [heq] at hm
    linarith
  have hs := sum_le_sum (s := (univ : Finset (Fin 4))) (fun j _ => hj j)
  rw [sum_add_distrib,← sum_mul] at hs
  have heq : (∑ _j : Fin 4, (epsilon/4)*Theta N Q D sigma) =
      epsilon*Theta N Q D sigma := by
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  rwa [heq] at hs

end
end ImbalancedChen.P2EnhancedFourWordCostTheta
