import ImbalancedChen.P2EnhancedTwentyOneChildCorrection

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.
The original 21-term source action is normalized by its original positive
Theta, with its genuine negative-child li/phi AP model and signed AP
remainder. The two positive pairs and every marked switched occurrence
remain real counts. No positive-K cost, table endpoint or generic Sound
invariant is a premise. This is the actual count receiver before those
positive costs and the limiting feedback integrals have been proved.
-/
namespace ImbalancedChen.P2EnhancedActualTwentyOneNormalization

noncomputable section
open P2EnhancedTwentyOneSameQWeighted
open P2EnhancedTwentyOneChildCorrection

/-- Uniform thresholds are fixed before the positive marked family and Q.
The divisor five is the actual original 21-term coefficient. In
particular all positive counts survive with coefficient one fifth; they
are not replaced here by an unlicensed current-K scalar. -/
theorem actual_sameQ_normalized_twentyOne_transfer
    {eta epsilon : ℝ} (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q≤(N:ℝ) →
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) →
      (∀d∈D,1<Q/(d:ℝ)) →
      (∀d∈D,∀q∈d.primeFactors,(N:ℝ)^eta≤(q:ℝ)) →
      (∀d∈D,(N:ℝ)^eta≤cutoff Q d (227/50)) →
      (∃d∈D,0<sigma d) →
      Phi N Q D sigma (11/5)/Theta N Q D sigma ≤
        (4*Phi N Q D sigma (227/50)+Phi N Q D sigma (353/100)-
          negativeMean N Q D sigma-negativeSignedRemainder N Q D sigma+
          positivePairs N Q D sigma+switchedCount N Q D sigma)/
            (5*Theta N Q D sigma)+epsilon/5 := by
  obtain ⟨T,hT,htransfer⟩ := actual_sameQ_signed_child_correction heta hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT hEven Q D sigma hQN hd hsigma hR hold hcut hpositive
  have hTheta := Theta_pos (hT.trans hNT) Q D sigma hd hsigma hR hpositive
  have hsource := htransfer N hNT hEven Q D sigma hQN hd hsigma hR hold hcut
  unfold signedChildCorrection at hsource
  let budget : ℝ :=
    4*Phi N Q D sigma (227/50)+Phi N Q D sigma (353/100)-
      negativeMean N Q D sigma-negativeSignedRemainder N Q D sigma+
      positivePairs N Q D sigma+switchedCount N Q D sigma
  have hbound : 5*Phi N Q D sigma (11/5)≤budget+epsilon*Theta N Q D sigma := by
    dsimp [budget]
    linarith
  change Phi N Q D sigma (11/5)/Theta N Q D sigma≤
    budget/(5*Theta N Q D sigma)+epsilon/5
  calc
    Phi N Q D sigma (11/5)/Theta N Q D sigma =
        (5*Phi N Q D sigma (11/5))/(5*Theta N Q D sigma) := by
      field_simp [hTheta.ne'] <;> ring
    _ ≤ (budget+epsilon*Theta N Q D sigma)/(5*Theta N Q D sigma) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = budget/(5*Theta N Q D sigma)+epsilon/5 := by
      field_simp [hTheta.ne'] <;> ring

end
end ImbalancedChen.P2EnhancedActualTwentyOneNormalization
