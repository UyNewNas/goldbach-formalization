import ImbalancedChen.Part5OriginalH430SeedSameCarrierPP

/-! Reuse the original bad and long prime tests, four good-pair
occurrences, repeat and centre estimates before choosing the family.
This form applies to positive convolution marks as well as grouped
histories. -/

namespace ImbalancedChen.P2OriginalSeedPositiveBalances
noncomputable section
open Finset
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2EnhancedTwentyOneChildCorrection (positivePairs localPositivePairs)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualLocalPrimeMass)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2EnhancedExactExceptionTheta (weightedErrors localErrors exact_errors_theta_payment)
open P2OriginalW2CentreThetaPayment (all36_charge_theta_payment markedCharge)
open P2OriginalW2ComplementAction (W2Charge)
open P2OriginalW2CountTupleReindex (sourceGoodOccurrence)
open P5OriginalActionMassBound (originalW2At)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430OrdinaryPairCounts (ordinaryIntegral)
open Part5OriginalH430SeedOrdinaryFourIntegral (seed_four_ordinary)
open Part5OriginalH430SignedSeedCount (signedPositive)
open Part5OriginalH430SeedThirteenPrimeWords (restrictedPrime mother_positive_split)
open Part5OriginalH430SeedPurifiedPrimeFibres (switchedFibre restricted_prime_purified)
open Part5OriginalH430SeedSameCarrierPP (converted_eq_untested)
open scoped Classical BigOperators

def goodPairBalance (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  (∑ d ∈ D, σ d * ∑ j : Fin 4, sourceGoodOccurrence N Q (actualState N) d (originalW2At 0) j) -
    (∑ j : Fin 4, ordinaryIntegral 0 j) * Theta N Q D σ

def testedFibreBalance (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, σ d * (switchedFibre true N Q d -
    (K/4)*thetaConversion N d*switchedFibre false N Q d)

theorem positive_component_to_original_balances {η τ ε : ℝ} (hη : 0 < η)
    (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ σ d) →
      (∀ d ∈ D, (N : ℝ)^η ≤ Q/d) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ)^τ ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ)^τ ≤ cutoff Q d (227/50)) →
      signedPositive N Q D σ ≤ goodPairBalance N Q D σ + testedFibreBalance N Q D σ +
        ε*Theta N Q D σ := by
  obtain ⟨Ta,h4,ha⟩ := all36_charge_theta_payment hη (half_pos hε)
  obtain ⟨Tb,_,hb⟩ := exact_errors_theta_payment hτ (half_pos hε)
  refine ⟨max Ta Tb, h4.trans (le_max_left _ _), ?_⟩
  intro N hN he Q D σ hQN hd hσ hscale hold hcut
  have hNa := (le_max_left Ta Tb).trans hN
  have hN4 := h4.trans hNa
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) hη).trans_le (hscale d hm)
  have hcharge := ha N hNa he Q D σ hQN hd hσ hscale 0
  have herror := hb N ((le_max_right Ta Tb).trans hN) he Q D σ hQN hd hσ hR hold hcut
  have hlocal (d : ℕ) (hm : d ∈ D) :
      localPositivePairs N Q d+actualLocalPrimeMass N Q d ≤
        (∑ j : Fin 4, sourceGoodOccurrence N Q (actualState N) d (originalW2At 0) j)+
          switchedFibre true N Q d+W2Charge N Q d 0+localErrors N Q d := by
    linarith only [mother_positive_split hN4 he (hd d hm) (hR d hm),
      restricted_prime_purified Q hN4 he (hd d hm)]
  have hsum := sum_le_sum (s := D) (fun d hm => mul_le_mul_of_nonneg_left
    (hlocal d hm) (hσ d hm))
  simp only [mul_add, sum_add_distrib] at hsum
  unfold markedCharge at hcharge
  unfold weightedErrors at herror
  unfold signedPositive positivePairs goodPairBalance testedFibreBalance
  rw [← seed_four_ordinary, converted_eq_untested,
    Finset.mul_sum D (fun d => σ d*(thetaConversion N d*switchedFibre false N Q d)) (K/4)]
  have hcost (d : ℕ) : (K/4)*(σ d*(thetaConversion N d*switchedFibre false N Q d)) =
      σ d*((K/4)*thetaConversion N d*switchedFibre false N Q d) := by ring
  simp only [hcost, mul_sub, sum_sub_distrib]
  linarith only [hsum,hcharge,herror]

end
end ImbalancedChen.P2OriginalSeedPositiveBalances
