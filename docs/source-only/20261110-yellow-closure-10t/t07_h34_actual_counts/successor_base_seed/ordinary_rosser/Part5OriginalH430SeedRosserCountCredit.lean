import ImbalancedChen.Part5OriginalH430SeedThreeNegativeMeans

/-! The three genuine negative counts exceed their original Rosser polynomial.
Keep that signed gain through the finite 21-term source identity and its
already-paid square, bad-prime, and pi-recentring errors. -/
namespace ImbalancedChen.Part5OriginalH430SeedRosserCountCredit
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted P2EnhancedTwentyOneQuotientFinite
open P2EnhancedTwentyOneChildCorrection P2EnhancedTwentyOnePNTReceiver
open P2EnhancedNegativeChildModulusPrimePayment (piCenteredPhysicalError)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualLocalPrimeMass actual_marked_source_identity)
open scoped Classical BigOperators

def trueSingles (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  fourthRowMotherSingle N d N (cutoff Q d (227/50)) (cutoff Q d (11/5))+
  fourthRowMotherSingle N d N (cutoff Q d (227/50)) (cutoff Q d (29/10))+
  fourthRowMotherSingle N d N (cutoff Q d (227/50)) (cutoff Q d (61/25))

def credit (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) : ℝ :=
  ∑ d∈D,σ d*(trueSingles N Q d-localNegativeEstimator N Q d)

theorem credit_nonneg {N : ℕ} {Q : ℝ} {D : Finset ℕ} {σ : ℕ → ℝ}
    (hd : ∀ d∈D,0<d) (hs : ∀ d∈D,0≤σ d) (hr : ∀ d∈D,1<Q/(d:ℝ)) :
    0≤credit N Q D σ :=
  sum_nonneg (fun d h => mul_nonneg (hs d h) (sub_nonneg.mpr (localNegativeEstimator_le (hd d h) (hr d h))))

theorem quotient_plus_credit (N : ℕ) (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ) :
    weightedQuotient N Q D σ+credit N Q D σ =
      4*Phi N Q D σ (227/50)+Phi N Q D σ (353/100)-negativeMean N Q D σ-
        negativeSignedRemainder N Q D σ+positivePairs N Q D σ+switchedCount N Q D σ := by
  have hlocal (d : ℕ) : localQuotient N Q d+(trueSingles N Q d-localNegativeEstimator N Q d)=
      4*(sourceSieveCount N d (d*N) (cutoff Q d (227/50)):ℝ)+
        (sourceSieveCount N d (d*N) (cutoff Q d (353/100)):ℝ)-
        localNegativeMean N Q d-localNegativeRemainder N Q d+localPositivePairs N Q d+localSwitched N Q d := by
    rw [localNegativeEstimator_eq]
    unfold localQuotient quotientLocal trueSingles localPositivePairs localSwitched
    ring
  have hsum : (∑ d∈D,σ d*(localQuotient N Q d+(trueSingles N Q d-localNegativeEstimator N Q d)))=
      ∑ d∈D,σ d*(4*(sourceSieveCount N d (d*N) (cutoff Q d (227/50)):ℝ)+
        (sourceSieveCount N d (d*N) (cutoff Q d (353/100)):ℝ)-
        localNegativeMean N Q d-localNegativeRemainder N Q d+localPositivePairs N Q d+localSwitched N Q d) := by
    apply sum_congr rfl
    intro d _
    rw [hlocal]
  unfold weightedQuotient credit Phi negativeMean negativeSignedRemainder positivePairs switchedCount
  simp only [mul_sum,mul_sub,mul_add,sum_sub_distrib,sum_add_distrib,mul_assoc,mul_left_comm,mul_comm] at hsum ⊢
  exact hsum

theorem source_count_with_credit {η ε : ℝ} (hη : 0<η) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (Q : ℝ) (D : Finset ℕ) (σ : ℕ → ℝ),
      Q≤(N:ℝ) → (∀ d∈D,0<d) → (∀ d∈D,0≤σ d) → (∀ d∈D,1<Q/(d:ℝ)) →
      (∀ d∈D,∀ q∈d.primeFactors,(N:ℝ)^η≤(q:ℝ)) → (∀ d∈D,(N:ℝ)^η≤cutoff Q d (227/50)) →
      5*Phi N Q D σ (11/5)+credit N Q D σ+negativeMean N Q D σ+piCenteredPhysicalError N Q D σ ≤
        4*Phi N Q D σ (227/50)+Phi N Q D σ (353/100)+positivePairs N Q D σ+
          (∑ d∈D,σ d*actualLocalPrimeMass N Q d)+ε*Theta N Q D σ := by
  obtain ⟨Ta,h4,ha⟩ := P2EnhancedTwentyOneSourceComparison.twentyOne_source_comparison hη (half_pos he)
  obtain ⟨Tb,_,hb⟩ := actual_model_error_to_pi_packet_theta_payment (half_pos he)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN hEven Q D σ hQN hd hσ hR hrough hcut
  have hN4 := h4.trans ((le_max_left _ _).trans hN)
  have hs := ha N ((le_max_left _ _).trans hN) hEven Q D σ hQN hd hσ hR hrough hcut
  have hπ := (abs_le.mp (hb N ((le_max_right _ _).trans hN) Q D σ hQN hd hσ hR)).1
  have hc := quotient_plus_credit N Q D σ
  rw [actual_marked_source_identity Q D σ hN4 hEven hd] at hc
  linarith only [hs,hπ,hc]

end
end ImbalancedChen.Part5OriginalH430SeedRosserCountCredit
