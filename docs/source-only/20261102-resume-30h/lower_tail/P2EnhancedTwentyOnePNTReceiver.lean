import ImbalancedChen.P2EnhancedNegativeChildPNTPayment
import ImbalancedChen.P2EnhancedTwentyOnePhysicalReceiver

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Insert the actual paid PNT error into the ORIGINAL Phi/sifted-count
receiver at the SAME Q.  The independently defined pi-centered physical
AP packet and all positive pair/full switched counts remain literal.
This is neither a signed-density definition of H248 nor its full payment. -/

namespace ImbalancedChen.P2EnhancedTwentyOnePNTReceiver

noncomputable section
open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted P2EnhancedTwentyOneChildCorrection
open P2EnhancedNegativeChildRosser P2EnhancedNegativeChildSignedModulus
open P2EnhancedNegativeChildModulusPrimePayment P2EnhancedNegativeChildPNTPayment
open P2EnhancedTwentyOnePhysicalReceiver
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)

/-- Exact recentering at total pi, with the real signed physical rho.
All nonprimitive raw counts stay in the AP packet.  The modulus-prime
terms cancel between the finite mean and finite discrepancy; they are
not counted twice in this actual-count identity. -/
theorem actual_count_eq_model_add_pi_packet (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) :
    (∑ q ∈ modulusSupport N Q D,
      physicalCoefficient N Q D sigma q * rawPrimeAPCount N q) =
      negativeMean N Q D sigma + piCenteredPhysicalError N Q D sigma +
        (((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N) *
          primitivePhysicalDensity N Q D sigma := by
  rw [model_mean_pushforward]
  unfold piCenteredPhysicalError primitivePhysicalDensity
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hcop : q.Coprime N
  · simp only [childAPMean, hcop, if_true]
    ring
  · simp only [childAPMean, hcop, if_false, mul_zero, sub_zero, add_zero]

/-- The remaining actual analytic error is exactly G's pi-centered
physical AP packet, up to the PNT payment already supplied above. -/
theorem actual_model_error_to_pi_packet_theta_payment {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      |negativeSignedRemainder N Q D sigma - piCenteredPhysicalError N Q D sigma| ≤
        epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, hpay⟩ := actual_pnt_density_theta_payment hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT Q D sigma hQN hd hsigma hR
  have hc := actual_count_eq_model_add_pi_packet N Q D sigma
  rw [← negative_mean_add_error_eq_physical_count] at hc
  have heq : negativeSignedRemainder N Q D sigma - piCenteredPhysicalError N Q D sigma =
      (((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N) *
        primitivePhysicalDensity N Q D sigma := by linarith only [hc]
  rw [heq]
  exact hpay N hNT Q D sigma hQN hd hsigma hR

/-- The real same-Q Phi receiver now consumes a proved PNT payment.
The pi-centered signed AP packet, pairs and all Gamma7--21 switched
counts are explicit remaining INTERNAL obligations, never premises. -/
theorem actual_sameQ_pi_packet_receiver {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      5 * Phi N Q D sigma (11 / 5) + negativeMean N Q D sigma +
        piCenteredPhysicalError N Q D sigma ≤
        4 * Phi N Q D sigma (227 / 50) + Phi N Q D sigma (353 / 100) +
          positivePairs N Q D sigma + switchedCount N Q D sigma +
          epsilon * Theta N Q D sigma := by
  obtain ⟨T1, hT1, hsource⟩ := actual_sameQ_physical_receiver heta (half_pos hepsilon)
  obtain ⟨T2, hT2, hPNT⟩ := actual_pnt_density_theta_payment (half_pos hepsilon)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hNT hEven Q D sigma hQN hd hsigma hR hold hcut
  have hs := hsource N ((le_max_left _ _).trans hNT) hEven Q D sigma
    hQN hd hsigma hR hold hcut
  have hp := hPNT N ((le_max_right _ _).trans hNT) Q D sigma hQN hd hsigma hR
  rw [actual_count_eq_model_add_pi_packet] at hs
  have hlo := (abs_le.mp hp).1
  linarith only [hs, hlo]

/-- Keep every original alpha-inadmissible Phi count as the exact
fallback.  The paid PNT term is inserted only into the admitted family,
with one common Q and its unchanged original normalizer. -/
theorem actual_pi_packet_receiver_with_alpha_fallback {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      let A := alphaAdmitted N Q D
      5 * Phi N Q D sigma (11 / 5) ≤
        4 * Phi N Q A sigma (227 / 50) + Phi N Q A sigma (353 / 100) -
          negativeMean N Q A sigma - piCenteredPhysicalError N Q A sigma +
          positivePairs N Q A sigma + switchedCount N Q A sigma +
          5 * Phi N Q (alphaFallback N Q D) sigma (11 / 5) +
          epsilon * Theta N Q A sigma := by
  obtain ⟨T, hT, hsource⟩ := actual_sameQ_pi_packet_receiver heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT hEven Q D sigma hQN hd hsigma hR hold hcut
  dsimp only
  have hs := hsource N hNT hEven Q (alphaAdmitted N Q D) sigma hQN
    (fun d hdA => hd d (Finset.mem_filter.mp hdA).1)
    (fun d hdA => hsigma d (Finset.mem_filter.mp hdA).1)
    (fun d hdA => hR d (Finset.mem_filter.mp hdA).1)
    (fun d hdA => hold d (Finset.mem_filter.mp hdA).1)
    (fun d hdA => hcut d (Finset.mem_filter.mp hdA).1)
  rw [Phi_exact_alpha_split N Q D sigma (11 / 5)]
  linarith only [hs]

end
end ImbalancedChen.P2EnhancedTwentyOnePNTReceiver
