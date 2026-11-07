import ImbalancedChen.P2EnhancedCollisionThetaPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPayment

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual finite repaired 21-term source comparison, with its two
exception mechanisms paid uniformly against the SAME original Theta_Q.
The selected-square event has already been paid. Here the three distinct
negative bad-prime windows are summed with the original real sigma and
paid using their existing finite prime-power bound.

Consequently 5 Phi_(11/5) <= actual quotient 21-term RHS + epsilon Theta_Q,
with one threshold before Q, the finite support, sigma, and every marked
tuple. The physical Q/d cutoffs, all original colour words/multiplicities,
and the separate Gamma20/21 unit quotients are retained throughout.

This supplies the combinatorial/source-convention primitive. It is NOT
the enhanced seed gain. Signed ordinary child mean estimates and positive
K switched-product estimates must still be proved on the enhanced stable
prefix family, preserving full/selected squares, inherited cap/ceiling,
and actual alpha. No WuSourceBox identification or unrestricted Upsilon6
lower mean is claimed; its corrected p1*p2 product gate remains required.
-/

namespace ImbalancedChen.P2EnhancedTwentyOneSourceComparison

noncomputable section

open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted P2EnhancedThetaReciprocalMass
open P2EnhancedCollisionThetaPayment
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical

/-- The real three-window cost at the unchanged physical cutoffs. -/
theorem local_bad_primes_le {N d : ℕ} {Q eta : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (hQN : Q ≤ (N : ℝ))
    (hR : 1 < Q / (d : ℝ)) (heta : 0 < eta)
    (hold : ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) :
    localBadPrimes N Q d ≤ (3 / eta) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ eta) := by
  have hdreal : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdQ : (d : ℝ) < Q := by
    simpa only [one_mul] using (lt_div_iff₀ hdreal).mp hR
  have hdN : d ≤ N := by exact_mod_cast hdQ.le.trans hQN
  obtain ⟨_, _, h23, h3s⟩ := cutoff_order Q d hR.le
  exact secondFunctionalMother_three_error_power hN he hd hdN h23 h3s heta hold

theorem weighted_bad_primes_le {N : ℕ} {Q eta : ℝ} (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hN : 4 ≤ N) (he : Even N) (hQN : Q ≤ (N : ℝ)) (heta : 0 < eta)
    (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 < Q / (d : ℝ))
    (hold : ∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) :
    weightedBadPrimes N Q D sigma ≤
      ((3 / eta) * (N : ℝ) / (N : ℝ) ^ eta) * ∑ d ∈ D, sigma d / (d : ℝ) := by
  calc
    weightedBadPrimes N Q D sigma ≤
        ∑ d ∈ D, sigma d * ((3 / eta) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ eta)) := by
      apply sum_le_sum
      intro d hmem
      exact mul_le_mul_of_nonneg_left
        (local_bad_primes_le hN he (hd d hmem) hQN (hR d hmem) heta (hold d hmem))
        (hsigma d hmem)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The threshold for all three negative windows precedes every original weight. -/
theorem bad_primes_theta_payment {eta epsilon : ℝ} (heta : 0 < eta)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      weightedBadPrimes N Q D sigma ≤ epsilon * Theta N Q D sigma := by
  have hU := liuUniversalProduct_pos
  obtain ⟨T, hT, hpay⟩ := ninth_power_log_error_budget 0
    (C := 3 / eta) (α := eta) (ε := 2 * liuUniversalProduct * epsilon)
    (by positivity) heta (by positivity)
  refine ⟨T, by omega, ?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold
  have hN4 : 4 ≤ N := by omega
  have hmass : 0 ≤ ∑ d ∈ D, sigma d / (d : ℝ) :=
    sum_nonneg (fun d hmem => div_nonneg (hsigma d hmem) (Nat.cast_nonneg d))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma
    (fun d hmem => ⟨hR d hmem, residual_level_le_N (hd d hmem) hQN⟩)
  have hbudget : (3 / eta) * (N : ℝ) / (N : ℝ) ^ eta ≤
      (2 * liuUniversalProduct * epsilon) * N / Real.log N ^ 2 := by
    simpa only [pow_zero, mul_one] using hpay N hNT
  calc
    weightedBadPrimes N Q D sigma ≤
        ((3 / eta) * (N : ℝ) / (N : ℝ) ^ eta) * ∑ d ∈ D, sigma d / (d : ℝ) :=
      weighted_bad_primes_le D sigma hN4 he hQN heta hd hsigma hR hold
    _ ≤ ((2 * liuUniversalProduct * epsilon) * N / Real.log N ^ 2) *
        ∑ d ∈ D, sigma d / (d : ℝ) := mul_le_mul_of_nonneg_right hbudget hmass
    _ = epsilon * ((2 * liuUniversalProduct * (N : ℝ) / Real.log N ^ 2) *
        (∑ d ∈ D, sigma d / (d : ℝ))) := by ring
    _ ≤ epsilon * Theta N Q D sigma := mul_le_mul_of_nonneg_left htheta hepsilon.le

/-- The actual repaired 21-term comparison with every finite exception paid.
This is derived from event counts, not assumed as an enhanced native licence. -/
theorem twentyOne_source_comparison {eta epsilon : ℝ} (heta : 0 < eta)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227/50)) →
      5 * Phi N Q D sigma (11/5) ≤
        weightedQuotient N Q D sigma + epsilon * Theta N Q D sigma := by
  obtain ⟨T1, hT1, hcollision⟩ := collision_theta_payment heta (half_pos hepsilon)
  obtain ⟨T2, hT2, hbad⟩ := bad_primes_theta_payment heta (half_pos hepsilon)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold hcut
  have hN1 := (le_max_left T1 T2).trans hNT
  have hN2 := (le_max_right T1 T2).trans hNT
  have hN4 := hT1.trans hN1
  have hfinite := weighted_sameQ_finite N Q D sigma hsigma (fun d hmem => (hR d hmem).le)
  have hc := hcollision N hN1 he Q D sigma hQN hd hsigma hR hold hcut
  have hb := hbad N hN2 he Q D sigma hQN hd hsigma hR hold
  linarith

end
end ImbalancedChen.P2EnhancedTwentyOneSourceComparison
