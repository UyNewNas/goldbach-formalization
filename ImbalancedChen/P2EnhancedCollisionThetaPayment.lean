import ImbalancedChen.P2EnhancedCollisionWeightedBudget
import ImbalancedChen.P2EnhancedThetaReciprocalMass
import MathlibNt.Wu2008DoubleSieve.NinthErrorPaymentAsymptotic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual selected-square collisions are o(Theta_Q), uniformly over the
original finite nonnegative real sigma weights and all common levels
Q<=N satisfying the fixed-positive-cutoff hypotheses. The threshold is
chosen before N, Q, support, weights, and all marked tuples.

The proof uses the explicit weighted collision count, the exact original
Theta reciprocal-mass lower bound, and the existing proved power-log
budget. No source count estimate, enhanced gain, or table value is an
assumption. The normalization is never changed to a child level.
-/

namespace ImbalancedChen.P2EnhancedCollisionThetaPayment

noncomputable section

open Finset Filter Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted P2EnhancedCollisionWeightedBudget
open P2EnhancedThetaReciprocalMass
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical Topology

theorem residual_level_le_N {N d : ℕ} {Q : ℝ} (hd : 0 < d) (hQ : Q ≤ (N : ℝ)) :
    Q / (d : ℝ) ≤ N := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNd : (N : ℝ) ≤ (N : ℝ) * d := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 (Nat.cast_nonneg N)
  exact (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr (hQ.trans hNd)

theorem collision_coefficient_le {N : ℕ} {eta : ℝ} (heta : 0 < eta)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    22 * (1 + Real.log N) ^ 6 * (1 / eta) * (N : ℝ) / (N : ℝ) ^ eta ≤
      (1408 / eta) * (N : ℝ) * Real.log N ^ 6 / (N : ℝ) ^ eta := by
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log (N : ℝ))
    (by linarith : 1 + Real.log (N : ℝ) ≤ 2 * Real.log N) 6
  have hcoef : 0 ≤ 22 * (1 / eta) * (N : ℝ) / (N : ℝ) ^ eta := by positivity
  calc
    _ ≤ 22 * (2 * Real.log N) ^ 6 * (1 / eta) * (N : ℝ) / (N : ℝ) ^ eta := by
      convert mul_le_mul_of_nonneg_left hpow hcoef using 1 <;> ring
    _ = _ := by ring

/-- A genuine uniform relative payment for the actual collision counts.
The finite support can be empty and the given sigma weights can all vanish. -/
theorem collision_theta_payment {eta epsilon : ℝ} (heta : 0 < eta)
    (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227/50)) →
      weightedCollisions N Q D sigma ≤ epsilon * Theta N Q D sigma := by
  have hU := liuUniversalProduct_pos
  obtain ⟨T1, hT1, hpay⟩ := ninth_power_log_error_budget 6
    (C := 1408 / eta) (α := eta) (ε := 2 * liuUniversalProduct * epsilon)
    (by positivity) heta (by positivity)
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hlogT⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2, by omega, ?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold hcut
  have hN1 := (le_max_left T1 T2).trans hNT
  have hN4 : 4 ≤ N := by omega
  have hlog1 := hlogT N ((le_max_right T1 T2).trans hNT)
  have hmass : 0 ≤ ∑ d ∈ D, sigma d / (d : ℝ) :=
    sum_nonneg (fun d hmem => div_nonneg (hsigma d hmem) (Nat.cast_nonneg d))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma
    (fun d hmem => ⟨hR d hmem, residual_level_le_N (hd d hmem) hQN⟩)
  calc
    weightedCollisions N Q D sigma ≤
        (22 * (1 + Real.log N) ^ 6 * (1 / eta) * (N : ℝ) / (N : ℝ) ^ eta) *
          ∑ d ∈ D, sigma d / (d : ℝ) :=
      weightedCollisions_le D sigma hN4 he hQN heta hd hsigma
        (fun d hmem => (hR d hmem).le) hold hcut
    _ ≤ ((1408 / eta) * (N : ℝ) * Real.log N ^ 6 / (N : ℝ) ^ eta) *
        ∑ d ∈ D, sigma d / (d : ℝ) :=
      mul_le_mul_of_nonneg_right (collision_coefficient_le heta hlog1) hmass
    _ ≤ ((2 * liuUniversalProduct * epsilon) * N / Real.log N ^ 2) *
        ∑ d ∈ D, sigma d / (d : ℝ) :=
      mul_le_mul_of_nonneg_right (hpay N hN1) hmass
    _ = epsilon * ((2 * liuUniversalProduct * (N : ℝ) / Real.log N ^ 2) *
        (∑ d ∈ D, sigma d / (d : ℝ))) := by ring
    _ ≤ epsilon * Theta N Q D sigma := mul_le_mul_of_nonneg_left htheta hepsilon.le

end
end ImbalancedChen.P2EnhancedCollisionThetaPayment
