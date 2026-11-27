import ImbalancedChen.ActualRosserResidualDensity
import ImbalancedChen.ActualRosserCubeLimit
import ImbalancedChen.ActualRosserUpperGeneralLimit

/-!
# Actual residual-density savings on the initial upper branch

Uniqueness of the already proved actual density limits identifies the
canonical continuous upper factor on `1<s<=3`. This turns the compact
residual theorem into a common `4/beta` threshold. Subtracting those
two-sided estimates for the same literal coefficients gives the rational
saving for a cap change, uniformly before its varying residual parameters.
This is not a subtraction of unrelated one-sided sieve inequalities.

The result concerns the ordinary residual subtree. Causal replacement,
prefix mass integration and the manuscript's certified boxes are separate.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory

theorem positiveEvenNatAtTop_neBot :
    (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}).NeBot := by
  rw [Filter.inf_principal_neBot_iff]
  intro U hU
  obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.mp hU
  refine ⟨2 * (a + 1), ha _ (by omega), by omega, ?_⟩
  exact ⟨a + 1, by omega⟩

/-- The canonical factor is identified using two limits of the same
actual coefficient, including the part of the branch below `3/2`. -/
theorem suzukiContinuousUpperFactor_eq_initial_of_actual_limits
    (s : ℝ) (hs : 1 < s) (hs3 : s ≤ 3) :
    suzukiContinuousUpperFactor s = 2 * Real.exp Real.eulerMascheroniConstant / s := by
  have := positiveEvenNatAtTop_neBot
  have hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) := Filter.Eventually.of_forall (by simp)
  exact tendsto_nhds_unique
    (tendsto_actualSmallRosserPlusDensity_general_ratio 1 (by norm_num) s hs id hcap)
    (tendsto_actualSmallRosserPlusDensity_fixedResidual_ratio 1 (by norm_num)
      s (by linarith) hs3 id hcap)

theorem normalized_suzukiUpperFactor_initial
    (beta u : ℝ) (hu : 0 < u) (hub : u < beta) (hbu : beta ≤ 3 * u) :
    (2 * Real.exp (-Real.eulerMascheroniConstant) / u) *
        suzukiContinuousUpperFactor (beta / u) = 4 / beta := by
  have hs : 1 < beta / u := (one_lt_div hu).mpr hub
  have hs3 : beta / u ≤ 3 := (div_le_iff₀ hu).mpr hbu
  rw [suzukiContinuousUpperFactor_eq_initial_of_actual_limits (beta / u) hs hs3,
    Real.exp_neg]
  have hbeta : beta ≠ 0 := ne_of_gt (hu.trans hub)
  field_simp [hu.ne', hbeta, Real.exp_ne_zero]
  ring

theorem exists_actualSmallRosserPlusDensity_initial_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ T, ∀ cap : ℕ, (N : ℝ) ^ p.2 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) *
            Real.log (N : ℝ) / singularSeries N - 4 / p.1| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_residual_compact_normalized_threshold
      T hT (fun p hp => ⟨(hparam p hp).1, (hparam p hp).2.1⟩) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  have h := hbound N hN hEven p hp cap hcap
  rw [normalized_suzukiUpperFactor_initial p.1 p.2
    (hparam p hp).1 (hparam p hp).2.1 (hparam p hp).2.2] at h
  exact h

/-- One threshold controls the exact difference of two actual residual
densities. No order between the two caps is needed for the identity. -/
theorem exists_actualSmallRosserPlusDensity_initial_compact_difference_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ betaOld betaNew u : ℝ, (betaOld, u) ∈ T → (betaNew, u) ∈ T →
        ∀ cap : ℕ, (N : ℝ) ^ u ≤ (cap : ℝ) →
          |(actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ betaOld) -
              actualSmallRosserPlusDensity N cap ((N : ℝ) ^ u) ((N : ℝ) ^ betaNew)) *
                Real.log (N : ℝ) / singularSeries N -
              4 * (betaNew - betaOld) / (betaOld * betaNew)| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_compact_normalized_threshold
      T hT hparam (eta / 2) (by linarith)
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven betaOld betaNew u hOld hNew cap hcap
  have hold := abs_lt.mp (hbound N hN hEven (betaOld, u) hOld cap hcap)
  have hnew := abs_lt.mp (hbound N hN hEven (betaNew, u) hNew cap hcap)
  have hOld0 : betaOld ≠ 0 := ne_of_gt ((hparam _ hOld).1.trans (hparam _ hOld).2.1)
  have hNew0 : betaNew ≠ 0 := ne_of_gt ((hparam _ hNew).1.trans (hparam _ hNew).2.1)
  have hconstant : 4 * (betaNew - betaOld) / (betaOld * betaNew) =
      4 / betaOld - 4 / betaNew := by field_simp
  rw [hconstant, sub_mul, sub_div]
  dsimp only at hold hnew
  exact abs_lt.mpr ⟨by linarith [hold.1, hnew.2], by linarith [hold.2, hnew.1]⟩

/-- The quotient-level form is uniform before the actual varying prefix
product and both caps. Its rational numerator is the new cap minus the
current parent cap, with the common prefix exponent cancelling exactly. -/
theorem exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambdaOld lambdaNew : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y lambdaOld ∈ T →
        actualRosserQuotientParameters (N : ℝ) P y lambdaNew ∈ T →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |(actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambdaOld / P) -
              actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambdaNew / P)) *
                Real.log (N : ℝ) / singularSeries N -
              4 * (lambdaNew - lambdaOld) /
                ((lambdaOld - Real.log P / Real.log (N : ℝ)) *
                  (lambdaNew - Real.log P / Real.log (N : ℝ)))| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_compact_difference_threshold T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambdaOld lambdaNew hP hy hOld hNew cap hcap
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hOldLevel, hcut⟩ := actualRosserQuotientParameters_exact
    (N : ℝ) P y lambdaOld hN1 hP hy
  obtain ⟨hNewLevel, _⟩ := actualRosserQuotientParameters_exact
    (N : ℝ) P y lambdaNew hN1 hP hy
  simp only [actualRosserQuotientParameters] at hOldLevel hNewLevel hcut
  have h := hbound N hN hEven
    (lambdaOld - Real.log P / Real.log (N : ℝ))
    (lambdaNew - Real.log P / Real.log (N : ℝ))
    (Real.log y / Real.log (N : ℝ)) hOld hNew cap (by simpa only [hcut] using hcap)
  rw [hOldLevel, hNewLevel, hcut] at h
  have hcancel : (lambdaNew - Real.log P / Real.log (N : ℝ)) -
      (lambdaOld - Real.log P / Real.log (N : ℝ)) = lambdaNew - lambdaOld := by ring
  simpa only [hcancel] using h

end

end ImbalancedChen
