import ImbalancedChen.RealHalfProductSieveBridge
import ImbalancedChen.RealUpperCountingAssembly
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Instances.Rat

/-!
# P4B rational-minorant continuity and conditional upper-bound transfer

YELLOW / SOURCE-ONLY / UNCOMPILED DRAFT.

For a fixed real exponent `b` strictly between `1/2` and `1`, continuity
chooses a rational exponent strictly below `b` with arbitrarily small loss
in the coefficient `currentK * log (1 / b)`. The finite antitone theorem
then transfers an actual `RealB` estimate at this rational exponent.

The final theorem assumes the rational-exponent upper estimates explicitly.
It does not instantiate the four same-weight analytic hypotheses of
`eventually_RealB_le_currentK_log_of_same_rho_inputs` and does not close
the manuscript's `hUpper` obligation.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- A rational minorant can be chosen after the real exponent and tolerance,
with an arbitrarily small loss in the actual current upper coefficient. -/
theorem exists_rat_minorant_currentK_log
    {b eta : ℝ} (hb : (1 / 2 : ℝ) < b) (hb1 : b < 1)
    (heta : 0 < eta) :
    ∃ q : ℚ, (1 / 2 : ℚ) < q ∧ (q : ℝ) < b ∧ q < 1 ∧
      currentK * Real.log (1 / (q : ℝ)) ≤
        currentK * Real.log (1 / b) + eta := by
  have hbpos : 0 < b := by linarith
  let f : ℝ → ℝ := fun x => currentK * Real.log (1 / x)
  have hinv : ContinuousAt (fun x : ℝ => 1 / x) b :=
    continuousAt_const.div continuousAt_id hbpos.ne'
  have hbinv : 0 < (1 : ℝ) / b := one_div_pos.mpr hbpos
  have hf : ContinuousAt f b := by
    exact continuousAt_const.mul
      ((Real.continuousAt_log hbinv.ne').comp hinv)
  obtain ⟨delta, hdelta, hnear⟩ :=
    Metric.continuousAt_iff.mp hf eta heta
  have hleft : max (1 / 2 : ℝ) (b - delta) < b :=
    max_lt hb (sub_lt_self b hdelta)
  obtain ⟨q, hqleft, hqb⟩ := exists_rat_btwn hleft
  have hqhalfR : (1 / 2 : ℝ) < (q : ℝ) :=
    (le_max_left _ _).trans_lt hqleft
  have hqdelta : b - delta < (q : ℝ) :=
    (le_max_right _ _).trans_lt hqleft
  have hdist : dist (q : ℝ) b < delta := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hqb)]
    linarith
  have hclose : |f (q : ℝ) - f b| < eta := by
    simpa only [Real.dist_eq] using hnear hdist
  have hcoefficient : currentK * Real.log (1 / (q : ℝ)) ≤
      currentK * Real.log (1 / b) + eta := by
    have hupper := (abs_lt.mp hclose).2
    dsimp only [f] at hupper
    linarith
  refine ⟨q, ?_, hqb, ?_, hcoefficient⟩
  · apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hqhalfR
  · have hqoneR : (q : ℝ) < 1 := hqb.trans hb1
    exact_mod_cast hqoneR

/-- An actual upper bound at a rational minorant transfers to the fixed real
exponent; the coefficient-continuity loss is retained explicitly as `eta`.
The rational upper bound is a premise, including its exact `RealB` count. -/
theorem RealB_cast_le_currentK_log_of_rat_minorant
    {b eta epsilon : ℝ} {q : ℚ} (hb1 : b < 1)
    (hq1 : (q : ℝ) < 1) (hqb : (q : ℝ) ≤ b)
    (hcoefficient : currentK * Real.log (1 / (q : ℝ)) ≤
      currentK * Real.log (1 / b) + eta)
    (N : ℕ)
    (hUpperQ : (RealB (q : ℝ) N : ℝ) ≤
      (currentK * Real.log (1 / (q : ℝ)) + epsilon) *
        singularNormalization N) :
    (RealB b N : ℝ) ≤
      (currentK * Real.log (1 / b) + eta + epsilon) *
        singularNormalization N := by
  have hcount : (RealB b N : ℝ) ≤ (RealB (q : ℝ) N : ℝ) := by
    exact_mod_cast RealB_antitone hq1 hb1 hqb N
  have hnormalization : 0 ≤ singularNormalization N := by
    unfold singularNormalization
    exact div_nonneg
      (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N))
      (sq_nonneg _)
  exact hcount.trans (hUpperQ.trans
    (mul_le_mul_of_nonneg_right
      (add_le_add_right hcoefficient epsilon) hnormalization))

/-- Conditional rational-to-real upper-count assembly. Rational estimates
must already be supplied for every rational exponent in `(1/2, 1)` and
every positive tolerance. The selected rational exponent is fixed before
the eventual target threshold. No analytic upper estimate is proved here. -/
theorem eventually_RealB_le_currentK_log_of_rational_inputs
    (hUpperQ : ∀ q : ℚ, (1 / 2 : ℚ) < q → q < 1 →
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
        (RealB (q : ℝ) N : ℝ) ≤
          (currentK * Real.log (1 / (q : ℝ)) + epsilon) *
            singularNormalization N)
    {b : ℝ} (hb : (1 / 2 : ℝ) < b) (hb1 : b < 1) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + epsilon) * singularNormalization N := by
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := div_pos hepsilon (by norm_num)
  obtain ⟨q, hqhalf, hqb, hq1, hcoefficient⟩ :=
    exists_rat_minorant_currentK_log hb hb1 hhalf
  have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hbudget : currentK * Real.log (1 / b) + epsilon / 2 + epsilon / 2 =
      currentK * Real.log (1 / b) + epsilon := by ring
  filter_upwards [hUpperQ q hqhalf hq1 (epsilon / 2) hhalf] with N hUpperQN
  intro hEven
  have htransfer := RealB_cast_le_currentK_log_of_rat_minorant
    hb1 hq1R hqb.le hcoefficient N (hUpperQN hEven)
  simpa only [hbudget] using htransfer

end

end ImbalancedChen
