import ImbalancedChen.P1VariableOwnCubeResidualUniformity
import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

A compact cap-rounding error supplier for the literal actual lower Rosser
residual, at any nonempty prefix rank.  The modulus of continuity is proved
for the canonical factor, uniformly in rank.  The arithmetic threshold uses
the existing uniform-level supplier; no residual convergence is assumed.

The weighted conclusion sums ABSOLUTE errors on the actual target-deleted
prime tuples.  Its threshold precedes the later subset and both cap tables.
There is no cell-count cost, no ordering factorial, and the two strict
own-cube gates remain present on the arithmetic side.  A cap or history
construction must still identify these terms with its signed source.
This module alone does not claim full87, All22, or a total density reserve.
-/

namespace ImbalancedChen.P4AActualOwnCubeCapPayment

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators

/-- The existing canonical normalization, for every nonempty prefix rank. -/
theorem profile_eq_canonical {k : ℕ} (lam : ℝ) (t : Fin (k + 1) → ℝ)
    (hz : 0 < t (Fin.last k)) :
    primeTupleMinusProfile lam t =
      4 * actualExtendedThirdLowerFactor
        ((lam - ∑ i, t i) / t (Fin.last k)) / t (Fin.last k) := by
  unfold primeTupleMinusProfile actualExtendedThirdLowerFactor thirdTailLowerFactor
  rw [Real.exp_neg]
  field_simp [hz.ne', (Real.exp_pos Real.eulerMascheroniConstant).ne']
  <;> ring

/-- Failure, including equality, costs zero in the actual continuous
extension.  This removes no arithmetic history and trims no equality wall. -/
theorem ownCube_profile_gate {k : ℕ} (lam : ℝ) (t : Fin (k + 1) → ℝ)
    (hz : 0 < t (Fin.last k)) :
    (if primeTupleOwnCubeForm t < lam then primeTupleMinusProfile lam t else 0) =
      primeTupleMinusProfile lam t := by
  split_ifs with hg
  · rfl
  · have hratio : (lam - ∑ i, t i) / t (Fin.last k) ≤ 2 := by
      apply (div_le_iff₀ hz).mpr
      have hgate := le_of_not_gt hg
      dsimp only [primeTupleOwnCubeForm] at hgate
      linarith
    rw [profile_eq_canonical lam t hz,
      actualExtendedThirdLowerFactor_of_le_two hratio, mul_zero, zero_div]

private theorem clamped_argument_mem {k : ℕ} {a theta lam : ℝ}
    (ha : 0 < a) (htheta : 0 ≤ theta) (hlam : lam ≤ theta)
    (t : Fin (k + 1) → ℝ) (ht : ∀ i, a ≤ t i) :
    max 2 ((lam - ∑ i, t i) / t (Fin.last k)) ∈
      Icc (2 : ℝ) (max 2 (theta / a)) := by
  have hz := ha.trans_le (ht (Fin.last k))
  have hsum : 0 ≤ ∑ i, t i :=
    Finset.sum_nonneg (fun i _ => (ha.trans_le (ht i)).le)
  refine ⟨le_max_left _ _, max_le (le_max_left _ _) ?_⟩
  calc
    (lam - ∑ i, t i) / t (Fin.last k) ≤ theta / t (Fin.last k) :=
      div_le_div_of_nonneg_right (by linarith) hz.le
    _ ≤ theta / a := by
      apply (div_le_div_iff₀ hz ha).mpr
      exact mul_le_mul_of_nonneg_left (ht (Fin.last k)) htheta
    _ ≤ max 2 (theta / a) := le_max_right _ _

/-- One cap modulus works at every rank.  Only the positive last-prime
cutoff and fixed physical ceiling enter the compact argument interval. -/
theorem exists_rank_uniform_profile_cap_modulus (a theta eta : ℝ)
    (ha : 0 < a) (htheta : 0 ≤ theta) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ k : ℕ, ∀ lam L : ℝ,
      lam ≤ theta → L ≤ theta → |lam - L| ≤ delta →
      ∀ t : Fin (k + 1) → ℝ, (∀ i, a ≤ t i) →
        |primeTupleMinusProfile lam t - primeTupleMinusProfile L t| ≤ eta := by
  let tau : ℝ := eta * a / 8
  have htau : 0 < tau := by dsimp [tau]; positivity
  have huc : UniformContinuousOn actualExtendedThirdLowerFactor
      (Icc (2 : ℝ) (max 2 (theta / a))) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      continuous_actualExtendedThirdLowerFactor.continuousOn
  obtain ⟨d, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc tau htau
  refine ⟨d * a / 2, by positivity, ?_⟩
  intro k lam L hlam hL hgap t ht
  have hz : 0 < t (Fin.last k) := ha.trans_le (ht (Fin.last k))
  have hraw : |(lam - ∑ i, t i) / t (Fin.last k) -
      (L - ∑ i, t i) / t (Fin.last k)| ≤ d / 2 := by
    calc
      _ = |lam - L| / t (Fin.last k) := by
        rw [← sub_div, abs_div, abs_of_pos hz]
        congr 2
        ring
      _ ≤ (d * a / 2) / t (Fin.last k) :=
        div_le_div_of_nonneg_right hgap hz.le
      _ ≤ d / 2 := by
        apply (div_le_iff₀ hz).mpr
        nlinarith [mul_le_mul_of_nonneg_left (ht (Fin.last k)) (half_pos hd).le]
  have hclamp : |max 2 ((lam - ∑ i, t i) / t (Fin.last k)) -
      max 2 ((L - ∑ i, t i) / t (Fin.last k))| ≤ d / 2 := by
    calc
      _ ≤ |(lam - ∑ i, t i) / t (Fin.last k) -
          (L - ∑ i, t i) / t (Fin.last k)| := by
        simpa only [max_comm] using (_root_.abs_max_sub_max_le_abs
          ((lam - ∑ i, t i) / t (Fin.last k))
          ((L - ∑ i, t i) / t (Fin.last k)) (2 : ℝ))
      _ ≤ d / 2 := hraw
  have hdist : dist (max 2 ((lam - ∑ i, t i) / t (Fin.last k)))
      (max 2 ((L - ∑ i, t i) / t (Fin.last k))) < d := by
    rw [Real.dist_eq]
    exact hclamp.trans_lt (half_lt_self hd)
  have hf := hclose _ (clamped_argument_mem ha htheta hlam t ht)
    _ (clamped_argument_mem ha htheta hL t ht) hdist
  have hfactor : |actualExtendedThirdLowerFactor ((lam - ∑ i, t i) / t (Fin.last k)) -
      actualExtendedThirdLowerFactor ((L - ∑ i, t i) / t (Fin.last k))| ≤ tau := by
    simpa only [Real.dist_eq, actualExtendedThirdLowerFactor, ← max_assoc, max_self]
      using hf.le
  rw [profile_eq_canonical lam t hz, profile_eq_canonical L t hz,
    ← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hz,
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  calc
    _ ≤ 4 * tau / t (Fin.last k) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor (by norm_num)) hz.le
    _ ≤ 4 * tau / a := by
      apply (div_le_div_iff₀ hz ha).mpr
      exact mul_le_mul_of_nonneg_left (ht (Fin.last k)) (by positivity)
    _ = eta / 2 := by dsimp [tau]; field_simp [ha.ne']; ring
    _ ≤ eta := by linarith

/-- The existing uniform-level arithmetic theorem is used for two caps
selected AFTER N0, on the same tuple, target deletion and enumeration cap. -/
theorem exists_actual_cap_difference_threshold (k : ℕ) (a b lower theta eta : ℝ)
    (ha : 0 < a) (htheta : 0 ≤ theta) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
      ∀ lam L : ℝ, lam ∈ Icc lower theta → L ∈ Icc lower theta →
      |lam - L| ≤ delta →
        |actualPrimeTupleOwnCubeMinus N cap lam p -
          actualPrimeTupleOwnCubeMinus N cap L p| < eta := by
  have heta3 : 0 < eta / 3 := by positivity
  obtain ⟨delta, hd, hmod⟩ :=
    exists_rank_uniform_profile_cap_modulus a theta (eta / 3) ha htheta heta3
  obtain ⟨N0, hN0, hres⟩ :=
    P1VariableOwnCubeResidualUniformity.exists_actualPrimeTupleOwnCubeMinus_uniform_levels_threshold
      k a b lower theta ha (eta / 3) heta3
  refine ⟨delta, hd, N0, hN0, ?_⟩
  intro N hN hEven cap hcap p hp lam L hlam hL hgap
  have hlog := ((mem_actualPrimeBoxTuples_log_iff (by omega : 1 < N) _ _ p).mp hp).2
  have ht : ∀ i, a ≤ actualPrimeTupleLog N p i :=
    fun i => (mem_logPrimeBox.mp hlog i).1
  have hz : 0 < actualPrimeTupleLog N p (Fin.last k) := ha.trans_le (ht _)
  have hleft := hres N hN hEven cap hcap p hp lam hlam
  have hright := hres N hN hEven cap hcap p hp L hL
  rw [ownCube_profile_gate lam _ hz] at hleft
  rw [ownCube_profile_gate L _ hz] at hright
  have hm := hmod k lam L hlam.2 hL.2 hgap (actualPrimeTupleLog N p) ht
  have ht1 := abs_sub_le (actualPrimeTupleOwnCubeMinus N cap lam p)
    (primeTupleMinusProfile lam (actualPrimeTupleLog N p))
    (actualPrimeTupleOwnCubeMinus N cap L p)
  have ht2 := abs_sub_le (primeTupleMinusProfile lam (actualPrimeTupleLog N p))
    (primeTupleMinusProfile L (actualPrimeTupleLog N p))
    (actualPrimeTupleOwnCubeMinus N cap L p)
  rw [abs_sub_comm (primeTupleMinusProfile L _)] at ht2
  linarith

/-- Literal weighted absolute cap error. The prime tuples, rather than
mesh atoms, are the charged objects; original multiplicity is retained. -/
def capDefect (k N cap : ℕ) (chosen : Finset (Fin (k + 1) → ℕ))
    (lam L : (Fin (k + 1) → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ chosen, (∏ i, 1 / ((p i : ℝ) - 1)) *
    |actualPrimeTupleOwnCubeMinus N cap (lam p) p -
      actualPrimeTupleOwnCubeMinus N cap (L p) p|

/-- Genuine arithmetic payment.  The threshold is uniform over all later
subsets and cap tables satisfying only their geometric range and modulus.
No actual-error or full-policy density estimate is a premise. -/
theorem exists_weighted_cap_payment (k : ℕ) (a b lower theta eta : ℝ)
    (ha : 0 < a) (hab : a < b) (htheta : 0 ≤ theta) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N → ∀ cap : ℕ,
      (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ chosen : Finset (Fin (k + 1) → ℕ),
      chosen ⊆ actualPrimeBoxTuples N (fun _ => a) (fun _ => b) →
      ∀ lam L : (Fin (k + 1) → ℕ) → ℝ,
      (∀ p ∈ chosen, lam p ∈ Icc lower theta ∧ L p ∈ Icc lower theta ∧
        |lam p - L p| ≤ delta) →
        capDefect k N cap chosen lam L < eta := by
  let B : ℝ := |∏ i : Fin (k + 1), Real.log (b / a)| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hmass : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin (k + 1) => a) (fun _ => b) < B :=
    (tendsto_actualPrimeBoxMass (fun _ : Fin (k + 1) => a) (fun _ => b)
      (fun _ => ha) (fun _ => hab)).eventually (gt_mem_nhds (by
        dsimp [B]
        linarith [le_abs_self (∏ i : Fin (k + 1), Real.log (b / a))]))
  obtain ⟨Nm, hm⟩ := eventually_atTop.mp hmass
  obtain ⟨delta, hd, Nr, hNr, hres⟩ := exists_actual_cap_difference_threshold
    k a b lower theta (eta / (2 * B)) ha htheta (by positivity)
  refine ⟨delta, hd, max Nm Nr, hNr.trans (le_max_right _ _), ?_⟩
  intro N hN hEven cap hcap chosen hchosen lam L hlevels
  have hNmass := (hm N ((le_max_left _ _).trans hN)).le
  have hNres : Nr ≤ N := (le_max_right _ _).trans hN
  have hsum : capDefect k N cap chosen lam L ≤
      (∑ p ∈ chosen, ∏ i, 1 / ((p i : ℝ) - 1)) * (eta / (2 * B)) := by
    unfold capDefect
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro p hp
    have he := hlevels p hp
    exact mul_le_mul_of_nonneg_left
      (hres N hNres hEven cap hcap p (hchosen hp) (lam p) (L p)
        he.1 he.2.1 he.2.2).le
      (actualPrimeBoxWeight_nonneg (hchosen hp))
  have hweight : (∑ p ∈ chosen, ∏ i, 1 / ((p i : ℝ) - 1)) ≤
      actualPrimeBoxMass N (fun _ : Fin (k + 1) => a) (fun _ => b) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hchosen
      (fun p hp _ => actualPrimeBoxWeight_nonneg hp)
  calc
    capDefect k N cap chosen lam L ≤
        (∑ p ∈ chosen, ∏ i, 1 / ((p i : ℝ) - 1)) * (eta / (2 * B)) := hsum
    _ ≤ B * (eta / (2 * B)) :=
      mul_le_mul_of_nonneg_right (hweight.trans hNmass) (by positivity)
    _ = eta / 2 := by field_simp [hB.ne']; ring
    _ < eta := half_lt_self heta

end
end ImbalancedChen.P4AActualOwnCubeCapPayment
