import ImbalancedChen.FirstExitHistoricalLevels
import ImbalancedChen.ActualRosserInitialResidualSaving

/-!
# Actual minimum caps: finite causal telescope and honest local gain

This source-only predecessor uses the existing historical policies and the
literal actual Rosser densities. A minimum cap must pass both inherited
level comparisons. Its normalized initial residual saving has the minimum
of the two rational gains, with one uniform threshold before the prefix
product, cutoffs, and caps are chosen.

The finite theorem keeps the original rank-four frontier and every next
candidate, including candidates rejected by the old fifth own-cube test.
No integrated minimum is replaced by a minimum of separate integrals.

Remaining manuscript binding: identify the actual 22 selected cap functions
with these finite functions, supply their inherited comparisons and compact
parameter memberships, and integrate/enclose their pointwise minimum on the
actual adopted cells. The results here do not assert that binding or a
full-policy numerical saving. Constants and normalizations are unchanged.
-/

namespace ImbalancedChen.P2CausalMinSaving

noncomputable section

open scoped Classical

/-- The literal initial-branch quotient saving; the common prefix exponent
cancels from the numerator, but remains in both denominators. -/
def initialQuotientGain (old new sigma : ℝ) : ℝ :=
  4 * (new - old) / ((old - sigma) * (new - sigma))

theorem initialQuotientGain_eq_difference {old new sigma : ℝ}
    (hold : 0 < old - sigma) (hnew : 0 < new - sigma) :
    initialQuotientGain old new sigma =
      4 / (old - sigma) - 4 / (new - sigma) := by
  unfold initialQuotientGain
  field_simp [hold.ne', hnew.ne'] <;> ring

/-- Monotonicity is proved for the genuine rational local gain, rather
than asserted for the finite signed Rosser density. -/
theorem initialQuotientGain_mono {old a b sigma : ℝ}
    (hold : 0 < old - sigma) (ha : 0 < a - sigma) (hab : a ≤ b) :
    initialQuotientGain old a sigma ≤ initialQuotientGain old b sigma := by
  have hb : 0 < b - sigma := lt_of_lt_of_le ha (sub_le_sub_right hab sigma)
  have hinv : 1 / (b - sigma) ≤ 1 / (a - sigma) :=
    one_div_le_one_div_of_le ha (sub_le_sub_right hab sigma)
  have hfour : 4 / (b - sigma) ≤ 4 / (a - sigma) := by
    convert mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  rw [initialQuotientGain_eq_difference hold ha,
    initialQuotientGain_eq_difference hold hb]
  exact sub_le_sub_left hfour _

/-- The gain from the smaller cap is exactly the smaller honest local
gain. In particular, summing the two gains would double count this step. -/
theorem initialQuotientGain_min {old a b sigma : ℝ}
    (hold : 0 < old - sigma) (ha : 0 < a - sigma) (hb : 0 < b - sigma) :
    initialQuotientGain old (min a b) sigma =
      min (initialQuotientGain old a sigma) (initialQuotientGain old b sigma) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, min_eq_left (initialQuotientGain_mono hold ha hab)]
  · rw [min_eq_right hba, min_eq_right (initialQuotientGain_mono hold hb hba)]

/-- The existing actual-density supplier remains uniform for a minimum
of two caps. The target is the pointwise minimum of the actual rational
gain profiles, with both candidate cap parameters checked in the same
compact set. No final saving estimate is a hypothesis. -/
theorem exists_actual_quotient_min_saving_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 3 * p.2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y old left right : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y old ∈ T →
        actualRosserQuotientParameters (N : ℝ) P y left ∈ T →
        actualRosserQuotientParameters (N : ℝ) P y right ∈ T →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |(actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ old / P) -
              actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ (min left right) / P)) *
                Real.log (N : ℝ) / singularSeries N -
              min (initialQuotientGain old left (Real.log P / Real.log (N : ℝ)))
                (initialQuotientGain old right (Real.log P / Real.log (N : ℝ)))| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_quotient_saving_threshold T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y old left right hP hy hold hleft hright cap hcap
  have hmin : actualRosserQuotientParameters (N : ℝ) P y (min left right) ∈ T := by
    rcases le_total left right with hlr | hrl
    · simpa only [min_eq_left hlr] using hleft
    · simpa only [min_eq_right hrl] using hright
  have hOldPos : 0 < old - Real.log P / Real.log (N : ℝ) := by
    have h := hparam _ hold
    simpa only [actualRosserQuotientParameters] using h.1.trans h.2.1
  have hLeftPos : 0 < left - Real.log P / Real.log (N : ℝ) := by
    have h := hparam _ hleft
    simpa only [actualRosserQuotientParameters] using h.1.trans h.2.1
  have hRightPos : 0 < right - Real.log P / Real.log (N : ℝ) := by
    have h := hparam _ hright
    simpa only [actualRosserQuotientParameters] using h.1.trans h.2.1
  rw [← initialQuotientGain_min hOldPos hLeftPos hRightPos]
  simpa only [initialQuotientGain] using
    hbound N hN hEven P y old (min left right) hP hy hold hmin cap hcap

/-- A literal strict own-cube admission at a minimum cap is the intersection
of the two original strict gates, including their endpoint convention. -/
theorem ownCube_gate_min (A B : List ℕ → ℝ) (pre : List ℕ) :
    (pre.prod : ℝ) * (pre.headD 0 : ℝ) ^ 2 < min (A pre) (B pre) ↔
      (pre.prod : ℝ) * (pre.headD 0 : ℝ) ^ 2 < A pre ∧
        (pre.prod : ℝ) * (pre.headD 0 : ℝ) ^ 2 < B pre := by
  exact lt_min_iff

/-- The complete actual gated residual selects the smaller cap's density.
This identity makes no unsupported monotonicity claim for finite weights. -/
theorem actualOwnCubeGatedMinusDensity_min (N cap : ℕ)
    (A B : List ℕ → ℝ) (pre : List ℕ) :
    actualOwnCubeGatedMinusDensity N cap (fun history => min (A history) (B history)) pre =
      if A pre ≤ B pre then actualOwnCubeGatedMinusDensity N cap A pre
      else actualOwnCubeGatedMinusDensity N cap B pre := by
  by_cases hab : A pre ≤ B pre
  · simp only [if_pos hab, actualOwnCubeGatedMinusDensity, min_eq_left hab]
  · have hba : B pre ≤ A pre := le_of_not_ge hab
    simp only [if_neg hab, actualOwnCubeGatedMinusDensity, min_eq_right hba]

/-- A common inherited lower level survives taking a minimum of two caps;
the next-step comparison only requires the paired left/right comparisons.
These are geometric cap obligations, not density saving assumptions. -/
theorem actualHistorical_min_cap_telescope
    (base : Bool → List ℕ → Bool) (Q3 A4 B4 A5 B5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ)
    (h34A : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ A4 state.selectedPrefix)
    (h34B : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ B4 state.selectedPrefix)
    (h45A : ∀ frontier ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        A4 frontier.selectedPrefix ≤ A5 candidate.selectedPrefix)
    (h45B : ∀ frontier ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        B4 frontier.selectedPrefix ≤ B5 candidate.selectedPrefix) :
    firstExitRetainedPolynomial (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (fifthCappedUpperPolicy base Q3 (fun pre => min (A5 pre) (B5 pre)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving base Q3 (fun pre => min (A4 pre) (B4 pre)) N cap z +
        actualHistoricalFifthSaving base Q3 (fun pre => min (A4 pre) (B4 pre))
          (fun pre => min (A5 pre) (B5 pre)) N cap z := by
  apply actualHistoricalThirdToFifthSaving_eq
  · intro state hstate
    exact le_min (h34A state hstate) (h34B state hstate)
  · intro frontier hfrontier candidate hcandidate
    exact min_le_min (h45A frontier hfrontier candidate hcandidate)
      (h45B frontier hfrontier candidate hcandidate)

end

end ImbalancedChen.P2CausalMinSaving
