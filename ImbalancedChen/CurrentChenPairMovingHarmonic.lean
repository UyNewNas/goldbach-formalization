import ImbalancedChen.CurrentChenPairHarmonicMean
import ImbalancedChen.MovingWeightTransport

/-!
# The actual rounded fifth-row harmonic integral

The actual reciprocal-totient pair mass is bounded by its proved arithmetic
prime-box limit. Uniform control of the rounded row coordinate and compact
continuity then give the same integral at the genuine integer row levels.
There is no density, distribution, count-mean or harmonic-limit hypothesis.

Executed verification status is recorded in
`docs/PROOF_CONTINUATION_2026-10-15.md`.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory
open scoped BigOperators
open Classical

/-- The ordinary, variable-residual integral on the actual strict fifth
triangle. This definition does not substitute a numerical certificate. -/
def currentChenUpsilon5OrdinaryIntegral : ℝ :=
  ∫ x in logPrimeBox (fun _ : Fin 2 => (417 / 5000 : ℝ))
      (fun _ => (19 / 125 : ℝ)) ∩
      primeAffineGateRegion currentChenPairOrderForms (fun _ => 0),
    currentChenPairOrdinaryKernel x * ∏ i, 1 / x i

def currentChenUpsilon5OrdinaryFactor (s : ℝ) : ℝ :=
  4 * Real.log (s - 1) / (s * (417 / 5000))

theorem continuousOn_currentChenUpsilon5OrdinaryFactor :
    ContinuousOn currentChenUpsilon5OrdinaryFactor (Set.Icc (2 : ℝ) 4) := by
  unfold currentChenUpsilon5OrdinaryFactor
  apply (continuousOn_const.mul
    ((continuousOn_id.sub continuousOn_const).log ?_)).div
    (continuousOn_id.mul continuousOn_const) ?_
  · intro s hs
    exact (show 0 < s - 1 by linarith [hs.1]).ne'
  · intro s hs
    exact mul_ne_zero (show 0 < s by linarith [hs.1]).ne' (by norm_num)

/-- The total reciprocal-totient mass of the actual strict pair selector
is bounded by an independently proved prime-box limit. -/
theorem currentChenUpsilon5_reciprocalTotient_eventually_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop,
      (∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)), 1 / (Nat.totient (t.1 * t.2) : ℝ)) ≤ M := by
  have h := tendsto_currentChenUpsilon5_harmonic_test (fun _ => (1 : ℝ))
    continuousOn_const
  exact exists_eventually_bounded_mass_of_tendsto h

/-- The actual integer row parameter has the same harmonic integral as
its logarithmic profile. Its nonnegative mass is supplied above, and both
coordinates remain in one proved compact subset of the first interval. -/
theorem tendsto_currentChenUpsilon5_ordinary_moving_harmonic (B : ℝ) :
    Tendsto (fun N : ℕ =>
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
        ((N : ℝ) ^ (19 / 125 : ℝ)),
        (1 / (Nat.totient (t.1 * t.2) : ℝ)) *
          currentChenUpsilon5OrdinaryFactor
            (chenQuotientRosserT B (417 / 5000) N (t.1 * t.2)))
      atTop (𝓝 currentChenUpsilon5OrdinaryIntegral) := by
  obtain ⟨M, hM, hmass⟩ := currentChenUpsilon5_reciprocalTotient_eventually_bounded
  let T := fun N : ℕ => chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ))
  let w := fun (_N : ℕ) (t : ℕ × ℕ) => 1 / (Nat.totient (t.1 * t.2) : ℝ)
  let x := fun N (t : ℕ × ℕ) => chenQuotientRosserT B (417 / 5000) N (t.1 * t.2)
  let y := fun N (t : ℕ × ℕ) => currentChenPairLogProfile N (t.1 * t.2)
  have hfixed : Tendsto (fun N : ℕ =>
      ∑ t ∈ T N, w N t * currentChenUpsilon5OrdinaryFactor (y N t)) atTop
        (𝓝 currentChenUpsilon5OrdinaryIntegral) := by
    have h := tendsto_currentChenUpsilon5_ordinary_harmonic_mean
    apply h.congr'
    apply Eventually.of_forall
    intro N
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [w, y, currentChenUpsilon5OrdinaryFactor]
    ring
  apply tendsto_nonneg_weighted_comp_of_compact T w x y (Set.Icc (2 : ℝ) 4)
    currentChenUpsilon5OrdinaryFactor M currentChenUpsilon5OrdinaryIntegral
    isCompact_Icc continuousOn_currentChenUpsilon5OrdinaryFactor hM
    (Eventually.of_forall (fun N t ht => by dsimp [w]; positivity)) hmass
    ?_ ?_ hfixed
  · filter_upwards [eventually_currentChenUpsilon5_row_first_interval B,
      eventually_ge_atTop (2 : ℕ)] with N hrow hN
    intro t ht
    have hs := hrow t ht
    have hp := currentChenUpsilon5_profile_mem hN ht
    exact ⟨⟨by dsimp [x]; linarith [hs.1], by dsimp [x]; exact hs.2.le⟩,
      ⟨by dsimp [y]; linarith [hp.1], by dsimp [y]; linarith [hp.2]⟩⟩
  · intro delta hdelta
    exact eventually_currentChenUpsilon5_row_profile B delta hdelta

end

end ImbalancedChen
