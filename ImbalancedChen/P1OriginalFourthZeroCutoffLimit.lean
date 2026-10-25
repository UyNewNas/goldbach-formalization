import ImbalancedChen.P1OriginalFourthUniformSmallRemainder
import ImbalancedChen.P1OriginalFourthCutoffOrder
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# The original fourth zero-cutoff and complete arithmetic mean

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The limit is constructed from the original positive-cube integrals, not
assumed as a supplier. The actual signed small remainder gives a Cauchy
estimate between every two small cutoffs. Completeness of the reals then
gives their limit, and the same genuine tail estimate proves convergence
of the full original arithmetic policy saving to that value.

Identification with a separately defined untruncated Lebesgue integral
is not asserted. All prime carriers, original first stops, d=1 and empty
initial history, original raw Gamma and checked fourth caps are retained.
-/

namespace ImbalancedChen.P1OriginalFourthZeroCutoffLimit
noncomputable section
open scoped Classical BigOperators
open Filter Topology Set
open P1OriginalCoarseContinuation P1OriginalFourthIntegral
open P1OriginalFourthUniformSmallRemainder

private theorem evenTargets_nonempty : NeBot evenTargets := by
  have hd : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have he : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop
      (Filter.principal {N : ℕ | 0 < N ∧ Even N}) := by
    apply tendsto_principal.2
    exact Eventually.of_forall (fun n => ⟨by omega, ⟨n + 1, by omega⟩⟩)
  exact (tendsto_inf.2 ⟨hd, he⟩).neBot

/-- One genuine constant controls the difference between every pair of
original positive-cube integrals. The arithmetic source is eliminated
using its exact original remainder-increment limit. -/
theorem exists_original_cutoff_difference_le
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∃ D : ℝ, 0 < D ∧ ∀ a b : ℝ,
      0 < a → 2 * a ≤ omega → 0 < b → 2 * b ≤ omega →
      |selectedIntegral e chi m omega a J4 cap4 -
          selectedIntegral e chi m omega b J4 cap4| ≤ D * (a + b) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_eventually_original_smallRemainder_abs_le_linear
      e chi m omega homega homegaRho J4 cap4 hcheck
  refine ⟨D, hD, ?_⟩
  intro a b ha haomega hb hbomega
  letI : NeBot evenTargets := evenTargets_nonempty
  let cap : ℕ → ℕ := fun N => Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))
  have hc : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ) :=
    Eventually.of_forall (fun N => Nat.le_ceil _)
  have hlim := P1OriginalFourthCutoffOrder.tendsto_original_remainder_cutoff_increment
    e chi m omega a b ha (by linarith) hb (by linarith)
      J4 cap4 hcheck cap hc
  have hev : ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N :=
    (eventually_mem_principal _).filter_mono inf_le_right
  have hpair : ∀ᶠ N : ℕ in evenTargets,
      |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N) -
          P1OriginalFourthLimit.smallRemainder e chi m omega b J4 cap4 N (cap N)| ≤
        D * (a + b) := by
    filter_upwards [(hbound a ha haomega).filter_mono inf_le_left,
      (hbound b hb hbomega).filter_mono inf_le_left, hev] with N hNa hNb heN
    exact (abs_sub _ _).trans (by
      have hA := hNa heN.2 (cap N)
      have hB := hNb heN.2 (cap N)
      linarith)
  have h := le_of_tendsto hlim.abs hpair
  simpa only [abs_sub_comm] using h

/-- The original selected integrals are a Cauchy family at zero from the
right. This statement has no mean-value or boundedness supplier. -/
theorem cauchy_original_selectedIntegral_at_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    Cauchy (Filter.map (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4)
      (𝓝[Ioi 0] (0 : ℝ))) := by
  obtain ⟨D, hD, hbound⟩ := exists_original_cutoff_difference_le
    e chi m omega homega homegaRho J4 cap4 hcheck
  let I : ℝ → ℝ := fun a => selectedIntegral e chi m omega a J4 cap4
  apply Metric.cauchy_iff.2
  refine ⟨inferInstance, ?_⟩
  intro epsilon hepsilon
  let delta := min (omega / 2) (epsilon / (2 * D))
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  refine ⟨I '' Ioo 0 delta, ?_, ?_⟩
  · apply Filter.mem_map.2
    filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds hdelta).filter_mono nhdsWithin_le_nhds] with a ha haD
    exact ⟨a, ⟨ha, haD⟩, rfl⟩
  · intro x hx y hy
    obtain ⟨a, ⟨ha, hadelta⟩, rfl⟩ := hx
    obtain ⟨b, ⟨hb, hbdelta⟩, rfl⟩ := hy
    have haomega : 2 * a ≤ omega := by
      have := hadelta.trans_le (min_le_left _ _)
      dsimp only [delta] at this
      linarith
    have hbomega : 2 * b ≤ omega := by
      have := hbdelta.trans_le (min_le_left _ _)
      dsimp only [delta] at this
      linarith
    have had : a < epsilon / (2 * D) := hadelta.trans_le (min_le_right _ _)
    have hbd : b < epsilon / (2 * D) := hbdelta.trans_le (min_le_right _ _)
    have hA := (lt_div_iff₀ (show 0 < 2 * D by positivity)).mp had
    have hB := (lt_div_iff₀ (show 0 < 2 * D by positivity)).mp hbd
    have hp : D * (a + b) < epsilon := by nlinarith
    rw [Real.dist_eq]
    exact (hbound a b ha haomega hb hbomega).trans_lt hp

/-- Completeness constructs the original zero-cutoff integral value. -/
theorem exists_original_selectedIntegral_zero_cutoff_limit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∃ L : ℝ, Tendsto (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) := by
  exact cauchy_map_iff_exists_tendsto.1
    (cauchy_original_selectedIntegral_at_zero
      e chi m omega homega homegaRho J4 cap4 hcheck)

/-- The full original arithmetic saving, normalized exactly as in the
positive-cube dictionary. -/
def normalizedActualSaving (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) (N cap : ℕ) : ℝ :=
  actualHistoricalFourthSaving
      (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
      (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
      (level4 e chi m omega J4 cap4 (N : ℝ))
      N cap ((N : ℝ) ^ (19 / 96 : ℝ)) * Real.log (N : ℝ) / singularSeries N

/-- The same constructed limit is the mean of the complete actual source.
Only the geometric finite h34Check and the genuine enumeration coverage
are premises; no limiting target or small-remainder supplier is assumed. -/
theorem exists_original_fourth_actual_mean_and_cutoff_limit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∃ L : ℝ,
      Tendsto (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4)
        (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) ∧
      ∀ cap : ℕ → ℕ,
        (∀ᶠ N : ℕ in evenTargets,
          (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
        Tendsto (fun N : ℕ => normalizedActualSaving e chi m omega J4 cap4 N (cap N))
          evenTargets (𝓝 L) := by
  obtain ⟨L, hI⟩ := exists_original_selectedIntegral_zero_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 hcheck
  obtain ⟨D, hD, hbound⟩ :=
    exists_eventually_original_smallRemainder_abs_le_linear
      e chi m omega homega homegaRho J4 cap4 hcheck
  refine ⟨L, hI, ?_⟩
  intro cap hcap
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have hthird : 0 < epsilon / 3 := by positivity
  have hcut : 0 < min (omega / 2) (epsilon / (3 * D)) :=
    lt_min (by positivity) (by positivity)
  obtain ⟨a, ha, hsmall, hnear⟩ :=
    (self_mem_nhdsWithin.and
      (((Iio_mem_nhds hcut).filter_mono nhdsWithin_le_nhds).and
        (Metric.tendsto_nhds.1 hI (epsilon / 3) hthird))).exists
  have ha0 : 0 < a := ha
  have haomega : 2 * a ≤ omega := by
    have := hsmall.trans_le (min_le_left _ _)
    linarith
  have hDa : D * a < epsilon / 3 := by
    have h := hsmall.trans_le (min_le_right _ _)
    have := (lt_div_iff₀ (show 0 < 3 * D by positivity)).mp h
    nlinarith
  have hpos := P1OriginalFourthLimit.tendsto_actualSaving_sub_smallRemainder
    e chi m omega a ha0 (by linarith) J4 cap4 hcheck cap hcap
  have hclose := Metric.tendsto_nhds.1 hpos (epsilon / 3) hthird
  have hev : ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N :=
    (eventually_mem_principal _).filter_mono inf_le_right
  filter_upwards [(hbound a ha0 haomega).filter_mono inf_le_left, hclose, hev]
    with N hrem hposN heN
  have hR := hrem heN.2 (cap N)
  rw [Real.dist_eq] at hnear hposN ⊢
  have htri : |normalizedActualSaving e chi m omega J4 cap4 N (cap N) - L| ≤
      |normalizedActualSaving e chi m omega J4 cap4 N (cap N) -
          P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N) -
            selectedIntegral e chi m omega a J4 cap4| +
        |P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)| +
        |selectedIntegral e chi m omega a J4 cap4 - L| := by
    calc
      _ = |((normalizedActualSaving e chi m omega J4 cap4 N (cap N) -
          P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N)) -
          selectedIntegral e chi m omega a J4 cap4) +
          P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N) +
          (selectedIntegral e chi m omega a J4 cap4 - L)| := by
        congr 1
        ring
      _ ≤ _ := (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
  change |normalizedActualSaving e chi m omega J4 cap4 N (cap N) -
      P1OriginalFourthLimit.smallRemainder e chi m omega a J4 cap4 N (cap N) -
      selectedIntegral e chi m omega a J4 cap4| < epsilon / 3 at hposN
  linarith

/-- The original retained polynomial difference starts at d=1 with empty
history. Its complete normalized saving has the constructed cutoff limit. -/
theorem exists_original_fourth_policy_mean_and_cutoff_limit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    ∃ L : ℝ,
      Tendsto (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4)
        (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) ∧
      ∀ cap : ℕ → ℕ,
        (∀ᶠ N : ℕ in evenTargets,
          (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
        Tendsto (fun N : ℕ =>
          (firstExitRetainedPolynomial
              (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
              (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
              (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ))) -
            firstExitRetainedPolynomial
              (fourthCappedUpperPolicy
                (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
                (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
                (level4 e chi m omega J4 cap4 (N : ℝ)))
              (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
              (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
            Real.log (N : ℝ) / singularSeries N)
          evenTargets (𝓝 L) := by
  obtain ⟨L, hI, hmean⟩ := exists_original_fourth_actual_mean_and_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 hcheck
  refine ⟨L, hI, ?_⟩
  intro cap hcap
  apply (hmean cap hcap).congr'
  filter_upwards [(eventually_gt_atTop (1 : ℕ)).filter_mono
    (show evenTargets ≤ atTop from inf_le_left)] with N hN
  rw [P1OriginalFourthLimit.originalPolicySaving_eq e chi m omega J4 cap4 hcheck
    N (cap N) hN]
  rfl

end
end ImbalancedChen.P1OriginalFourthZeroCutoffLimit
