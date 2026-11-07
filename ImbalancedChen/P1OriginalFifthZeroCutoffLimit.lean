import ImbalancedChen.P1OriginalFifthUniformSmallRemainder
import Mathlib.Topology.MetricSpace.Cauchy

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual uniform arithmetic tail constructs the zero-cutoff limit of the
SAME coarse original fifth selected integrals by completeness of the reals.
The full actual saving then converges to that constructed value. No mean
or zero-cutoff integral is supplied as an assumption. The corrected variable
old-parent dictionary remains distinct.
-/

namespace ImbalancedChen.P1OriginalFifthZeroCutoffLimit
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation P1OriginalFifthIntegral
open P1OriginalFifthMovingScaleLimit P1OriginalFifthUniformSmallRemainder

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

def normalizedActualSaving (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) : ℝ :=
  actualHistoricalFifthSaving
    (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
    (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
    (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ))
    (level5 e chi m omega J4 cap4 J5 cap5 (N : ℝ))
    N cap ((N : ℝ) ^ (19 / 96 : ℝ)) * Real.log (N : ℝ) / singularSeries N

theorem exists_cutoff_difference_le
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    ∃ D : ℝ, 0 < D ∧ ∀ a b : ℝ,
      0 < a → a < min (19 / 96 : ℝ) (omega / 6) →
      0 < b → b < min (19 / 96 : ℝ) (omega / 6) →
      |selectedIntegral e chi m omega a J4 cap4 J5 cap5 -
        selectedIntegral e chi m omega b J4 cap4 J5 cap5| ≤ D * (a + b) := by
  obtain ⟨D, hD, hbound⟩ := exists_eventually_smallRemainder_abs_le_linear
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  refine ⟨D, hD, ?_⟩
  intro a b ha hamax hb hbmax
  letI : NeBot evenTargets := evenTargets_nonempty
  let cap : ℕ → ℕ := fun N => Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))
  have hc : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ) :=
    Eventually.of_forall (fun N => Nat.le_ceil _)
  have hla := P1OriginalFifthLimit.tendsto_actualSaving_sub_smallRemainder
    e chi m omega a ha (hamax.trans_le (min_le_left _ _)) J4 cap4 J5 cap5 cap hc
  have hlb := P1OriginalFifthLimit.tendsto_actualSaving_sub_smallRemainder
    e chi m omega b hb (hbmax.trans_le (min_le_left _ _)) J4 cap4 J5 cap5 cap hc
  have hlim : Tendsto (fun N : ℕ =>
      P1OriginalFifthLimit.smallRemainder e chi m omega b J4 cap4 J5 cap5 N (cap N) -
      P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N))
      evenTargets (𝓝 (selectedIntegral e chi m omega a J4 cap4 J5 cap5 -
        selectedIntegral e chi m omega b J4 cap4 J5 cap5)) := by
    convert hla.sub hlb using 1
    funext N
    ring
  have hpair : ∀ᶠ N : ℕ in evenTargets,
      |P1OriginalFifthLimit.smallRemainder e chi m omega b J4 cap4 J5 cap5 N (cap N) -
        P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)| ≤
        D * (a + b) := by
    filter_upwards [hbound a ha hamax.le cap hc, hbound b hb hbmax.le cap hc]
      with N hA hB
    exact (abs_sub _ _).trans (by linarith)
  exact le_of_tendsto hlim.abs hpair

theorem cauchy_selectedIntegral_at_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    Cauchy (Filter.map (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4 J5 cap5)
      (𝓝[Ioi 0] (0 : ℝ))) := by
  obtain ⟨D, hD, hbound⟩ := exists_cutoff_difference_le
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  let I : ℝ → ℝ := fun a => selectedIntegral e chi m omega a J4 cap4 J5 cap5
  let mu : ℝ := min (19 / 96 : ℝ) (omega / 6)
  have hmu : 0 < mu := lt_min (by norm_num) (by positivity)
  apply Metric.cauchy_iff.2
  refine ⟨inferInstance, ?_⟩
  intro epsilon hepsilon
  let delta := min mu (epsilon / (2 * D))
  have hdelta : 0 < delta := lt_min hmu (by positivity)
  refine ⟨I '' Ioo 0 delta, ?_, ?_⟩
  · apply Filter.mem_map.2
    filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds hdelta).filter_mono nhdsWithin_le_nhds] with a ha haD
    exact ⟨a, ⟨ha, haD⟩, rfl⟩
  · intro x hx y hy
    obtain ⟨a, ⟨ha, had⟩, rfl⟩ := hx
    obtain ⟨b, ⟨hb, hbd⟩, rfl⟩ := hy
    have hamu : a < mu := had.trans_le (min_le_left _ _)
    have hbmu : b < mu := hbd.trans_le (min_le_left _ _)
    have hA := (lt_div_iff₀ (show 0 < 2 * D by positivity)).mp
      (had.trans_le (min_le_right _ _))
    have hB := (lt_div_iff₀ (show 0 < 2 * D by positivity)).mp
      (hbd.trans_le (min_le_right _ _))
    rw [Real.dist_eq]
    exact (hbound a b ha hamu hb hbmu).trans_lt (by nlinarith)

theorem exists_selectedIntegral_zero_cutoff_limit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    ∃ L : ℝ, Tendsto (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4 J5 cap5)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) :=
  cauchy_map_iff_exists_tendsto.1 (cauchy_selectedIntegral_at_zero
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45)

theorem exists_actual_mean_and_cutoff_limit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    ∃ L : ℝ,
      Tendsto (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4 J5 cap5)
        (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) ∧
      ∀ cap : ℕ → ℕ,
        (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
        Tendsto (fun N : ℕ => normalizedActualSaving e chi m omega J4 cap4 J5 cap5 N (cap N))
          evenTargets (𝓝 L) := by
  obtain ⟨L, hI⟩ := exists_selectedIntegral_zero_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  obtain ⟨D, hD, hbound⟩ := exists_eventually_smallRemainder_abs_le_linear
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  refine ⟨L, hI, ?_⟩
  intro cap hcap
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  let mu : ℝ := min (19 / 96 : ℝ) (omega / 6)
  have hmu : 0 < mu := lt_min (by norm_num) (by positivity)
  have hthird : 0 < epsilon / 3 := by positivity
  have hcut : 0 < min mu (epsilon / (3 * D)) := lt_min hmu (by positivity)
  obtain ⟨a, ha, hsmall, hnear⟩ :=
    (self_mem_nhdsWithin.and
      (((Iio_mem_nhds hcut).filter_mono nhdsWithin_le_nhds).and
        (Metric.tendsto_nhds.1 hI (epsilon / 3) hthird))).exists
  have ha0 : 0 < a := ha
  have hamu : a < mu := hsmall.trans_le (min_le_left _ _)
  have hDa : D * a < epsilon / 3 := by
    have hh := (lt_div_iff₀ (show 0 < 3 * D by positivity)).mp
      (hsmall.trans_le (min_le_right _ _))
    nlinarith
  have hpos := P1OriginalFifthLimit.tendsto_actualSaving_sub_smallRemainder
    e chi m omega a ha0 (hamu.trans_le (min_le_left _ _)) J4 cap4 J5 cap5 cap hcap
  have hclose := Metric.tendsto_nhds.1 hpos (epsilon / 3) hthird
  filter_upwards [hbound a ha0 hamu.le cap hcap, hclose] with N hR hposN
  rw [Real.dist_eq] at hnear hposN ⊢
  change |normalizedActualSaving e chi m omega J4 cap4 J5 cap5 N (cap N) -
    P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N) -
    selectedIntegral e chi m omega a J4 cap4 J5 cap5| < epsilon / 3 at hposN
  have htri : |normalizedActualSaving e chi m omega J4 cap4 J5 cap5 N (cap N) - L| ≤
      |normalizedActualSaving e chi m omega J4 cap4 J5 cap5 N (cap N) -
        P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N) -
        selectedIntegral e chi m omega a J4 cap4 J5 cap5| +
      |P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)| +
      |selectedIntegral e chi m omega a J4 cap4 J5 cap5 - L| := by
    calc
      _ = |((normalizedActualSaving e chi m omega J4 cap4 J5 cap5 N (cap N) -
          P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N)) -
          selectedIntegral e chi m omega a J4 cap4 J5 cap5) +
          P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N (cap N) +
          (selectedIntegral e chi m omega a J4 cap4 J5 cap5 - L)| := by congr 1; ring
      _ ≤ _ := (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
  linarith

end
end ImbalancedChen.P1OriginalFifthZeroCutoffLimit
