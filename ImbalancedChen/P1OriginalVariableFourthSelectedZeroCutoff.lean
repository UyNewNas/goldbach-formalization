import ImbalancedChen.P1OriginalVariableFourthSmallRemainder
import ImbalancedChen.P1OriginalVariableFourthBoundedSourceLimit
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Zero-cutoff closure of the actual selected variable-fourth source

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The actual full selected tuple sum splits EXACTLY into the positive-cube
source and the literal small-coordinate source. The genuine bounded-cube
limit and uniform signed O(a) bound construct a Cauchy family of the actual
refined integrals. Completeness constructs their limit and the same tail
bound proves convergence of the full selected arithmetic source.

Only selected original cells occur. No claim that variable producer rows
vanish on the complementary original frontier, no full-policy identity,
and no untruncated-integral identification is made here.
-/

namespace ImbalancedChen.P1OriginalVariableFourthSelectedZeroCutoff

noncomputable section
open scoped Classical BigOperators
open Filter Topology Set
open HistoricalThirdCoarse P1OriginalCoarseContinuation
open P1OriginalCoarseFourthResidual P1OriginalFourthSmallPrimeStratification
open P1OriginalVariableFourthContinuation P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthSourceLimit
open P1OriginalVariableFourthBoundedSourceLimit
open P1OriginalVariableFourthSmallRemainder

abbrev evenTargets : Filter ℕ :=
  atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}

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

/-- Full actual contribution of a selected original mesh cell, before
discarding any small-coordinate tuples. -/
def fullCellSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) : ℝ :=
  ∑ p ∈ admitted e chi m omega N cap,
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
        literalTupleResidualDifference (rawLevel (e : ℝ) chi m omega (N : ℝ))
          (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p else 0)

def selectedFullSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4,
    fullCellSource e chi m omega j rows licensed N cap

def selectedPositiveSource (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4,
    positiveCellSource e chi m omega a j rows licensed N cap

def refinedSelectedIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4,
    refinedCellIntegral e m omega a j rows licensed

/-- Exact finite source partition. No sign or limiting assertion occurs. -/
theorem fullCellSource_eq_positive_add_small
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (j : FourthCell m) (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (N cap : ℕ) (hN : 1 < N) :
    fullCellSource e chi m omega j rows licensed N cap =
      positiveCellSource e chi m omega a j rows licensed N cap +
        smallCellSource e chi m omega a j rows licensed N cap := by
  rw [smallCellSource_eq_original_filter e chi m omega a j rows licensed N cap hN]
  unfold fullCellSource positiveCellSource
  change (∑ p ∈ admitted e chi m omega N cap, _) =
    (∑ p ∈ (admitted e chi m omega N cap).filter
      (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i), _) + _
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hpos : ∀ i, a ≤ actualPrimeTupleLog N p i
  · have hsmall : ¬ ∃ i, actualPrimeTupleLog N p i < a := by
      rintro ⟨i, hi⟩
      exact (not_lt_of_ge (hpos i)) hi
    by_cases hc : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
    · simp only [if_pos hpos, if_pos hc, hsmall, false_and, if_false, add_zero]
    · simp only [if_pos hpos, if_neg hc, mul_zero, hsmall, false_and, if_false, add_zero]
  · have hsmall : ∃ i, actualPrimeTupleLog N p i < a := by
      push_neg at hpos
      exact hpos
    by_cases hc : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
    · simp only [if_neg hpos, hsmall, hc, and_self, if_true, zero_add]
    · simp only [if_neg hpos, if_neg hc, mul_zero, hsmall, hc, and_false, if_false, zero_add]

theorem selectedFullSource_eq_positive_add_small
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (N cap : ℕ) (hN : 1 < N) :
    selectedFullSource e chi m omega J4 rows licensed N cap =
      selectedPositiveSource e chi m omega a J4 rows licensed N cap +
        selectedSmallSource e chi m omega a J4 rows licensed N cap := by
  unfold selectedFullSource selectedPositiveSource selectedSmallSource
  simp_rw [fullCellSource_eq_positive_add_small e chi m omega a _ rows licensed N cap hN]
  exact Finset.sum_add_distrib

/-- Two genuine positive-cube integrals differ by no more than the sum
of their true arithmetic tail payments. A ceil power cap supplies one
actual covering enumeration; its mean is not assumed. -/
theorem exists_refinedIntegral_difference_le
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) :
    ∃ D : ℝ, 0 < D ∧ ∀ a b : ℝ,
      0 < a → 2 * a ≤ omega → 0 < b → 2 * b ≤ omega →
      |refinedSelectedIntegral e chi m omega a J4 rows licensed -
        refinedSelectedIntegral e chi m omega b J4 rows licensed| ≤ D * (a + b) := by
  obtain ⟨D, hD, htail⟩ := exists_eventually_selectedSmallSource_abs_le_linear
    e chi m omega homega homegaRho J4
  refine ⟨D, hD, ?_⟩
  intro a b ha haomega hb hbomega
  letI : NeBot evenTargets := evenTargets_nonempty
  let cap : ℕ → ℕ := fun N => Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ))
  have hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ) :=
    Eventually.of_forall (fun N => Nat.le_ceil _)
  have hlim := (tendsto_selected_positive_source_refinedIntegral e chi m omega a
    ha (by linarith) J4 rows licensed cap hcap).sub
      (tendsto_selected_positive_source_refinedIntegral e chi m omega b
        hb (by linarith) J4 rows licensed cap hcap)
  have hbound : ∀ᶠ N : ℕ in evenTargets,
      |selectedPositiveSource e chi m omega a J4 rows licensed N (cap N) -
        selectedPositiveSource e chi m omega b J4 rows licensed N (cap N)| ≤ D * (a + b) := by
    filter_upwards [(htail a ha haomega).filter_mono inf_le_left,
      (htail b hb hbomega).filter_mono inf_le_left,
      (eventually_gt_atTop (1 : ℕ)).filter_mono
        (show evenTargets ≤ atTop from inf_le_left),
      (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
        (eventually_mem_principal _).filter_mono inf_le_right)] with N hNa hNb hN hEven
    have hea := selectedFullSource_eq_positive_add_small e chi m omega a J4 rows licensed N (cap N) hN
    have heb := selectedFullSource_eq_positive_add_small e chi m omega b J4 rows licensed N (cap N) hN
    have heq : selectedPositiveSource e chi m omega a J4 rows licensed N (cap N) -
        selectedPositiveSource e chi m omega b J4 rows licensed N (cap N) =
      selectedSmallSource e chi m omega b J4 rows licensed N (cap N) -
        selectedSmallSource e chi m omega a J4 rows licensed N (cap N) := by linarith
    rw [heq]
    exact (abs_sub _ _).trans (by
      have hA := hNa hEven.2 (cap N) rows licensed
      have hB := hNb hEven.2 (cap N) rows licensed
      linarith)
  exact le_of_tendsto hlim.abs hbound

/-- Completeness constructs the cutoff value from the actual selected
integrals. No desired limiting value or untruncated integral is an input. -/
theorem exists_refinedSelectedIntegral_zero_cutoff_limit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) :
    ∃ L : ℝ, Tendsto (fun a : ℝ => refinedSelectedIntegral e chi m omega a J4 rows licensed)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨D, hD, hbound⟩ := exists_refinedIntegral_difference_le
    e chi m omega homega homegaRho J4 rows licensed
  let I : ℝ → ℝ := fun a => refinedSelectedIntegral e chi m omega a J4 rows licensed
  apply cauchy_map_iff_exists_tendsto.1
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

/-- The complete selected actual tuple source has the constructed cutoff
limit for every adequate cap function. Rows outside selected cells are
deliberately not removed or assigned a full-policy interpretation. -/
theorem exists_selected_actual_source_and_zero_cutoff_limit
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) :
    ∃ L : ℝ,
      Tendsto (fun a : ℝ => refinedSelectedIntegral e chi m omega a J4 rows licensed)
        (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) ∧
      ∀ cap : ℕ → ℕ,
        (∀ᶠ N : ℕ in evenTargets,
          (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
        Tendsto (fun N : ℕ => selectedFullSource e chi m omega J4 rows licensed N (cap N))
          evenTargets (𝓝 L) := by
  obtain ⟨L, hI⟩ := exists_refinedSelectedIntegral_zero_cutoff_limit
    e chi m omega homega homegaRho J4 rows licensed
  obtain ⟨D, hD, htail⟩ := exists_eventually_selectedSmallSource_abs_le_linear
    e chi m omega homega homegaRho J4
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
  have hpositive := tendsto_selected_positive_source_refinedIntegral
    e chi m omega a ha0 (by linarith) J4 rows licensed cap hcap
  have hclose := Metric.tendsto_nhds.1 hpositive (epsilon / 3) hthird
  filter_upwards [(htail a ha0 haomega).filter_mono inf_le_left, hclose,
    (eventually_gt_atTop (1 : ℕ)).filter_mono
      (show evenTargets ≤ atTop from inf_le_left),
    (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (eventually_mem_principal _).filter_mono inf_le_right)] with N hrem hpos hN heN
  have hR := hrem heN.2 (cap N) rows licensed
  rw [Real.dist_eq] at hnear hpos ⊢
  have heq := selectedFullSource_eq_positive_add_small e chi m omega a
    J4 rows licensed N (cap N) hN
  have htri : |selectedFullSource e chi m omega J4 rows licensed N (cap N) - L| ≤
      |selectedPositiveSource e chi m omega a J4 rows licensed N (cap N) -
        refinedSelectedIntegral e chi m omega a J4 rows licensed| +
      |selectedSmallSource e chi m omega a J4 rows licensed N (cap N)| +
      |refinedSelectedIntegral e chi m omega a J4 rows licensed - L| := by
    rw [heq]
    calc
      _ = |(selectedPositiveSource e chi m omega a J4 rows licensed N (cap N) -
          refinedSelectedIntegral e chi m omega a J4 rows licensed) +
          selectedSmallSource e chi m omega a J4 rows licensed N (cap N) +
          (refinedSelectedIntegral e chi m omega a J4 rows licensed - L)| := by
        congr 1
        ring
      _ ≤ _ := (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
  change |selectedPositiveSource e chi m omega a J4 rows licensed N (cap N) -
    refinedSelectedIntegral e chi m omega a J4 rows licensed| < epsilon / 3 at hpos
  linarith

end
end ImbalancedChen.P1OriginalVariableFourthSelectedZeroCutoff
