import ImbalancedChen.P1OriginalVariableFourthFullSourceAssembly
import ImbalancedChen.P1OriginalVariableFourthFullSmallRemainder
import ImbalancedChen.P1OriginalVariableFourthFullActiveIntegral

/-!
The FULL actual original variable-fourth source mean.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

All suppliers are concrete same-source theorems: exact full finite source
partition, genuine positive-cube arithmetic mean, actual full O(a) signed
tail, and the integrable full active-branch cutoff limit. The epsilon/3
argument removes the positive cutoff. No target mean or tail is a premise.
The original rawQ3, firstStop, current cube and every overlapping producer
row remain in the original retained-polynomial difference.
-/

namespace ImbalancedChen.P1OriginalVariableFourthFullSourceMean
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthSourceCoefficient
open P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthFullActivePositiveLimit
open P1OriginalVariableFourthFullSourceAssembly
open P1OriginalVariableFourthFullSmallRemainder
open P1OriginalVariableFourthFullActiveIntegral

abbrev evenTargets : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}

/-- Full actual original variable-fourth normalized saving converges to the
explicit untruncated actual active-source integral. No selected J4 support,
whole-active cell, fixed eligibility, global continuity or analytic target
mean is assumed. The fine mesh hypothesis is explicit. -/
theorem tendsto_normalizedActualSaving_fullActiveIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFourthSaving (initialPolicy (e : ℝ) m (N : ℝ))
          (rawLevel (e : ℝ) chi m omega (N : ℝ))
          (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed)
          N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) * Real.log (N : ℝ) / singularSeries N)
      evenTargets (𝓝 (fullActiveIntegral e chi m omega rows licensed)) := by
  let F (N : ℕ) := actualHistoricalFourthSaving (initialPolicy (e : ℝ) m (N : ℝ))
      (rawLevel (e : ℝ) chi m omega (N : ℝ))
      (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed)
      N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) * Real.log (N : ℝ) / singularSeries N
  let I (a : ℝ) := ∑ label ∈ activeAdoptedLabels (e : ℝ) chi m,
    refinedBranchIntegral (e : ℝ) chi m omega a rows licensed label
  let L := fullActiveIntegral e chi m omega rows licensed
  have hI : Tendsto I (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) := by
    simpa only [I, L, refinedBranchIntegral] using
      tendsto_activeRefinedSum_fullActiveIntegral e he chi m omega homega homegaRho hmesh rows licensed
  obtain ⟨D, hD, htail⟩ := exists_eventually_fullSmallSource_abs_le_linear
    e chi m omega homega homegaRho hmesh
  change Tendsto F evenTargets (𝓝 L)
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have hthird : 0 < epsilon / 3 := by positivity
  have hcut : 0 < min (omega / 4) (epsilon / (3 * D)) := lt_min (by positivity) (by positivity)
  obtain ⟨a, ha, hsmall, hnear⟩ :=
    (self_mem_nhdsWithin.and
      (((Iio_mem_nhds hcut).filter_mono nhdsWithin_le_nhds).and
        (Metric.tendsto_nhds.1 hI (epsilon / 3) hthird))).exists
  have ha0 : 0 < a := ha
  have haomega : 4 * a ≤ omega := by
    have := hsmall.trans_le (min_le_left _ _)
    linarith
  have haRho : a < (19 / 96 : ℝ) := by
    have := hsmall.trans_le (min_le_left _ _)
    linarith
  have hDa : D * a < epsilon / 3 := by
    have h := hsmall.trans_le (min_le_right _ _)
    have := (lt_div_iff₀ (show 0 < 3 * D by positivity)).mp h
    nlinarith
  have hpositive : Tendsto (fun N : ℕ => fullPositiveSource e chi m omega a rows licensed N (cap N))
      evenTargets (𝓝 (I a)) := by
    simpa only [fullPositiveSource, I] using
      tendsto_full_positive_original_correction (e : ℝ) chi m omega a ha0 haRho rows licensed cap hcap
  have hclose := Metric.tendsto_nhds.1 hpositive (epsilon / 3) hthird
  filter_upwards [(htail a ha0 haomega).filter_mono inf_le_left, hclose,
    (eventually_gt_atTop (1 : ℕ)).filter_mono (show evenTargets ≤ atTop from inf_le_left),
    (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (eventually_mem_principal _).filter_mono inf_le_right), hcap]
      with N hrem hpos hN heN hc
  have hR := hrem heN.2 (cap N) rows licensed
  have heq := actualSaving_normalized_eq_positive_add_fullSmall
    e chi m omega a N (cap N) hN hc rows licensed
  change F N = fullPositiveSource e chi m omega a rows licensed N (cap N) +
    fullSmallSource e chi m omega a rows licensed N (cap N) at heq
  rw [Real.dist_eq] at hnear hpos ⊢
  have htri : |F N - L| ≤
      |fullPositiveSource e chi m omega a rows licensed N (cap N) - I a| +
      |fullSmallSource e chi m omega a rows licensed N (cap N)| + |I a - L| := by
    rw [heq]
    calc
      _ = |(fullPositiveSource e chi m omega a rows licensed N (cap N) - I a) +
          fullSmallSource e chi m omega a rows licensed N (cap N) + (I a - L)| := by
        congr 1
        ring
      _ ≤ _ := (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
  change |fullPositiveSource e chi m omega a rows licensed N (cap N) - I a| < epsilon / 3 at hpos
  linarith

/-- The same genuine mean is the literal originalT3-minus-producerQ4
retained-polynomial difference, with d=1 and empty history kept in both. -/
theorem tendsto_normalizedOriginalPolicyDifference_fullActiveIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ))) -
        firstExitRetainedPolynomial (producerPolicy4 (e : ℝ) chi m omega (N : ℝ) rows licensed)
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
          Real.log (N : ℝ) / singularSeries N)
      evenTargets (𝓝 (fullActiveIntegral e chi m omega rows licensed)) := by
  apply (tendsto_normalizedActualSaving_fullActiveIntegral
    e he chi m omega homega homegaRho hmesh rows licensed cap hcap).congr'
  filter_upwards [(eventually_gt_atTop (1 : ℕ)).filter_mono
    (show evenTargets ≤ atTop from inf_le_left)] with N hN
  rw [original_policy_difference_eq_fourth_saving (e : ℝ) chi m omega N (cap N)
    ((N : ℝ) ^ (19 / 96 : ℝ)) rows licensed (by exact_mod_cast (show 1 ≤ N by omega))]

end
end ImbalancedChen.P1OriginalVariableFourthFullSourceMean
