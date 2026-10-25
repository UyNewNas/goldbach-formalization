import ImbalancedChen.P1ActualVariableFifthGlobalPositiveLimit
import ImbalancedChen.P1ActualVariableFifthUniformTail
import ImbalancedChen.P1ActualVariableFifthUntruncatedDomination
import ImbalancedChen.P1OriginalVariableFourthFullSourceMean
import ImbalancedChen.P1OriginalFourthFifthTotalTupleSource

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The full ACTUAL finite-max fifth mean. Every cell, tail and full-integral
supplier is concrete proved source, with no desired mean, tail, integrability
or numerical certificate as input. Original firstStop/raw-Q3, all overlap
rows and d=1 remain. No generic-D, stored-old5 or all15 substitution. -/

namespace ImbalancedChen.P1ActualVariableFifthFullMean
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation P1OriginalVariableFifthContinuation
open P1ActualVariableFifthGlobalSourceAssembly
open P1ActualVariableFifthUntruncatedDomination P1OriginalFifthMovingScaleLimit
open P1CorrectedFifthDensityDictionary

theorem tendsto_normalizedSaving_fullSelectedIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedSaving e chi m omega rows4 licensed4 J5 rows5 N (cap N))
      evenTargets (𝓝 (fullSelectedIntegral e chi m omega rows4 licensed4 J5 rows5)) := by
  let F (N : ℕ) := normalizedSaving e chi m omega rows4 licensed4 J5 rows5 N (cap N)
  let I (a : ℝ) := selectedIntegral e chi m omega rows4 licensed4 J5 rows5 a
  let L := fullSelectedIntegral e chi m omega rows4 licensed4 J5 rows5
  have hI : Tendsto I (𝓝[Ioi 0] (0 : ℝ)) (𝓝 L) :=
    tendsto_selectedCellIntegral_fullSelectedIntegral
      e he chi m omega homega homegaRho rows4 licensed4 J5 rows5
  obtain ⟨D, hD, htail⟩ :=
    P1ActualVariableFifthUniformTail.exists_eventually_actual_smallRemainder_abs_le_linear
      e chi m omega rows4 licensed4 J5 rows5 homega homegaRho
  change Tendsto F evenTargets (𝓝 L)
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have hthird : 0 < epsilon / 3 := by positivity
  have hcut : 0 < min (omega / 6) (min (19 / 96 : ℝ) (epsilon / (3 * D))) :=
    lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  obtain ⟨a, ha, hsmall, hnear⟩ :=
    (self_mem_nhdsWithin.and
      (((Iio_mem_nhds hcut).filter_mono nhdsWithin_le_nhds).and
        (Metric.tendsto_nhds.1 hI (epsilon / 3) hthird))).exists
  have ha0 : 0 < a := ha
  have haomega : a ≤ omega / 6 := (hsmall.trans_le (min_le_left _ _)).le
  have haRho : a < (19 / 96 : ℝ) :=
    (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hDa : D * a < epsilon / 3 := by
    have h := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have hh := (lt_div_iff₀ (show 0 < 3 * D by positivity)).mp h
    nlinarith
  have hpositive : Tendsto
      (fun N : ℕ => positiveCharge e chi m omega rows4 licensed4 J5 rows5 a N (cap N))
      evenTargets (𝓝 (I a)) :=
    tendsto_positiveCharge_selectedIntegral
      e chi m omega rows4 licensed4 J5 rows5 a ha0 haRho cap hcap
  filter_upwards [htail a ha0 (le_min haRho.le haomega) cap hcap,
    Metric.tendsto_nhds.1 hpositive (epsilon / 3) hthird] with N hrem hpos
  have heq := normalizedSaving_eq_positive_add_smallRemainder
    e chi m omega rows4 licensed4 J5 rows5 a N (cap N)
  change F N = positiveCharge e chi m omega rows4 licensed4 J5 rows5 a N (cap N) +
    smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N (cap N) at heq
  rw [Real.dist_eq] at hnear hpos ⊢
  have htri : |F N - L| ≤
      |positiveCharge e chi m omega rows4 licensed4 J5 rows5 a N (cap N) - I a| +
      |smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N (cap N)| + |I a - L| := by
    rw [heq]
    calc
      _ = |(positiveCharge e chi m omega rows4 licensed4 J5 rows5 a N (cap N) - I a) +
          smallRemainder e chi m omega rows4 licensed4 J5 rows5 a N (cap N) + (I a - L)| := by
        congr 1
        ring
      _ ≤ _ := (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
  linarith

theorem tendsto_retainedFourth_sub_variableFifth_fullIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (originalFourthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) rows4 licensed4 -
        variableFifthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
          rows4 licensed4 J5 rows5) * Real.log (N : ℝ) / singularSeries N)
      evenTargets (𝓝 (fullSelectedIntegral e chi m omega rows4 licensed4 J5 rows5)) := by
  apply (tendsto_normalizedSaving_fullSelectedIntegral
    e he chi m omega homega homegaRho rows4 licensed4 J5 rows5 cap hcap).congr'
  filter_upwards [(eventually_gt_atTop (1 : ℕ)).filter_mono
    (show evenTargets ≤ atTop from inf_le_left)] with N hN
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast hN
  simp only [normalizedSaving, variable_fifth_finite_density_identity
    e chi m omega N (cap N) hNreal ((N : ℝ) ^ (19 / 96 : ℝ)) rows4 licensed4 J5 rows5]

/-- The two true original corrections add; the identical actual fourth
retained polynomial cancels. Empty-history terms remain in both trees. -/
theorem tendsto_originalThird_sub_variableFifth_totalIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (P1OriginalFourthFifthTotalTupleSource.originalThirdRetained
          e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) -
        variableFifthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
          rows4 licensed4 J5 rows5) * Real.log (N : ℝ) / singularSeries N)
      evenTargets (𝓝 (P1OriginalVariableFourthFullActiveIntegral.fullActiveIntegral
        e chi m omega rows4 licensed4 + fullSelectedIntegral e chi m omega rows4 licensed4 J5 rows5)) := by
  have h4 :=
    P1OriginalVariableFourthFullSourceMean.tendsto_normalizedOriginalPolicyDifference_fullActiveIntegral
      e he chi m omega homega homegaRho hmesh rows4 licensed4 cap hcap
  have h5 := tendsto_retainedFourth_sub_variableFifth_fullIntegral
    e he chi m omega homega homegaRho rows4 licensed4 J5 rows5 cap hcap
  apply (h4.add h5).congr'
  apply Eventually.of_forall
  intro N
  change
    ((P1OriginalFourthFifthTotalTupleSource.originalThirdRetained
          e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) -
        originalFourthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) rows4 licensed4) *
        Real.log (N : ℝ) / singularSeries N +
      (originalFourthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) rows4 licensed4 -
        variableFifthRetained e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
          rows4 licensed4 J5 rows5) * Real.log (N : ℝ) / singularSeries N) = _
  ring

end
end ImbalancedChen.P1ActualVariableFifthFullMean
