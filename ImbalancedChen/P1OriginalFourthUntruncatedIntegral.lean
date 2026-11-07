import ImbalancedChen.P1OriginalFourthZeroCutoffLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The untruncated integral on the original positive fourth source

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

The full source is the positive-coordinate part of the ORIGINAL joint
firstStop/raw-Q3 region. Its exact old-minus-new raw PLUS kernel is proved
integrable, using the already constructed bounded positive-cutoff integrals.
The resulting full Lebesgue integral is identified with the constructed
zero-cutoff value and with the full original arithmetic saving mean.
No generic historical-prefix fullIntegral or integrability supplier occurs.
-/

namespace ImbalancedChen.P1OriginalFourthUntruncatedIntegral
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Filter Topology Set
open P1OriginalCoarseContinuation P1OriginalFourthIntegral
open P1FourthFullCellIntegral P1OriginalFourthCutoffOrder
open P1OriginalFourthZeroCutoffLimit P1OriginalFourthUniformSmallRemainder

abbrev Tuple := Fin 4 → ℝ

/-- Literal original joint region, with every logarithmic prime coordinate
positive and the original outer cutoff 19/96. -/
def fullCell (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m) : Set Tuple :=
  {t | ∀ i, 0 < t i} ∩
    (logPrimeBox (fun _ : Fin 4 => 0) (fun _ => (19 / 96 : ℝ)) ∩
      P1OriginalFourthLimit.sourceRegion e m omega j)

def extendedKernel (e : ℚ) (m : ℕ) (cap4 : FourthCell m → ℚ)
    (j : FourthCell m) (t : Tuple) : ℝ :=
  (extendedProfile (oldExponent e m j) t - extendedProfile (cap4 j : ℝ) t) *
    reciprocalWeight t

/-- Exact original Gamma-minus-checked-Q4 kernel at the same terminal
coordinate, including the full reciprocal-prime logarithmic Jacobian. -/
def rawKernel (e : ℚ) (m : ℕ) (cap4 : FourthCell m → ℚ)
    (j : FourthCell m) (t : Tuple) : ℝ :=
  (fourthPlusProfileP1 (oldExponent e m j) t -
    fourthPlusProfileP1 (cap4 j : ℝ) t) * ∏ i, 1 / t i

def fullCellIntegral (e : ℚ) (m : ℕ) (omega : ℝ)
    (cap4 : FourthCell m → ℚ) (j : FourthCell m) : ℝ :=
  ∫ t in fullCell e m omega j, rawKernel e m cap4 j t

def fullSelectedIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) : ℝ :=
  ∑ j ∈ selectedFourthCells e chi m omega J4, fullCellIntegral e m omega cap4 j

def cutoff (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_tendsto_zero : Tendsto cutoff atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem cutoff_tendsto_right : Tendsto cutoff atTop (𝓝[Ioi 0] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.2 ⟨cutoff_tendsto_zero,
    Eventually.of_forall cutoff_pos⟩

theorem fullCell_measurable (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m) :
    MeasurableSet (fullCell e m omega j) := by
  have hp : MeasurableSet {t : Tuple | ∀ i, 0 < t i} := by
    have heq : {t : Tuple | ∀ i, 0 < t i} =
        ⋂ i : Fin 4, {t : Tuple | 0 < t i} := by
      ext t
      simp only [mem_iInter, mem_setOf_eq]
    rw [heq]
    exact MeasurableSet.iInter (fun i =>
      measurableSet_lt measurable_const (measurable_pi_apply i))
  apply hp.inter
  apply (measurableSet_logPrimeBox _ _).inter
  exact (HistoricalThirdCoarse.P1OriginalFourth.jointCell_measurable _ _ _ _).inter
    (HistoricalThirdCoarse.P1OriginalFourth.jointRegion_measurable _ _ _ _)

theorem truncatedCell_subset_fullCell (e : ℚ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : FourthCell m) :
    truncatedCell e m omega a j ⊆ fullCell e m omega j := by
  intro t ht
  refine ⟨fun i => ha.trans_le (mem_logPrimeBox.mp ht.1 i).1, ?_, ht.2⟩
  exact mem_logPrimeBox.mpr (fun i =>
    ⟨(ha.trans_le (mem_logPrimeBox.mp ht.1 i).1).le, (mem_logPrimeBox.mp ht.1 i).2⟩)

theorem eventually_mem_truncatedCell (e : ℚ) (m : ℕ) (omega : ℝ)
    (j : FourthCell m) {t : Tuple} (ht : t ∈ fullCell e m omega j) :
    ∀ᶠ n : ℕ in atTop, t ∈ truncatedCell e m omega (cutoff n) j := by
  have hc : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 4, cutoff n < t i :=
    eventually_all.2 (fun i => cutoff_tendsto_zero.eventually (gt_mem_nhds (ht.1 i)))
  filter_upwards [hc] with n hn
  exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(hn i).le, (mem_logPrimeBox.mp ht.2.1 i).2⟩),
    ht.2.2⟩

/-- Every positive original source tuple belongs to a positive-cutoff cell. -/
theorem fullCell_eq_iUnion_truncatedCell
    (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m) :
    fullCell e m omega j = ⋃ n : ℕ, truncatedCell e m omega (cutoff n) j := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := (eventually_mem_truncatedCell e m omega j ht).exists
    exact mem_iUnion.2 ⟨n, hn⟩
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.1 ht
    exact truncatedCell_subset_fullCell e m omega (cutoff_pos n) j hn

theorem truncatedCell_aecover (e : ℚ) (m : ℕ) (omega : ℝ) (j : FourthCell m) :
    AECover (volume.restrict (fullCell e m omega j)) atTop
      (fun n : ℕ => truncatedCell e m omega (cutoff n) j) where
  measurableSet n := truncatedCell_measurable e m omega (cutoff n) j
  ae_eventually_mem := by
    filter_upwards [ae_restrict_mem (fullCell_measurable e m omega j)] with t ht
    exact eventually_mem_truncatedCell e m omega j ht

theorem extendedKernel_nonneg_on_fullCell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    {t : Tuple} (ht : t ∈ fullCell e m omega j) :
    0 ≤ extendedKernel e m cap4 j t := by
  obtain ⟨n, hn⟩ := (eventually_mem_truncatedCell e m omega j ht).exists
  exact original_integrand_nonneg e chi m omega (cutoff_pos n) J4 cap4 hcheck j hj hn

theorem rawKernel_eq_extended_on_fullCell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    {t : Tuple} (ht : t ∈ fullCell e m omega j) :
    rawKernel e m cap4 j t = extendedKernel e m cap4 j t := by
  obtain ⟨n, hn⟩ := (eventually_mem_truncatedCell e m omega j ht).exists
  unfold rawKernel extendedKernel
  rw [rawProfile_eq_extended_on_truncated e m omega (cutoff_pos n) j le_rfl hn,
    rawProfile_eq_extended_on_truncated e m omega (cutoff_pos n) j
      (selected_cap_ge_old e chi m omega J4 cap4 hcheck j hj) hn]
  rfl

/-- Integrability is deduced from the genuinely proved bounded cutoff
selected integrals, the nonnegative original integrand, and exhaustion. -/
theorem integrableOn_original_extendedKernel_fullCell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    IntegrableOn (extendedKernel e m cap4 j) (fullCell e m omega j) := by
  obtain ⟨L, hL⟩ := exists_original_selectedIntegral_zero_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 hcheck
  obtain ⟨B, hB⟩ := (hL.comp cutoff_tendsto_right).isBoundedUnder_le
  have hfi : ∀ n : ℕ, IntegrableOn (extendedKernel e m cap4 j)
      (truncatedCell e m omega (cutoff n) j)
      (volume.restrict (fullCell e m omega j)) := by
    intro n
    change Integrable _ ((volume.restrict _).restrict _)
    rw [Measure.restrict_restrict_of_subset
      (truncatedCell_subset_fullCell e m omega (cutoff_pos n) j)]
    exact integrableOn_cellIntegrand e m omega (cutoff_pos n) cap4 j
  have hnn : ∀ᵐ t ∂volume.restrict (fullCell e m omega j),
      0 ≤ extendedKernel e m cap4 j t := by
    filter_upwards [ae_restrict_mem (fullCell_measurable e m omega j)] with t ht
    exact extendedKernel_nonneg_on_fullCell e chi m omega J4 cap4 hcheck j hj ht
  apply (truncatedCell_aecover e m omega j).integrable_of_integral_bounded_of_nonneg_ae
    B hfi hnn
  filter_upwards [hB] with n hn
  change (∫ t, extendedKernel e m cap4 j t
    ∂(volume.restrict (fullCell e m omega j)).restrict
      (truncatedCell e m omega (cutoff n) j)) ≤ B
  rw [Measure.restrict_restrict_of_subset
    (truncatedCell_subset_fullCell e m omega (cutoff_pos n) j)]
  change cellIntegral e m omega (cutoff n) cap4 j ≤ B
  apply le_trans ?_ hn
  exact Finset.single_le_sum (fun k hk =>
    original_cellIntegral_nonneg e chi m omega (cutoff_pos n) J4 cap4 hcheck k hk) hj

/-- In particular the actual original raw PLUS difference is integrable
on the full positive original source, rather than merely on each cutoff. -/
theorem integrableOn_original_rawKernel_fullCell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    IntegrableOn (rawKernel e m cap4 j) (fullCell e m omega j) := by
  apply (integrableOn_original_extendedKernel_fullCell e chi m omega
    homega homegaRho J4 cap4 hcheck j hj).congr_fun
      (fun t ht => (rawKernel_eq_extended_on_fullCell e chi m omega
        J4 cap4 hcheck j hj ht).symm) (fullCell_measurable e m omega j)

theorem tendsto_cellIntegral_fullCellIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4) :
    Tendsto (fun n : ℕ => cellIntegral e m omega (cutoff n) cap4 j)
      atTop (𝓝 (fullCellIntegral e m omega cap4 j)) := by
  have h := (truncatedCell_aecover e m omega j).integral_tendsto_of_countably_generated
    (integrableOn_original_rawKernel_fullCell e chi m omega
      homega homegaRho J4 cap4 hcheck j hj)
  change Tendsto (fun n : ℕ => ∫ t, rawKernel e m cap4 j t
    ∂(volume.restrict (fullCell e m omega j)).restrict
      (truncatedCell e m omega (cutoff n) j)) atTop
        (𝓝 (fullCellIntegral e m omega cap4 j)) at h
  have heq : ∀ n : ℕ, (∫ t, rawKernel e m cap4 j t
      ∂(volume.restrict (fullCell e m omega j)).restrict
        (truncatedCell e m omega (cutoff n) j)) =
      cellIntegral e m omega (cutoff n) cap4 j := by
    intro n
    rw [Measure.restrict_restrict_of_subset
      (truncatedCell_subset_fullCell e m omega (cutoff_pos n) j)]
    exact (cellIntegral_eq_raw e chi m omega (cutoff_pos n) J4 cap4 hcheck j hj).symm
  simpa only [heq] using h

theorem tendsto_selectedIntegral_fullSelectedIntegral_sequence
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    Tendsto (fun n : ℕ => selectedIntegral e chi m omega (cutoff n) J4 cap4)
      atTop (𝓝 (fullSelectedIntegral e chi m omega J4 cap4)) := by
  exact tendsto_finsetSum (selectedFourthCells e chi m omega J4) (fun j hj =>
    tendsto_cellIntegral_fullCellIntegral e chi m omega homega homegaRho J4 cap4 hcheck j hj)

/-- The constructed zero-cutoff value is now identified with the exact
untruncated Lebesgue integral of the original raw kernel on every selected cell. -/
theorem tendsto_selectedIntegral_fullSelectedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true) :
    Tendsto (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (fullSelectedIntegral e chi m omega J4 cap4)) := by
  obtain ⟨L, hL⟩ := exists_original_selectedIntegral_zero_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 hcheck
  have heq : L = fullSelectedIntegral e chi m omega J4 cap4 :=
    tendsto_nhds_unique (hL.comp cutoff_tendsto_right)
      (tendsto_selectedIntegral_fullSelectedIntegral_sequence
        e chi m omega homega homegaRho J4 cap4 hcheck)
  rwa [heq] at hL

/-- Full original arithmetic mean with its explicit untruncated original
integral, retaining the exact normalized saving and arbitrary covering cap. -/
theorem tendsto_original_actualSaving_fullSelectedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedActualSaving e chi m omega J4 cap4 N (cap N))
      evenTargets (𝓝 (fullSelectedIntegral e chi m omega J4 cap4)) := by
  obtain ⟨L, hL, hmean⟩ := exists_original_fourth_actual_mean_and_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 hcheck
  have heq : L = fullSelectedIntegral e chi m omega J4 cap4 :=
    tendsto_nhds_unique hL (tendsto_selectedIntegral_fullSelectedIntegral
      e chi m omega homega homegaRho J4 cap4 hcheck)
  simpa only [heq] using hmean cap hcap

/-- The literal original retained-policy saving, starting at d=1 and the
empty causal history. -/
def normalizedPolicySaving (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ) (N cap : ℕ) : ℝ :=
  (firstExitRetainedPolynomial
      (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) -
    firstExitRetainedPolynomial
      (fourthCappedUpperPolicy
        (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (level4 e chi m omega J4 cap4 (N : ℝ)))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
    Real.log (N : ℝ) / singularSeries N

theorem tendsto_original_policySaving_fullSelectedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedPolicySaving e chi m omega J4 cap4 N (cap N))
      evenTargets (𝓝 (fullSelectedIntegral e chi m omega J4 cap4)) := by
  apply (tendsto_original_actualSaving_fullSelectedIntegral
    e chi m omega homega homegaRho J4 cap4 hcheck cap hcap).congr'
  filter_upwards [(eventually_gt_atTop (1 : ℕ)).filter_mono
    (show evenTargets ≤ atTop from inf_le_left)] with N hN
  unfold normalizedPolicySaving normalizedActualSaving
  rw [P1OriginalFourthLimit.originalPolicySaving_eq e chi m omega J4 cap4 hcheck
    N (cap N) hN]

end
end ImbalancedChen.P1OriginalFourthUntruncatedIntegral
