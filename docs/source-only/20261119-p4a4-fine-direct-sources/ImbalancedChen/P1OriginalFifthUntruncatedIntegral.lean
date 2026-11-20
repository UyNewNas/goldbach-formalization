import ImbalancedChen.P1OriginalFifthZeroCutoffLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The full positive SAME-coarse original fifth source, with its true gated
canonical lower kernel, is integrable. Integrability follows from kernel
positivity, the constructed bounded cutoff integrals and exact exhaustion.
The full Lebesgue integral equals the actual arithmetic and retained-policy
saving mean. No full-integral or mean supplier is assumed. This is not an
identification with the corrected variable-old manuscript dictionary.
-/

namespace ImbalancedChen.P1OriginalFifthUntruncatedIntegral
noncomputable section
open MeasureTheory Filter Topology Set
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation P1OriginalFifthIntegral
open P1OriginalFifthMovingScaleLimit P1OriginalFifthZeroCutoffLimit

abbrev Tuple := Fin 5 → ℝ

def fullCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m) : Set Tuple :=
  {t | ∀ i, 0 < t i} ∩
    (logPrimeBox (fun _ : Fin 5 => 0) (fun _ => (19 / 96 : ℝ)) ∩
      P1OriginalFifthLimit.sourceRegion e chi m omega j)

def fullCellIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (cap5 : Label5 m → ℚ) (j : Label5 m) : ℝ :=
  ∫ t in fullCell e chi m omega j,
    cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t

def fullSelectedIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    fullCellIntegral e chi m omega J4 cap4 cap5 j

def cutoff (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_tendsto_zero : Tendsto cutoff atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem cutoff_tendsto_right : Tendsto cutoff atTop (𝓝[Ioi 0] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.2 ⟨cutoff_tendsto_zero, Eventually.of_forall cutoff_pos⟩

theorem fullCell_measurable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m) :
    MeasurableSet (fullCell e chi m omega j) := by
  have hp : MeasurableSet {t : Tuple | ∀ i, 0 < t i} := by
    have heq : {t : Tuple | ∀ i, 0 < t i} = ⋂ i : Fin 5, {t : Tuple | 0 < t i} := by
      ext t
      simp only [mem_iInter, mem_setOf_eq]
    rw [heq]
    exact MeasurableSet.iInter (fun i =>
      measurableSet_lt measurable_const (measurable_pi_apply i))
  apply hp.inter
  apply (measurableSet_logPrimeBox _ _).inter
  exact (measurableSet_logPrimeMeshCell _ _ _ _).inter
    (HistoricalThirdCoarse.P1OriginalCoarseFifth.measurableSet_jointRegion _ _ _ _ _)

theorem truncatedCell_subset_fullCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    {a : ℝ} (ha : 0 < a) (j : Label5 m) :
    truncatedCell e chi m omega a j ⊆ fullCell e chi m omega j := by
  intro t ht
  refine ⟨fun i => ha.trans_le (mem_logPrimeBox.mp ht.1 i).1, ?_, ht.2⟩
  exact mem_logPrimeBox.mpr (fun i =>
    ⟨(ha.trans_le (mem_logPrimeBox.mp ht.1 i).1).le, (mem_logPrimeBox.mp ht.1 i).2⟩)

theorem eventually_mem_truncatedCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Label5 m) {t : Tuple} (ht : t ∈ fullCell e chi m omega j) :
    ∀ᶠ n : ℕ in atTop, t ∈ truncatedCell e chi m omega (cutoff n) j := by
  have hc : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 5, cutoff n < t i :=
    eventually_all.2 (fun i => cutoff_tendsto_zero.eventually (gt_mem_nhds (ht.1 i)))
  filter_upwards [hc] with n hn
  exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(hn i).le, (mem_logPrimeBox.mp ht.2.1 i).2⟩), ht.2.2⟩

theorem fullCell_eq_iUnion_truncatedCell (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (j : Label5 m) :
    fullCell e chi m omega j = ⋃ n : ℕ, truncatedCell e chi m omega (cutoff n) j := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := (eventually_mem_truncatedCell e chi m omega j ht).exists
    exact mem_iUnion.2 ⟨n, hn⟩
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.1 ht
    exact truncatedCell_subset_fullCell e chi m omega (cutoff_pos n) j hn

theorem truncatedCell_aecover (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Label5 m) :
    AECover (volume.restrict (fullCell e chi m omega j)) atTop
      (fun n : ℕ => truncatedCell e chi m omega (cutoff n) j) where
  measurableSet n := truncatedCell_measurable e chi m omega (cutoff n) j
  ae_eventually_mem := by
    filter_upwards [ae_restrict_mem (fullCell_measurable e chi m omega j)] with t ht
    exact eventually_mem_truncatedCell e chi m omega j ht

theorem kernel_nonneg_on_fullCell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5)
    {t : Tuple} (ht : t ∈ fullCell e chi m omega j) :
    0 ≤ cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t := by
  have hlevel : (old5 e chi m omega J4 cap4 j : ℝ) ≤ cap5 j := by
    exact_mod_cast h45Check_sound e chi m omega J4 cap4 J5 cap5 h45 j hj
  unfold cellKernel reciprocalWeight
  exact mul_nonneg (sub_nonneg.mpr (p1PrimeOwnCubeGatedProfile_mono t (ht.1 _) hlevel))
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht.1 i).le))

theorem cellIntegral_nonneg
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) :
    0 ≤ cellIntegral e chi m omega a J4 cap4 cap5 j := by
  exact setIntegral_nonneg (truncatedCell_measurable e chi m omega a j)
    (fun t ht => kernel_nonneg_on_fullCell e chi m omega J4 cap4 J5 cap5 h45 j hj
      (truncatedCell_subset_fullCell e chi m omega ha j ht))

/-- Integrability is concluded from bounded cutoff integrals, positivity,
and exact exhaustion; it is not supplied as a full-integral hypothesis. -/
theorem integrableOn_kernel_fullCell
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) :
    IntegrableOn (cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ))
      (fullCell e chi m omega j) := by
  obtain ⟨L, hL⟩ := exists_selectedIntegral_zero_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  obtain ⟨B, hB⟩ := (hL.comp cutoff_tendsto_right).isBoundedUnder_le
  have hfi : ∀ n : ℕ, IntegrableOn
      (cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ))
      (truncatedCell e chi m omega (cutoff n) j)
      (volume.restrict (fullCell e chi m omega j)) := by
    intro n
    change Integrable _ ((volume.restrict _).restrict _)
    rw [Measure.restrict_restrict_of_subset
      (truncatedCell_subset_fullCell e chi m omega (cutoff_pos n) j)]
    exact integrableOn_cellKernel e chi m omega (cutoff_pos n) j _ _
  have hnn : ∀ᵐ t ∂volume.restrict (fullCell e chi m omega j),
      0 ≤ cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t := by
    filter_upwards [ae_restrict_mem (fullCell_measurable e chi m omega j)] with t ht
    exact kernel_nonneg_on_fullCell e chi m omega J4 cap4 J5 cap5 h45 j hj ht
  apply (truncatedCell_aecover e chi m omega j).integrable_of_integral_bounded_of_nonneg_ae
    B hfi hnn
  filter_upwards [hB] with n hn
  change (∫ t, cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t
    ∂(volume.restrict (fullCell e chi m omega j)).restrict
      (truncatedCell e chi m omega (cutoff n) j)) ≤ B
  rw [Measure.restrict_restrict_of_subset
    (truncatedCell_subset_fullCell e chi m omega (cutoff_pos n) j)]
  change cellIntegral e chi m omega (cutoff n) J4 cap4 cap5 j ≤ B
  exact (Finset.single_le_sum (fun k hk =>
    cellIntegral_nonneg e chi m omega (cutoff n) (cutoff_pos n) J4 cap4 J5 cap5 h45 k hk) hj).trans hn

theorem tendsto_cellIntegral_fullCellIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (j : Label5 m) (hj : j ∈ selectedFifthCells e chi m omega J5) :
    Tendsto (fun n : ℕ => cellIntegral e chi m omega (cutoff n) J4 cap4 cap5 j)
      atTop (𝓝 (fullCellIntegral e chi m omega J4 cap4 cap5 j)) := by
  have hh := (truncatedCell_aecover e chi m omega j).integral_tendsto_of_countably_generated
    (integrableOn_kernel_fullCell e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45 j hj)
  have heq : ∀ n : ℕ, (∫ t, cellKernel (old5 e chi m omega J4 cap4 j : ℝ) (cap5 j : ℝ) t
      ∂(volume.restrict (fullCell e chi m omega j)).restrict
        (truncatedCell e chi m omega (cutoff n) j)) =
      cellIntegral e chi m omega (cutoff n) J4 cap4 cap5 j := by
    intro n
    rw [Measure.restrict_restrict_of_subset
      (truncatedCell_subset_fullCell e chi m omega (cutoff_pos n) j)]
    rfl
  simpa only [heq, fullCellIntegral] using hh

theorem tendsto_selectedIntegral_fullSelectedIntegral_sequence
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    Tendsto (fun n : ℕ => selectedIntegral e chi m omega (cutoff n) J4 cap4 J5 cap5)
      atTop (𝓝 (fullSelectedIntegral e chi m omega J4 cap4 J5 cap5)) :=
  tendsto_finsetSum (selectedFifthCells e chi m omega J5) (fun j hj =>
    tendsto_cellIntegral_fullCellIntegral e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45 j hj)

theorem tendsto_selectedIntegral_fullSelectedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true) :
    Tendsto (fun a : ℝ => selectedIntegral e chi m omega a J4 cap4 J5 cap5)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (fullSelectedIntegral e chi m omega J4 cap4 J5 cap5)) := by
  obtain ⟨L, hL⟩ := exists_selectedIntegral_zero_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  have heq : L = fullSelectedIntegral e chi m omega J4 cap4 J5 cap5 :=
    tendsto_nhds_unique (hL.comp cutoff_tendsto_right)
      (tendsto_selectedIntegral_fullSelectedIntegral_sequence
        e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45)
  rwa [heq] at hL

theorem tendsto_actualSaving_fullSelectedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedActualSaving e chi m omega J4 cap4 J5 cap5 N (cap N))
      evenTargets (𝓝 (fullSelectedIntegral e chi m omega J4 cap4 J5 cap5)) := by
  obtain ⟨L, hL, hmean⟩ := exists_actual_mean_and_cutoff_limit
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45
  have heq : L = fullSelectedIntegral e chi m omega J4 cap4 J5 cap5 :=
    tendsto_nhds_unique hL (tendsto_selectedIntegral_fullSelectedIntegral
      e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45)
  simpa only [heq] using hmean cap hcap

/-- Literal retained-policy difference starts at d=1 and empty history. -/
def normalizedPolicySaving (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ) (N cap : ℕ) : ℝ :=
  (firstExitRetainedPolynomial
      (fourthCappedUpperPolicy (HistoricalThirdCoarse.initialPolicy (e : ℝ) m (N : ℝ))
        (HistoricalThirdCoarse.rawLevel (e : ℝ) chi m omega (N : ℝ))
        (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ)))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) -
    firstExitRetainedPolynomial (policy5 e chi m omega J4 cap4 J5 cap5 (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))) *
    Real.log (N : ℝ) / singularSeries N

theorem tendsto_policySaving_fullSelectedIntegral
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedPolicySaving e chi m omega J4 cap4 J5 cap5 N (cap N))
      evenTargets (𝓝 (fullSelectedIntegral e chi m omega J4 cap4 J5 cap5)) := by
  apply (tendsto_actualSaving_fullSelectedIntegral
    e chi m omega homega homegaRho J4 cap4 J5 cap5 h34 h45 cap hcap).congr'
  filter_upwards [(eventually_gt_atTop (1 : ℕ)).filter_mono
    (show evenTargets ≤ atTop from inf_le_left)] with N hN
  unfold normalizedPolicySaving normalizedActualSaving
  rw [actualFourthToFifthSaving_eq e chi m omega J4 cap4 J5 cap5 h34 h45
    N (cap N) hN ((N : ℝ) ^ (19 / 96 : ℝ))]

end
end ImbalancedChen.P1OriginalFifthUntruncatedIntegral
