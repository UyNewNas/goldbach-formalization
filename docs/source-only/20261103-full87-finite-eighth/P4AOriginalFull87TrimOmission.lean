import ImbalancedChen.P4AOriginalFull87StrictActionTrim
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

One trim index pays the L1 omission over the finite ORIGINAL87 family.
The unconditional instance is the actual omitted source volume. The weighted
version states its integrability hypothesis explicitly; no original saving
kernel, numerical endpoint, prime mean, or compiler reserve is smuggled in.
No assumption that Source intersect historyCore is compact is used.
-/
namespace ImbalancedChen.P4AOriginalFull87TrimOmission
noncomputable section
open scoped Classical BigOperators Topology ENNReal
open Set Filter MeasureTheory VariableEnvelope P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87HistoryCore (width width_pos)

/-- The actual omitted part, integrated against an absolute weight. -/
def omitted (c : Cell) (n : ℕ) (f : Point → ℝ) : ℝ :=
  ∫ t in sourceSet c, (trim c (width n))ᶜ.indicator (fun t => ‖f t‖) t

theorem omitted_nonneg (c : Cell) (n : ℕ) (f : Point → ℝ) :
    0 ≤ omitted c n f := by
  apply integral_nonneg
  intro t
  by_cases ht : t ∈ (trim c (width n))ᶜ
  · simpa only [indicator_of_mem ht] using norm_nonneg (f t)
  · simp only [indicator_of_notMem ht, le_refl]

/-- Exact identification of the paid set, not just a vanishing proxy. -/
theorem omitted_eq_sdiff (c : Cell) (n : ℕ) (f : Point → ℝ) :
    omitted c n f = ∫ t in sourceSet c \ trim c (width n), ‖f t‖ := by
  unfold omitted
  rw [setIntegral_indicator (isClosed_trim c (width n)).measurableSet.compl]
  rfl

theorem tendsto_omitted (c : Cell) (f : Point → ℝ)
    (hf : IntegrableOn f (sourceSet c)) :
    Tendsto (fun n => omitted c n f) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (sourceSet c))
    (F := fun n => (trim c (width n))ᶜ.indicator (fun t => ‖f t‖))
    (f := fun _ => (0 : ℝ)) (fun t => ‖f t‖)
    (fun n => (hf.norm.indicator
      (isClosed_trim c (width n)).measurableSet.compl).aestronglyMeasurable)
    hf.norm
    (fun n => Eventually.of_forall fun t => by
      simpa only [norm_norm] using
        (norm_indicator_le_norm_self (s := (trim c (width n))ᶜ)
          (fun t => ‖f t‖) t))
    (show ∀ᵐ t ∂volume.restrict (sourceSet c),
      Tendsto (fun n => (trim c (width n))ᶜ.indicator (fun t => ‖f t‖) t)
        atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
      apply tendsto_const_nhds.congr'
      filter_upwards [source_eventually_trimmed ht] with n hn
      simp [hn])
  simpa only [omitted, integral_zero] using hlim

def totalOmitted (n : ℕ) (f : Cell → Point → ℝ) : ℝ :=
  ∑ c : Cell, omitted c n (f c)

theorem totalOmitted_nonneg (n : ℕ) (f : Cell → Point → ℝ) :
    0 ≤ totalOmitted n f :=
  Finset.sum_nonneg (fun c _ => omitted_nonneg c n (f c))

theorem tendsto_totalOmitted (f : Cell → Point → ℝ)
    (hf : ∀ c, IntegrableOn (f c) (sourceSet c)) :
    Tendsto (fun n => totalOmitted n f) atTop (𝓝 0) := by
  have h := tendsto_finset_sum (Finset.univ : Finset Cell)
    (fun c _ => tendsto_omitted c (f c) (hf c))
  simpa only [totalOmitted, Finset.sum_const_zero] using h

/-- No per-source trim choices survive this terminal: the SAME index is
chosen before the arithmetic schedule, N, tuples and actual parent states. -/
theorem exists_common_L1_trim (f : Cell → Point → ℝ)
    (hf : ∀ c, IntegrableOn (f c) (sourceSet c))
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → totalOmitted n f < epsilon :=
  Filter.eventually_atTop.mp
    ((tendsto_totalOmitted f hf).eventually (gt_mem_nhds he))

/-- Finite source volume follows from the actual source coordinate bounds. -/
theorem source_volume_lt_top (c : Cell) : volume (sourceSet c) < ∞ := by
  have hsub : sourceSet c ⊆ Icc (fun _ : Fin 8 => (0 : ℝ)) (fun _ => mu) := by
    intro t ht
    obtain ⟨hlo, hup⟩ := P4AOriginalFull87HistoryCore.source_in_cube ht
    exact ⟨hlo, hup⟩
  exact (measure_mono hsub).trans_lt isCompact_Icc.measure_lt_top

/-- Unconditional volume instance. This does not purport to pay an
arithmetic/density reserve merely because Euclidean volume is small. -/
theorem exists_common_volume_trim (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      totalOmitted n (fun _ _ => (1 : ℝ)) < epsilon := by
  apply exists_common_L1_trim (fun _ _ => (1 : ℝ)) _ epsilon he
  intro c
  exact integrableOn_const (source_volume_lt_top c).ne

end
end ImbalancedChen.P4AOriginalFull87TrimOmission
