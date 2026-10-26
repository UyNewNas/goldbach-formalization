import ImbalancedChen.Part3PositiveRectangleSmoothTensorDensity
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One common sequence of positive compact-height C-infinity profiles
approximates an arbitrary family in TWO locally finite height measures.
The same explicit cutoff is used for every index and every sequence term.
Density is supplied by pinned SmoothApprox for the sum measure; it is
proved here, rather than stored in an hApprox assumption. In particular a
finite family of Fourier coefficients needs no separate diagonal choice.
The measures may be the pushforwards of the raw and reciprocal-square
height measures restricted to a fixed larger positive compact interval.
-/

namespace ImbalancedChen.Part3.CommonHeightSmoothApproximation20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open PositiveRectangleSmoothTensorDensity20261025a

theorem memLp_two_add_measure {μ ν : Measure ℝ} {f : ℝ → ℂ}
    (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν) : MemLp f 2 (μ + ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hμ.aestronglyMeasurable.add_measure hν.aestronglyMeasurable)).mpr
  exact ((memLp_two_iff_integrable_sq_norm hμ.aestronglyMeasurable).mp hμ).add_measure
    ((memLp_two_iff_integrable_sq_norm hν.aestronglyMeasurable).mp hν)

def bandCutoff (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (y : ℝ) : ℂ :=
  (verticalBump a b ha hab y : ℂ)

theorem bandCutoff_smooth (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContDiff ℝ ∞ (bandCutoff a b ha hab) :=
  Complex.ofRealCLM.contDiff.comp (verticalBump a b ha hab).contDiff

theorem bandCutoff_compact (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    HasCompactSupport (bandCutoff a b ha hab) :=
  (verticalBump a b ha hab).hasCompactSupport.comp_left rfl

theorem bandCutoff_norm_le_one (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    ‖bandCutoff a b ha hab y‖ ≤ 1 := by
  rw [bandCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (verticalBump a b ha hab).nonneg]
  exact (verticalBump a b ha hab).le_one

theorem bandCutoff_eq_one (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    {y : ℝ} (hy : y ∈ Icc a b) : bandCutoff a b ha hab y = 1 := by
  simp only [bandCutoff, verticalBump_eq_one a b ha hab hy, Complex.ofReal_one]

theorem bandCutoff_tsupport_positive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    tsupport (bandCutoff a b ha hab) ⊆ Ioi (0 : ℝ) :=
  (tsupport_comp_subset rfl _).trans (verticalBump_positive_support a b ha hab)

/-- The common outer interval has lower endpoint a/2 > 0. -/
theorem bandCutoff_tsupport_band (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    tsupport (bandCutoff a b ha hab) ⊆ Icc (a / 2) (b + a / 2) := by
  intro y hy
  have h := (tsupport_comp_subset (f := Complex.ofReal) rfl
    (verticalBump a b ha hab)) hy
  rw [(verticalBump a b ha hab).tsupport_eq, Metric.mem_closedBall,
    Real.dist_eq, abs_le] at h
  change -((b - a) / 2 + a / 2) ≤ y - (a + b) / 2 ∧
    y - (a + b) / 2 ≤ (b - a) / 2 + a / 2 at h
  constructor <;> linarith [h.1, h.2]

theorem cutoff_error_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f : ℝ → ℂ} (hs : Function.support f ⊆ Icc a b) (g : ℝ → ℂ) (y : ℝ) :
    ‖f y - bandCutoff a b ha hab y * g y‖ ≤ ‖f y - g y‖ := by
  have hf : bandCutoff a b ha hab y * f y = f y := by
    by_cases h : f y = 0
    · simp [h]
    · rw [bandCutoff_eq_one a b ha hab (hs h), one_mul]
  calc
    _ = ‖bandCutoff a b ha hab y * (f y - g y)‖ := by rw [mul_sub, hf]
    _ ≤ _ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (bandCutoff_norm_le_one a b ha hab y)
        (norm_nonneg _)).trans_eq (one_mul _)

/-- A literal smooth compact function, with common positive support and
both physical errors paid by a single approximation in the sum measure. -/
theorem exists_two_measure_band_approximation
    (μ ν : Measure ℝ) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (f : ℝ → ℂ)
    (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν)
    (hs : Function.support f ⊆ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ tsupport (bandCutoff a b ha hab) ∧
      eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 ν ≤ ENNReal.ofReal ε := by
  obtain ⟨q, hqc, hqs, hqe⟩ := (memLp_two_add_measure hμ hν).exist_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 ≤ (2 : ℝ≥0∞)) hε
  let g : ℝ → ℂ := fun y => bandCutoff a b ha hab y * q y
  have he : eLpNorm (f - g) 2 (μ + ν) ≤ ENNReal.ofReal ε := by
    exact (eLpNorm_mono (fun y => cutoff_error_le ha hab hs q y)).trans hqe
  exact ⟨g, (bandCutoff_smooth a b ha hab).mul hqs,
    (bandCutoff_compact a b ha hab).mul_right, tsupport_mul_subset_left,
    (eLpNorm_le_add_measure_right (f - g) μ ν).trans he,
    (eLpNorm_le_add_measure_left (f - g) μ ν).trans he⟩

def tolerance (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem tolerance_pos (n : ℕ) : 0 < tolerance n := by unfold tolerance; positivity

theorem tolerance_tendsto : Tendsto tolerance atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- All family members and sequence terms share one compact positive
height support. The index set need not even be finite. -/
theorem exists_common_height_sequence {ι : Type*}
    (μ ν : Measure ℝ) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (f : ι → ℝ → ℂ)
    (hμ : ∀ i, MemLp (f i) 2 μ) (hν : ∀ i, MemLp (f i) 2 ν)
    (hs : ∀ i, Function.support (f i) ⊆ Icc a b) :
    ∃ g : ℕ → ι → ℝ → ℂ, ∀ n i,
      ContDiff ℝ ∞ (g n i) ∧ HasCompactSupport (g n i) ∧
      tsupport (g n i) ⊆ tsupport (bandCutoff a b ha hab) ∧
      eLpNorm (f i - g n i) 2 μ ≤ ENNReal.ofReal (tolerance n) ∧
      eLpNorm (f i - g n i) 2 ν ≤ ENNReal.ofReal (tolerance n) := by
  classical
  have h (n : ℕ) (i : ι) := exists_two_measure_band_approximation
    μ ν ha hab (f i) (hμ i) (hν i) (hs i) (tolerance_pos n)
  choose g hg using h
  exact ⟨g, hg⟩

theorem norm_toLp_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε) :
    ‖hf.toLp f - hg.toLp g‖ ≤ ε := by
  rw [← MemLp.toLp_sub hf hg, Lp.norm_toLp]
  exact (ENNReal.toReal_mono (by simp) h).trans_eq (ENNReal.toReal_ofReal hε)

/-- The seminorm estimates give convergence in the native quotient L2
space, including the actual chosen representatives and their AE joins. -/
theorem toLp_tendsto_of_tolerance {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {g : ℕ → α → ℂ} (hf : MemLp f 2 μ)
    (hg : ∀ n, MemLp (g n) 2 μ)
    (he : ∀ n, eLpNorm (f - g n) 2 μ ≤ ENNReal.ofReal (tolerance n)) :
    Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hf.toLp f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => by
      rw [norm_sub_rev]
      exact norm_toLp_sub_le hf (hg n) (tolerance_pos n).le (he n))
    tolerance_tendsto

end
end ImbalancedChen.Part3.CommonHeightSmoothApproximation20261026b
