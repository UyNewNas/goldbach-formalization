import ImbalancedChen.Part3KLCandidateSmoothCore
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
SOURCEONLY / UNCOMPILED / CODE_ONLY, 2026-10-24.

This strengthens the ambient smooth core for the *positive restriction* of the
explicit candidate measure. The new approximants are smooth on the real line,
compactly supported, and their topological supports lie inside (0,infinity).
Thus their restrictions really belong to C_c^infinity((0,infinity)). The proof
uses zero mass on the nonpositive axis, regularity from local finiteness, a
strong L² cutoff at zero, and Mathlib's smooth approximation theorem. There
is no KL Plancherel or automorphic spectral measure identification here.

The smoothness order below is explicitly C∞, `((⊤ : ENat) : WithTop ENat)`,
not the analytic order `⊤ : WithTop ENat`. This corrects the former analytic
contracts to the stated smooth compact-support intent; it is a statement
correction, not merely a change to a proof. No energy or measure premise is
removed. Full intended-type regressions are included below.
-/

namespace ImbalancedChen.Part3.KLPositiveInteriorCore20261024zz
noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal
open P3KLDensityMeasureSourceOnly
open KLCandidateSmoothCore20261024zz

local instance : IsFiniteMeasureOnCompacts positiveCandidateMeasure := by
  dsimp [positiveCandidateMeasure]
  letI : IsFiniteMeasureOnCompacts candidateMeasure :=
    ⟨fun K hK => candidateMeasure_compact_lt_top hK⟩
  infer_instance

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The positive restriction gives no mass to the nonpositive axis. -/
theorem positiveCandidateMeasure_Iic_zero :
    positiveCandidateMeasure (Iic (0 : ℝ)) = 0 := by
  rw [positiveCandidateMeasure, Measure.restrict_apply measurableSet_Iic]
  have hempty : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    exact fun h => (not_lt_of_ge h.1) h.2
  rw [hempty, measure_empty]

/-- A precise strong cutoff input: every positive neighborhood of zero can
be chosen with arbitrarily small candidate mass. -/
theorem exists_positive_Iic_small {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ positiveCandidateMeasure (Iic δ) < η := by
  obtain ⟨U, hsub, hUopen, hUμ⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := positiveCandidateMeasure)
      (Iic (0 : ℝ)) η (by simpa [positiveCandidateMeasure_Iic_zero] using hη)
  have h0U : (0 : ℝ) ∈ U := hsub le_rfl
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds h0U)
  refine ⟨r / 2, by positivity, (measure_mono ?_).trans_lt hUμ⟩
  intro t ht
  by_cases ht0 : t ≤ 0
  · exact hsub ht0
  · apply hball
    have htp : 0 < t := lt_of_not_ge ht0
    change dist t 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_pos htp]
    linarith

/-- A fixed smooth multiplier, zero for `t ≤ δ/2` and one for `t ≥ δ`. -/
def nearZeroCutoff (δ t : ℝ) : ℝ :=
  Real.smoothTransition ((2 / δ) * t - 1)

theorem nearZeroCutoff_contDiff {δ : ℝ} :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (nearZeroCutoff δ) := by
  have hlinear : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun t : ℝ => (2 / δ) * t - 1) := by fun_prop
  exact Real.smoothTransition.contDiff.comp hlinear

theorem nearZeroCutoff_nonneg (δ t : ℝ) : 0 ≤ nearZeroCutoff δ t :=
  Real.smoothTransition.nonneg _

theorem nearZeroCutoff_le_one (δ t : ℝ) : nearZeroCutoff δ t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem nearZeroCutoff_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ / 2) :
    nearZeroCutoff δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  dsimp [nearZeroCutoff]
  have : (2 / δ) * t ≤ 1 := by
    apply (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq
    field_simp
    ring
  linarith

theorem nearZeroCutoff_one {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    nearZeroCutoff δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  dsimp [nearZeroCutoff]
  have : 2 ≤ (2 / δ) * t := by
    calc
      (2 : ℝ) = (2 / δ) * δ := by field_simp; ring
      _ ≤ (2 / δ) * t := mul_le_mul_of_nonneg_left ht (by positivity)
  linarith

def cutAtZero (δ : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  nearZeroCutoff δ t • g t

theorem cutAtZero_contDiff {δ : ℝ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (cutAtZero δ g) := by
  exact (nearZeroCutoff_contDiff (δ := δ)).smul hg

theorem cutAtZero_hasCompactSupport {δ : ℝ} {g : ℝ → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (cutAtZero δ g) := by
  apply hg.mono
  intro t ht
  change nearZeroCutoff δ t • g t ≠ 0 at ht
  exact fun hg0 => ht (by simp [hg0])

/-- The support is compact *inside* the positive half-axis, not merely
compact in the ambient real line. -/
theorem cutAtZero_tsupport_positive {δ : ℝ} {g : ℝ → ℂ}
    (hδ : 0 < δ) : tsupport (cutAtZero δ g) ⊆ Ioi (0 : ℝ) := by
  have hsupp : Function.support (cutAtZero δ g) ⊆ Ici (δ / 2) := by
    intro t ht
    by_contra h
    have hlt : t < δ / 2 := lt_of_not_ge h
    exact ht (by simp [cutAtZero, nearZeroCutoff_zero hδ hlt.le])
  have hclosed : tsupport (cutAtZero δ g) ⊆ Ici (δ / 2) :=
    closure_minimal hsupp isClosed_Ici
  intro t ht
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < δ / 2) (hclosed ht)

/-- Strong L² cutoff at zero for every smooth compactly supported function.
The statement is uniform for all smaller positive cutoff radii. -/
theorem smooth_strong_cutoff_at_zero {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) (hgc : HasCompactSupport g)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      eLpNorm (g - cutAtZero r g) 2 positiveCandidateMeasure ≤ ε := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hCnonneg : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  obtain ⟨η, hη, hsmall⟩ :=
    exists_eLpNorm_indicator_le (p := (2 : ℝ≥0∞))
      (μ := positiveCandidateMeasure) (by norm_num) (C : ℂ) hε
  obtain ⟨δ, hδ, hμδ⟩ := exists_positive_Iic_small
    (η := (η : ℝ≥0∞)) (by exact_mod_cast hη)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ
  let s : Set ℝ := Iic r
  have hs : NullMeasurableSet s positiveCandidateMeasure := measurableSet_Iic.nullMeasurableSet
  have hμs : positiveCandidateMeasure s ≤ (η : ℝ≥0∞) := by
    exact (measure_mono (Iic_subset_Iic.mpr hrδ)).trans hμδ.le
  have hconst : eLpNorm (s.indicator (fun _ : ℝ => (C : ℂ))) 2
      positiveCandidateMeasure ≤ ε := hsmall s hμs hs
  have hmeas : AEStronglyMeasurable (g - cutAtZero r g)
      positiveCandidateMeasure :=
    (hg.continuous.sub (cutAtZero_contDiff hg).continuous).aestronglyMeasurable
  have hpoint : ∀ᵐ t ∂positiveCandidateMeasure,
      ‖(g - cutAtZero r g) t‖ ≤
        (1 : ℝ) * ‖(s.indicator (fun _ : ℝ => (C : ℂ))) t‖ := by
    filter_upwards [] with t
    by_cases ht : t ∈ s
    · have hc0 := nearZeroCutoff_nonneg r t
      have hc1 := nearZeroCutoff_le_one r t
      have hnorm : ‖g t - cutAtZero r g t‖ =
          (1 - nearZeroCutoff r t) * ‖g t‖ := by
        simp only [cutAtZero, ← sub_smul, one_smul, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      simp only [Pi.sub_apply, indicator_of_mem ht, one_mul]
      rw [hnorm, Complex.norm_real, abs_of_nonneg hCnonneg]
      calc
        (1 - nearZeroCutoff r t) * ‖g t‖ ≤ ‖g t‖ := by
          nlinarith [mul_nonneg hc0 (norm_nonneg (g t))]
        _ ≤ C := hC t
    · have hrt : r ≤ t := le_of_not_ge ht
      simp [indicator_of_not_mem ht, cutAtZero,
        nearZeroCutoff_one hr hrt]
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpoint
    (2 : ℝ≥0∞)
  simpa using hle.trans hconst

/-- Genuine C_c^infinity((0,infinity)) density in the L² space of the
positive candidate measure, stated as a representative norm estimate. -/
theorem positive_candidate_interior_smooth_approx {f : ℝ → ℂ}
    (hf : MemLp f 2 positiveCandidateMeasure) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℂ,
      HasCompactSupport h ∧ ContDiff ℝ ((⊤ : ENat) : WithTop ENat) h ∧
      tsupport h ⊆ Ioi (0 : ℝ) ∧
      eLpNorm (f - h) 2 positiveCandidateMeasure ≤ ENNReal.ofReal ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨g, hgc, hgs, hfg⟩ :=
    positive_candidate_smooth_approx hf hhalf
  obtain ⟨δ, hδ, hcut⟩ :=
    smooth_strong_cutoff_at_zero hgs hgc
      (ε := ENNReal.ofReal (ε / 2)) (by positivity)
  let h : ℝ → ℂ := cutAtZero δ g
  refine ⟨h, cutAtZero_hasCompactSupport hgc,
    cutAtZero_contDiff hgs, cutAtZero_tsupport_positive hδ, ?_⟩
  have hgh : eLpNorm (g - h) 2 positiveCandidateMeasure ≤
      ENNReal.ofReal (ε / 2) := hcut δ hδ le_rfl
  have hfun : (f - h) = (f - g) + (g - h) := by
    funext t
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
  rw [hfun]
  calc
    eLpNorm ((f - g) + (g - h)) 2 positiveCandidateMeasure ≤
        eLpNorm (f - g) 2 positiveCandidateMeasure +
          eLpNorm (g - h) 2 positiveCandidateMeasure :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hfg hgh
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity)]
      congr 1
      ring


-- Full intended C∞ contracts (including all hypotheses and conclusions).

example {δ : ℝ} :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (nearZeroCutoff δ) :=
  nearZeroCutoff_contDiff

example {δ : ℝ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (cutAtZero δ g) :=
  cutAtZero_contDiff hg

example {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) (hgc : HasCompactSupport g)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      eLpNorm (g - cutAtZero r g) 2 positiveCandidateMeasure ≤ ε :=
  smooth_strong_cutoff_at_zero hg hgc hε

example {f : ℝ → ℂ}
    (hf : MemLp f 2 positiveCandidateMeasure) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℂ,
      HasCompactSupport h ∧ ContDiff ℝ ((⊤ : ENat) : WithTop ENat) h ∧
      tsupport h ⊆ Ioi (0 : ℝ) ∧
      eLpNorm (f - h) 2 positiveCandidateMeasure ≤ ENNReal.ofReal ε :=
  positive_candidate_interior_smooth_approx hf hε


-- Whole declaration ascriptions: @ exposes every implicit parameter.

example : ∀ {δ : ℝ},
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (nearZeroCutoff δ) :=
  @nearZeroCutoff_contDiff

example : ∀ {δ : ℝ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g),
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (cutAtZero δ g) :=
  @cutAtZero_contDiff

example : ∀ {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g) (hgc : HasCompactSupport g)
    {ε : ℝ≥0∞} (hε : ε ≠ 0),
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      eLpNorm (g - cutAtZero r g) 2 positiveCandidateMeasure ≤ ε :=
  @smooth_strong_cutoff_at_zero

example : ∀ {f : ℝ → ℂ}
    (hf : MemLp f 2 positiveCandidateMeasure) {ε : ℝ} (hε : 0 < ε),
    ∃ h : ℝ → ℂ,
      HasCompactSupport h ∧ ContDiff ℝ ((⊤ : ENat) : WithTop ENat) h ∧
      tsupport h ⊆ Ioi (0 : ℝ) ∧
      eLpNorm (f - h) 2 positiveCandidateMeasure ≤ ENNReal.ofReal ε :=
  @positive_candidate_interior_smooth_approx

end
end ImbalancedChen.Part3.KLPositiveInteriorCore20261024zz
