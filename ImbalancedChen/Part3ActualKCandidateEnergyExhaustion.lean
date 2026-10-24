import ImbalancedChen.Part3ActualKCompactEvenEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.MonotoneConvergence

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-24.

Full-height nonnegative energy is the supremum of compact-height energies.
For the actual K transform and the concrete candidate density measure,
continuity gives measurability and finite individual truncations.
A UNIFORM finite bound on all truncations is an explicit condition; this
file does not prove that bound. Exactly under that condition one gets full
square-energy integrability, equivalently MemLp 2 for the actual transform.
No Plancherel or spectral-measure identification is asserted. In particular,
no polynomial decay estimate is claimed to control the exponential density.
-/

namespace ImbalancedChen.Part3.ActualKCandidateEnergyExhaustion20261024z
noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualCommonHeightKGramSourceOnly
open ActualKTransformContinuity20261024z
open P3KLDensityMeasureSourceOnly
open ActualKCompactEvenEnergy20261024z

variable {ι : Type*}

/-- The fixed compact exhaustion, retaining both endpoints. -/
def heightWindow (N : ℕ) : Set ℝ := Icc (-(N : ℝ)) (N : ℝ)

theorem heightWindow_measurable (N : ℕ) : MeasurableSet (heightWindow N) := by
  exact measurableSet_Icc

theorem heightWindow_monotone : Monotone heightWindow := by
  intro N M hNM t ht
  have hcast : (N : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hNM
  exact ⟨(neg_le_neg hcast).trans ht.1, ht.2.trans hcast⟩

theorem exists_mem_heightWindow (t : ℝ) : ∃ N : ℕ, t ∈ heightWindow N := by
  obtain ⟨N, hN⟩ := exists_nat_ge |t|
  exact ⟨N, (neg_le_neg hN).trans (neg_abs_le t), (le_abs_self t).trans hN⟩

/-- A concrete monotone-convergence statement for any measurable ENNReal
function and any measure on the real line. No finiteness is assumed. -/
theorem lintegral_eq_iSup_heightWindow (μ : Measure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, f t ∂μ) = ⨆ N : ℕ, ∫⁻ t in heightWindow N, f t ∂μ := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun N => (heightWindow N).indicator f
  have hFm : ∀ N, Measurable (F N) := fun N =>
    hf.indicator (heightWindow_measurable N)
  have hFmono : Monotone F := by
    intro N M hNM t
    dsimp only [F]
    by_cases ht : t ∈ heightWindow N
    · rw [indicator_of_mem ht, indicator_of_mem (heightWindow_monotone hNM ht)]
    · rw [indicator_of_not_mem ht]
      exact bot_le
  have hsup : (fun t => ⨆ N : ℕ, F N t) = f := by
    funext t
    apply le_antisymm
    · apply iSup_le
      intro N
      dsimp only [F]
      by_cases ht : t ∈ heightWindow N
      · rw [indicator_of_mem ht]
      · rw [indicator_of_not_mem ht]
        exact bot_le
    · obtain ⟨N, ht⟩ := exists_mem_heightWindow t
      apply le_iSup_of_le N
      dsimp only [F]
      rw [indicator_of_mem ht]
  calc
    (∫⁻ t, f t ∂μ) = ∫⁻ t, ⨆ N : ℕ, F N t ∂μ := by rw [hsup]
    _ = ⨆ N : ℕ, ∫⁻ t, F N t ∂μ := lintegral_iSup hFm hFmono
    _ = ⨆ N : ℕ, ∫⁻ t in heightWindow N, f t ∂μ := by
      apply iSup_congr
      intro N
      exact lintegral_indicator (heightWindow_measurable N) f

/-- Raw real norm-square of the ACTUAL test transform. -/
def actualEnergyReal (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℝ :=
  ‖kTestTransform P k t‖ ^ 2

def actualEnergyENN (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (actualEnergyReal P k t)

theorem actualEnergyReal_continuous (P : PacketData ι) (k : D4 → ℤ) :
    Continuous (actualEnergyReal P k) := by
  exact (kTestTransform_continuous P k).norm.pow 2

theorem actualEnergyENN_measurable (P : PacketData ι) (k : D4 → ℤ) :
    Measurable (actualEnergyENN P k) := by
  exact (actualEnergyReal_continuous P k).measurable.ennreal_ofReal

def fullCandidateEnergy (P : PacketData ι) (k : D4 → ℤ) : ℝ≥0∞ :=
  ∫⁻ t, actualEnergyENN P k t ∂candidateMeasure

def truncatedCandidateEnergy (P : PacketData ι) (k : D4 → ℤ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ t in heightWindow N, actualEnergyENN P k t ∂candidateMeasure

theorem truncatedCandidateEnergy_monotone (P : PacketData ι) (k : D4 → ℤ) :
    Monotone (truncatedCandidateEnergy P k) := by
  intro N M hNM
  exact lintegral_mono_set (heightWindow_monotone hNM)

theorem truncatedCandidateEnergy_le_full (P : PacketData ι)
    (k : D4 → ℤ) (N : ℕ) :
    truncatedCandidateEnergy P k N ≤ fullCandidateEnergy P k := by
  exact setLIntegral_le_lintegral (heightWindow N) (actualEnergyENN P k)

/-- Each compact truncation is finite; this is not a uniform bound in N. -/
theorem truncatedCandidateEnergy_lt_top (P : PacketData ι)
    (k : D4 → ℤ) (N : ℕ) : truncatedCandidateEnergy P k N < ∞ := by
  have hn : 0 ≤ᵐ[candidateMeasure.restrict (heightWindow N)] actualEnergyReal P k :=
    Filter.Eventually.of_forall (fun t => sq_nonneg ‖kTestTransform P k t‖)
  exact (hasFiniteIntegral_iff_ofReal hn).mp
    (actualK_candidateMeasure_energy_integrableOn_Icc P k (-(N : ℝ)) (N : ℝ)).hasFiniteIntegral

/-- Full nonnegative energy, possibly infinite, is exactly the truncation supremum. -/
theorem fullCandidateEnergy_eq_iSup (P : PacketData ι) (k : D4 → ℤ) :
    fullCandidateEnergy P k = ⨆ N : ℕ, truncatedCandidateEnergy P k N := by
  exact lintegral_eq_iSup_heightWindow candidateMeasure (actualEnergyENN_measurable P k)

theorem truncatedCandidateEnergy_tendsto (P : PacketData ι) (k : D4 → ℤ) :
    Tendsto (truncatedCandidateEnergy P k) atTop (𝓝 (fullCandidateEnergy P k)) := by
  rw [fullCandidateEnergy_eq_iSup]
  exact tendsto_atTop_iSup (truncatedCandidateEnergy_monotone P k)

/-- The same exhaustion for the real weighted energy, encoded nonnegatively. -/
theorem weightedEnergy_lintegral_eq_iSup (P : PacketData ι) (k : D4 → ℤ) :
    (∫⁻ t, ENNReal.ofReal (candidateEnergyDensity P k t)) =
      ⨆ N : ℕ, ∫⁻ t in heightWindow N,
        ENNReal.ofReal (candidateEnergyDensity P k t) := by
  exact lintegral_eq_iSup_heightWindow volume
    (candidateEnergyDensity_continuous P k).measurable.ennreal_ofReal

/-- This is only the explicit density change, valid even at infinite total energy. -/
theorem fullCandidateEnergy_eq_weighted_lintegral (P : PacketData ι) (k : D4 → ℤ) :
    fullCandidateEnergy P k =
      ∫⁻ t, ENNReal.ofReal (candidateEnergyDensity P k t) := by
  unfold fullCandidateEnergy candidateMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume candidateDensityENN_measurable
    (actualEnergyENN_measurable P k)]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    exact (ENNReal.ofReal_mul (candidateDensity_nonneg t)).symm)

/-- The necessary and sufficient extra condition is one common finite bound. -/
theorem fullCandidateEnergy_lt_top_iff_uniform_bound (P : PacketData ι)
    (k : D4 → ℤ) :
    fullCandidateEnergy P k < ∞ ↔
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ N : ℕ, truncatedCandidateEnergy P k N ≤ C := by
  constructor
  · intro h
    exact ⟨fullCandidateEnergy P k, h, truncatedCandidateEnergy_le_full P k⟩
  · rintro ⟨C, hC, hbound⟩
    rw [fullCandidateEnergy_eq_iSup]
    exact lt_of_le_of_lt (iSup_le hbound) hC

theorem actualEnergyReal_integrable_iff_full_lt_top (P : PacketData ι)
    (k : D4 → ℤ) :
    Integrable (actualEnergyReal P k) candidateMeasure ↔ fullCandidateEnergy P k < ∞ := by
  have hn : 0 ≤ᵐ[candidateMeasure] actualEnergyReal P k :=
    Filter.Eventually.of_forall (fun t => sq_nonneg ‖kTestTransform P k t‖)
  constructor
  · intro h
    exact (hasFiniteIntegral_iff_ofReal hn).mp h.hasFiniteIntegral
  · intro h
    exact ⟨(actualEnergyReal_continuous P k).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr h⟩

theorem weightedEnergy_integrable_iff_full_lt_top (P : PacketData ι)
    (k : D4 → ℤ) :
    Integrable (candidateEnergyDensity P k) ↔ fullCandidateEnergy P k < ∞ := by
  have hn : 0 ≤ᵐ[volume] candidateEnergyDensity P k :=
    Filter.Eventually.of_forall (candidateEnergyDensity_nonneg P k)
  rw [fullCandidateEnergy_eq_weighted_lintegral]
  constructor
  · intro h
    exact (hasFiniteIntegral_iff_ofReal hn).mp h.hasFiniteIntegral
  · intro h
    exact ⟨(candidateEnergyDensity_continuous P k).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).mpr h⟩

/-- Exact MemLp 2 exit criterion; the common finite bound is not supplied here. -/
theorem actualK_memLp_two_iff_uniform_bound (P : PacketData ι) (k : D4 → ℤ) :
    MemLp (kTestTransform P k) 2 candidateMeasure ↔
      ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ N : ℕ, truncatedCandidateEnergy P k N ≤ C := by
  rw [memLp_two_iff_integrable_sq_norm (kTestTransform_continuous P k).aestronglyMeasurable]
  exact (actualEnergyReal_integrable_iff_full_lt_top P k).trans
    (fullCandidateEnergy_lt_top_iff_uniform_bound P k)

theorem actualK_memLp_two_of_uniform_bound (P : PacketData ι) (k : D4 → ℤ)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hbound : ∀ N : ℕ, truncatedCandidateEnergy P k N ≤ C) :
    MemLp (kTestTransform P k) 2 candidateMeasure := by
  exact (actualK_memLp_two_iff_uniform_bound P k).mpr ⟨C, hC, hbound⟩

end
end ImbalancedChen.Part3.ActualKCandidateEnergyExhaustion20261024z
