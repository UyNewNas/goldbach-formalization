import ImbalancedChen.Part3KLDensityMeasure
import ImbalancedChen.Part3ActualKTransformContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-24.

A finite-height parity reduction for the ACTUAL K_{2it}(q) dq/q test
transform and the explicitly defined candidate density t*sinh(2*pi*t).
Continuity is supplied by the concrete actual-transform continuity module.
No transform norm equality or spectral identification is asserted.
The withDensity identities below are changes of measure for this candidate,
not a Kontorovich--Lebedev or Kuznetsov Plancherel theorem.
-/

namespace ImbalancedChen.Part3.ActualKCompactEvenEnergy20261024z
noncomputable section

open Set MeasureTheory Filter
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualKTransformContinuity20261024z
open P3KLDensityMeasureSourceOnly

variable {ι : Type*}

/-- Direct parity proof from the actual integral K realization. -/
theorem actualKTransform_neg_height (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k (-t) = kTestTransform P k t := by
  unfold kTestTransform
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by rw [imaginaryOrderK_neg])

/-- The candidate-weighted energy density uses the actual transform. -/
def candidateEnergyDensity (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) : ℝ :=
  candidateDensity t * ‖kTestTransform P k t‖ ^ 2

theorem candidateEnergyDensity_continuous (P : PacketData ι) (k : D4 → ℤ) :
    Continuous (candidateEnergyDensity P k) := by
  exact candidateDensity_continuous.mul ((kTestTransform_continuous P k).norm.pow 2)

@[simp] theorem candidateEnergyDensity_neg (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    candidateEnergyDensity P k (-t) = candidateEnergyDensity P k t := by
  unfold candidateEnergyDensity
  rw [candidateDensity_neg, actualKTransform_neg_height]

theorem candidateEnergyDensity_nonneg (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) : 0 ≤ candidateEnergyDensity P k t := by
  exact mul_nonneg (candidateDensity_nonneg t) (sq_nonneg _)

theorem candidateEnergyDensity_integrableOn_Icc (P : PacketData ι)
    (k : D4 → ℤ) (a b : ℝ) :
    IntegrableOn (candidateEnergyDensity P k) (Icc a b) := by
  exact (candidateEnergyDensity_continuous P k).continuousOn.integrableOn_compact
    isCompact_Icc

/-- The interval argument explicitly removes only volume-null endpoints. -/
private theorem integral_Icc_even {f : ℝ → ℝ} (hc : Continuous f)
    (he : ∀ t : ℝ, f (-t) = f t) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Icc (-T) T, f t) = 2 * ∫ t in Icc 0 T, f t := by
  have hfull : (∫ t in Icc (-T) T, f t) = ∫ t in (-T)..T, f t := by
    rw [integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hhalf : (∫ t in Icc 0 T, f t) = ∫ t in 0..T, f t := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hT]
  have hneg : (∫ t in (-T)..0, f t) = ∫ t in 0..T, f t := by
    calc
      (∫ t in (-T)..0, f t) = ∫ t in 0..T, f (-t) := by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := T)).symm
      _ = ∫ t in 0..T, f t := by simp only [he]
  rw [hfull, hhalf]
  calc
    (∫ t in (-T)..T, f t) =
        (∫ t in (-T)..0, f t) + ∫ t in 0..T, f t :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (-T) 0) (hc.intervalIntegrable 0 T)).symm
    _ = 2 * ∫ t in 0..T, f t := by rw [hneg]; ring

/-- The actual weighted transform energy on [-T,T] is twice its positive half. -/
theorem actualK_candidateEnergy_Icc (P : PacketData ι) (k : D4 → ℤ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Icc (-T) T,
      candidateDensity t * ‖kTestTransform P k t‖ ^ 2) =
      2 * ∫ t in Icc 0 T,
        candidateDensity t * ‖kTestTransform P k t‖ ^ 2 := by
  exact integral_Icc_even (candidateEnergyDensity_continuous P k)
    (candidateEnergyDensity_neg P k) hT

@[simp] theorem candidateDensityENN_toReal (t : ℝ) :
    (candidateDensityENN t).toReal = candidateDensity t := by
  exact ENNReal.toReal_ofReal (candidateDensity_nonneg t)

/-- An actual change-of-measure identity for any measurable height set. -/
theorem actualK_candidateMeasure_energy_eq (P : PacketData ι) (k : D4 → ℤ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ t in s, ‖kTestTransform P k t‖ ^ 2 ∂candidateMeasure) =
      ∫ t in s, candidateEnergyDensity P k t := by
  have hf : ∀ᵐ t ∂volume.restrict s, candidateDensityENN t < ∞ :=
    Filter.Eventually.of_forall (fun t =>
      lt_top_iff_ne_top.mpr (candidateDensityENN_ne_top t))
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul
    candidateDensityENN_measurable hf (fun t => ‖kTestTransform P k t‖ ^ 2) hs
  simpa only [candidateMeasure, candidateDensityENN_toReal, smul_eq_mul,
    candidateEnergyDensity] using h

/-- Candidate-measure compact energy integrability follows from proven
continuity and the density identity, with no spectral assumption. -/
theorem actualK_candidateMeasure_energy_integrableOn_Icc (P : PacketData ι)
    (k : D4 → ℤ) (a b : ℝ) :
    IntegrableOn (fun t => ‖kTestTransform P k t‖ ^ 2) (Icc a b) candidateMeasure := by
  unfold IntegrableOn
  rw [candidateMeasure, restrict_withDensity measurableSet_Icc]
  have hf : ∀ᵐ t ∂volume.restrict (Icc a b), candidateDensityENN t < ∞ :=
    Filter.Eventually.of_forall (fun t =>
      lt_top_iff_ne_top.mpr (candidateDensityENN_ne_top t))
  apply (integrable_withDensity_iff_integrable_smul'
    candidateDensityENN_measurable hf).mpr
  simpa only [candidateDensityENN_toReal, smul_eq_mul, candidateEnergyDensity] using
    (candidateEnergyDensity_integrableOn_Icc P k a b)

/-- The corresponding integral identity for the explicitly defined measure. -/
theorem actualK_candidateMeasure_energy_Icc (P : PacketData ι) (k : D4 → ℤ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Icc (-T) T, ‖kTestTransform P k t‖ ^ 2 ∂candidateMeasure) =
      2 * ∫ t in Icc 0 T, ‖kTestTransform P k t‖ ^ 2 ∂candidateMeasure := by
  rw [actualK_candidateMeasure_energy_eq P k measurableSet_Icc,
    actualK_candidateMeasure_energy_eq P k measurableSet_Icc]
  exact actualK_candidateEnergy_Icc P k hT

end
end ImbalancedChen.Part3.ActualKCompactEvenEnergy20261024z
