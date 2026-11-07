import ImbalancedChen.Part3ActualKTransformContinuity
import ImbalancedChen.Part3ActualKHeightFourierTail
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact

/-!
SOURCE_WRITTEN / UNCOMPILED / NOT ROOT_ACCEPTED, 2026-10-24.

This is the actual physical packet at one common spectral height, with its
original completed m interval, coprime signed coefficient and all Fourier
modes. The first two imports are candidate dependencies delivered in this
same exclusive draft tree. They must be installed under those names before
this module can be compiled. No such installation or compilation is done
here. No Fourier decay, continuity, kernel estimate or desired spectral
large-sieve estimate is supplied as a premise.

The integration in height below is explicitly compact Lebesgue integration,
with an explicitly chosen continuous weight. This is not an assertion of
Kuznetsov, automorphic Plancherel or a spectral saving. In particular there
is no identification of this measure with an Eisenstein or cusp measure.
-/

namespace ImbalancedChen.Part3.ActualCompactHeightSeries20261024z

noncomputable section

open Classical Set MeasureTheory Filter
open scoped BigOperators Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualKTransformContinuity20261024z
open ActualKHeightFourierTail20261024z

variable {ι : Type*}

/-- The candidate's explicit absolute interchange budget is nonnegative. -/
theorem heightFourierBudget_nonneg (P : PacketData ι) :
    0 ≤ heightFourierBudget P := by
  unfold heightFourierBudget
  exact mul_nonneg
    (mul_nonneg (coefficientMass_nonneg P) (by positivity))
    ENNReal.toReal_nonneg

/-- Exact coefficient reconstruction, including all Fourier frequencies. -/
theorem heightPhysicalIntegral_hasSum (P : PacketData ι) (t : ℝ) (J0 : ℕ) :
    HasSum (heightFourierTerm P t) (heightPhysicalIntegral P t) := by
  exact k_hasSum_coefficient_times_modeIntegral P (commonHeight t) J0

/-- Here the actual test transform is multiplied by the actual completed
packet sum. Neither factor is replaced by a free spectral array. -/
theorem heightFourierTerm_eq_actual_transform (P : PacketData ι)
    (t : ℝ) (k : D4 → ℤ) :
    heightFourierTerm P t k = actualCoeff P.rho P.sigma k *
      (kTestTransform P k t * completedPacketSum P k) := by
  unfold heightFourierTerm
  rw [actual_common_height_modeIntegral]

theorem heightFourierTerm_continuous (P : PacketData ι) (k : D4 → ℤ) :
    Continuous (fun t : ℝ => heightFourierTerm P t k) := by
  simp only [heightFourierTerm_eq_actual_transform]
  exact continuous_const.mul ((kTestTransform_continuous P k).mul continuous_const)

/-- The actual physical integral is continuous in the common height. This
uses the genuine summable Fourier majorant, uniformly over all real t. -/
theorem heightPhysicalIntegral_continuous (P : PacketData ι) :
    Continuous (heightPhysicalIntegral P) := by
  have heq : heightPhysicalIntegral P =
      fun t : ℝ => ∑' k : D4 → ℤ, heightFourierTerm P t k := by
    funext t
    exact (heightPhysicalIntegral_hasSum P t 0).tsum_eq.symm
  rw [heq]
  exact continuous_tsum (heightFourierTerm_continuous P)
    ((P.actual_norm_summable 0).mul_right (heightFourierBudget P))
    (fun k t => heightFourierTerm_norm_le P t k)

/-- The compact height-weight supremum is the real continuous-map norm,
not an independently assumed analytic bound. Empty height intervals are
also allowed; the corresponding set integrals are zero. -/
def heightWeightRestriction (w : C(ℝ, ℂ)) (T : ℝ) : C(Icc (-T) T, ℂ) :=
  w.comp ⟨Subtype.val, continuous_subtype_val⟩

def heightWeightBound (w : C(ℝ, ℂ)) (T : ℝ) : ℝ :=
  ‖heightWeightRestriction w T‖

theorem heightWeightBound_nonneg (w : C(ℝ, ℂ)) (T : ℝ) :
    0 ≤ heightWeightBound w T := norm_nonneg _

theorem norm_weight_le (w : C(ℝ, ℂ)) (T t : ℝ) (ht : t ∈ Icc (-T) T) :
    ‖w t‖ ≤ heightWeightBound w T := by
  exact (heightWeightRestriction w T).norm_coe_le_norm ⟨t, ht⟩

theorem weighted_heightFourierTerm_norm_le (P : PacketData ι)
    (w : C(ℝ, ℂ)) (T t : ℝ) (ht : t ∈ Icc (-T) T) (k : D4 → ℤ) :
    ‖w t * heightFourierTerm P t k‖ ≤
      ‖actualCoeff P.rho P.sigma k‖ *
        (heightFourierBudget P * heightWeightBound w T) := by
  rw [norm_mul]
  calc
    ‖w t‖ * ‖heightFourierTerm P t k‖ ≤
        heightWeightBound w T *
          (‖actualCoeff P.rho P.sigma k‖ * heightFourierBudget P) :=
      mul_le_mul (norm_weight_le w T t ht)
        (heightFourierTerm_norm_le P t k) (norm_nonneg _)
        (heightWeightBound_nonneg w T)
    _ = _ := by ring

/-- Both actual functions are genuinely integrable on every compact height
interval. Continuity was proved above; it is not part of PacketData. -/
theorem weighted_heightPhysicalIntegral_integrableOn (P : PacketData ι)
    (w : C(ℝ, ℂ)) (T : ℝ) :
    IntegrableOn (fun t => w t * heightPhysicalIntegral P t) (Icc (-T) T) := by
  exact ((w.continuous.mul (heightPhysicalIntegral_continuous P)).continuousOn)
    .integrableOn_compact isCompact_Icc

theorem weighted_heightFourierTerm_integrableOn (P : PacketData ι)
    (w : C(ℝ, ℂ)) (T : ℝ) (k : D4 → ℤ) :
    IntegrableOn (fun t => w t * heightFourierTerm P t k) (Icc (-T) T) := by
  exact ((w.continuous.mul (heightFourierTerm_continuous P k)).continuousOn)
    .integrableOn_compact isCompact_Icc

/-- Main actual finite-to-integral connection: the original Fourier
reconstruction commutes with compact height integration, including every
coprime coefficient, common m phase and physical dq/q factor. -/
theorem weighted_compact_height_hasSum (P : PacketData ι)
    (w : C(ℝ, ℂ)) (T : ℝ) (J0 : ℕ) :
    HasSum
      (fun k : D4 → ℤ =>
        ∫ t in Icc (-T) T, w t * heightFourierTerm P t k)
      (∫ t in Icc (-T) T, w t * heightPhysicalIntegral P t) := by
  let μ : Measure ℝ := volume.restrict (Icc (-T) T)
  have hfin : (volume : Measure ℝ) (Icc (-T) T) < ⊤ :=
    isCompact_Icc.measure_lt_top
  let : IsFiniteMeasure μ :=
    ⟨by simpa only [μ, Measure.restrict_apply_univ] using hfin⟩
  have hs := (P.actual_norm_summable J0).mul_right
    (heightFourierBudget P * heightWeightBound w T)
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun k _t => ‖actualCoeff P.rho P.sigma k‖ *
      (heightFourierBudget P * heightWeightBound w T))
  · intro k
    exact (w.continuous.mul (heightFourierTerm_continuous P k)).aestronglyMeasurable
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact weighted_heightFourierTerm_norm_le P w T t ht k
  · exact Filter.Eventually.of_forall (fun _t => hs)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun t =>
      (heightPhysicalIntegral_hasSum P t J0).mul_left (w t))

/-- The actual target form of the preceding exchange, displaying the
K test transform and the frozen completed-packet coefficient separately. -/
theorem actual_weighted_compact_height_transform_hasSum (P : PacketData ι)
    (w : C(ℝ, ℂ)) (T : ℝ) (J0 : ℕ) :
    HasSum
      (fun k : D4 → ℤ => actualCoeff P.rho P.sigma k *
        ((∫ t in Icc (-T) T, w t * kTestTransform P k t) *
          completedPacketSum P k))
      (∫ t in Icc (-T) T,
        w t * ∫ q : ℝ, kPhysical P (commonHeight t) q) := by
  apply (weighted_compact_height_hasSum P w T J0).congr_fun
  intro k
  rw [show (fun t : ℝ => w t * heightFourierTerm P t k) =
      (fun t : ℝ => actualCoeff P.rho P.sigma k *
        ((w t * kTestTransform P k t) * completedPacketSum P k)) by
    funext t
    rw [heightFourierTerm_eq_actual_transform]
    ring]
  rw [integral_const_mul, integral_mul_const]

/-- An explicit compact-height absolute budget. It retains the complete
coefficient mass, actual Fourier weight, q-volume, height volume and weight
supremum. It is solely an interchange budget, with no spectral gain. -/
theorem norm_weighted_compact_heightIntegral_le (P : PacketData ι)
    (w : C(ℝ, ℂ)) (T : ℝ) (J0 : ℕ) :
    ‖∫ t in Icc (-T) T, w t * heightPhysicalIntegral P t‖ ≤
      P3ActualWeightedSpectralBudgetSourceOnly.actualW P.rho P.sigma J0 *
        heightFourierBudget P * heightWeightBound w T *
          (volume : Measure ℝ).real (Icc (-T) T) := by
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  intro t ht
  rw [norm_mul]
  have hphysical := k_norm_fullIntegral_le P (commonHeight t) J0
  change ‖heightPhysicalIntegral P t‖ ≤ _ at hphysical
  have hb : ‖heightPhysicalIntegral P t‖ ≤
      P3ActualWeightedSpectralBudgetSourceOnly.actualW P.rho P.sigma J0 *
        heightFourierBudget P := by
    simpa only [heightFourierBudget, P.region_measure, mul_assoc] using hphysical
  calc
    ‖w t‖ * ‖heightPhysicalIntegral P t‖ ≤
        heightWeightBound w T *
          (P3ActualWeightedSpectralBudgetSourceOnly.actualW P.rho P.sigma J0 *
            heightFourierBudget P) :=
      mul_le_mul (norm_weight_le w T t ht) hb (norm_nonneg _)
        (heightWeightBound_nonneg w T)
    _ = _ := by ring

end
end ImbalancedChen.Part3.ActualCompactHeightSeries20261024z
