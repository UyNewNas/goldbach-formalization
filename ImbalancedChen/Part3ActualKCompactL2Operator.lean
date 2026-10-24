import ImbalancedChen.Part3ActualKCompactHeightOperator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Operator.Extend

/-!
SOURCEONLY 20261024z. UNCOMPILED; no acceptance credit.

Assembly fragment after Part3ActualKRegionOperator.lean.txt and
Part3ActualKCompactHeightOperator.lean.txt. ROOT stages their dependencies
and adds Mathlib.MeasureTheory.Function.L2Space,
Mathlib.MeasureTheory.Function.ContinuousMapDense, and
Mathlib.Analysis.Normed.Operator.Extend as imports before this body.

The kernel is the actual K_{2it}(q)/q on the physical q interval. For
continuous input the integral equals a genuine L2 inner product against
the conjugate kernel. Cauchy-Schwarz and the real kernel sup bound give
the L2(q)-to-L2(t) estimate. Density extends this one actual operator.
-/

namespace ImbalancedChen.Part3.ActualKCompactL2OperatorSourceOnly

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.ImaginaryOrderKExplicitMajorantSourceOnly
  (restrictedKKernel restrictedKKernel_norm_le)
open ImbalancedChen.Part3.ActualKRegionOperatorSourceOnly
  (regionVolume regionVolume_univ regionVolume_real_univ kRegionFunctional)
open ImbalancedChen.Part3.ActualKCompactHeightOperatorSourceOnly
  (kCompactHeightOperator)
open P3ActualLiteralPacketIntegralSourceOnly

variable {ι : Type*}

/-- Lebesgue measure on the actual closed common-height subtype. -/
def heightVolume (T : ℝ) : Measure (Icc (-T) T) :=
  Measure.comap Subtype.val (volume : Measure ℝ)

theorem heightVolume_pushforward (T : ℝ) :
    (heightVolume T).map ((↑) : Icc (-T) T → ℝ) =
      (volume : Measure ℝ).restrict (Icc (-T) T) := by
  exact Measure.map_comap_subtype_coe
    (show MeasurableSet (Icc (-T) T) from measurableSet_Icc)
    (volume : Measure ℝ)

theorem heightVolume_univ (T : ℝ) :
    heightVolume T Set.univ = (volume : Measure ℝ) (Icc (-T) T) := by
  calc
    heightVolume T Set.univ =
        (volume : Measure ℝ) (((↑) : Icc (-T) T → ℝ) '' Set.univ) :=
      Measure.comap_subtype_coe_apply
        (show MeasurableSet (Icc (-T) T) from measurableSet_Icc)
        (volume : Measure ℝ) _
    _ = (volume : Measure ℝ) (Icc (-T) T) := by
      simp only [Set.image_univ, Subtype.range_coe]

theorem heightVolume_real_univ (T : ℝ) :
    (heightVolume T).real Set.univ =
      (volume : Measure ℝ).real (Icc (-T) T) := by
  simpa only [measureReal_def] using congrArg ENNReal.toReal (heightVolume_univ T)

private instance regionVolume_finiteL2 (P : PacketData ι) :
    IsFiniteMeasure (regionVolume P) :=
  ⟨by rw [regionVolume_univ]; exact isCompact_Icc.measure_lt_top⟩

private instance heightVolume_finite (T : ℝ) :
    IsFiniteMeasure (heightVolume T) :=
  ⟨by rw [heightVolume_univ]; exact isCompact_Icc.measure_lt_top⟩

/-- The numerical L2 embedding factor for a finite measure, expressed
using its real total mass. -/
private theorem toL2_mass_factor {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    ((measureUnivNNReal μ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ : ℝ) =
      Real.sqrt (μ.real Set.univ) := by
  rw [NNReal.coe_rpow, Real.sqrt_eq_rpow]
  change (μ Set.univ).toReal ^ ((2 : ℝ≥0∞).toReal)⁻¹ =
    (μ Set.univ).toReal ^ (1 / (2 : ℝ))
  norm_num

/-- Continuous functions enter the genuine L2 space for the physical
q-measure. -/
def regionToL2 (P : PacketData ι) :
    C(P.region, ℂ) →L[ℂ] Lp ℂ 2 (regionVolume P) :=
  ContinuousMap.toLp 2 (regionVolume P) ℂ

/-- Continuous functions enter L2 for the actual compact-height
Lebesgue measure. -/
def heightToL2 (T : ℝ) :
    C(Icc (-T) T, ℂ) →L[ℂ] Lp ℂ 2 (heightVolume T) :=
  ContinuousMap.toLp 2 (heightVolume T) ℂ

private theorem continuous_toL2_norm_le_mass {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopologyEither α ℂ] [CompactSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : C(α, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ≤
      Real.sqrt (μ.real Set.univ) * ‖f‖ := by
  have hOp :
      ‖(ContinuousMap.toLp 2 μ ℂ : C(α, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ ≤
        ((measureUnivNNReal μ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ : ℝ) :=
    ContinuousMap.toLp_norm_le μ
  rw [toL2_mass_factor μ] at hOp
  exact ((ContinuousMap.toLp 2 μ ℂ).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hOp (norm_nonneg _))

/-- The actual continuous-input integral is an L2 inner product against
the pointwise conjugate restricted K kernel. -/
theorem kRegionFunctional_eq_L2_inner (P : PacketData ι)
    (t : ℝ) (f : C(P.region, ℂ)) :
    kRegionFunctional P t f =
      inner ℂ
        (ContinuousMap.toLp 2 (regionVolume P) ℂ
          (star (restrictedKKernel P t)))
        (regionToL2 P f) := by
  change (∫ q : P.region, f q * restrictedKKernel P t q ∂regionVolume P) =
    inner ℂ
      (ContinuousMap.toLp 2 (regionVolume P) ℂ
        (star (restrictedKKernel P t)))
      (ContinuousMap.toLp 2 (regionVolume P) ℂ f)
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by
    simp [ContinuousMap.star_apply, Complex.star_def])

/-- Cauchy-Schwarz for the actual K integral. This uses the genuine
restrictedKKernel_norm_le and no spectral estimate. -/
theorem kRegionFunctional_L2_bound (P : PacketData ι)
    (t : ℝ) (f : C(P.region, ℂ)) :
    ‖kRegionFunctional P t f‖ ≤
      ((512 / P.Y0^2) *
        Real.sqrt ((volume : Measure ℝ).real P.region)) *
          ‖regionToL2 P f‖ := by
  have hK :
      ‖ContinuousMap.toLp 2 (regionVolume P) ℂ
          (star (restrictedKKernel P t))‖ ≤
        (512 / P.Y0^2) *
          Real.sqrt ((volume : Measure ℝ).real P.region) := by
    calc
      ‖ContinuousMap.toLp 2 (regionVolume P) ℂ
          (star (restrictedKKernel P t))‖ ≤
          Real.sqrt ((regionVolume P).real Set.univ) *
            ‖star (restrictedKKernel P t)‖ :=
        continuous_toL2_norm_le_mass (regionVolume P)
          (star (restrictedKKernel P t))
      _ = Real.sqrt ((volume : Measure ℝ).real P.region) *
            ‖restrictedKKernel P t‖ := by
        rw [regionVolume_real_univ, norm_star]
      _ ≤ Real.sqrt ((volume : Measure ℝ).real P.region) *
            (512 / P.Y0^2) :=
        mul_le_mul_of_nonneg_left (restrictedKKernel_norm_le P t)
          (Real.sqrt_nonneg _)
      _ = (512 / P.Y0^2) *
            Real.sqrt ((volume : Measure ℝ).real P.region) := mul_comm _ _
  rw [kRegionFunctional_eq_L2_inner]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

theorem kCompactHeightOperator_sup_L2_bound (P : PacketData ι)
    (T : ℝ) (f : C(P.region, ℂ)) :
    ‖kCompactHeightOperator P T f‖ ≤
      ((512 / P.Y0^2) *
        Real.sqrt ((volume : Measure ℝ).real P.region)) *
          ‖regionToL2 P f‖ := by
  have hC : 0 ≤
      ((512 / P.Y0^2) *
        Real.sqrt ((volume : Measure ℝ).real P.region)) *
          ‖regionToL2 P f‖ := by positivity
  apply (ContinuousMap.norm_le _ hC).mpr
  intro s
  change ‖kRegionFunctional P (s : ℝ) f‖ ≤ _
  exact kRegionFunctional_L2_bound P (s : ℝ) f

/-- The actual kernel first acts on continuous inputs, now measured in
L2 on both real variables. -/
def continuousInputL2Map (P : PacketData ι) (T : ℝ) :
    C(P.region, ℂ) →ₗ[ℂ] Lp ℂ 2 (heightVolume T) :=
  (heightToL2 T).toLinearMap.comp
    (kCompactHeightOperator P T).toLinearMap

/-- The exact Cauchy-Schwarz operator cost for continuous inputs. -/
theorem continuousInputL2_bound (P : PacketData ι) (T : ℝ)
    (f : C(P.region, ℂ)) :
    ‖continuousInputL2Map P T f‖ ≤
      (((512 / P.Y0^2) *
        Real.sqrt ((volume : Measure ℝ).real P.region)) *
        Real.sqrt ((volume : Measure ℝ).real (Icc (-T) T))) *
          ‖regionToL2 P f‖ := by
  calc
    ‖continuousInputL2Map P T f‖ =
        ‖heightToL2 T (kCompactHeightOperator P T f)‖ := rfl
    _ ≤ Real.sqrt ((heightVolume T).real Set.univ) *
          ‖kCompactHeightOperator P T f‖ :=
        continuous_toL2_norm_le_mass (heightVolume T)
          (kCompactHeightOperator P T f)
    _ ≤ Real.sqrt ((volume : Measure ℝ).real (Icc (-T) T)) *
          (((512 / P.Y0^2) *
            Real.sqrt ((volume : Measure ℝ).real P.region)) *
              ‖regionToL2 P f‖) := by
        rw [heightVolume_real_univ]
        exact mul_le_mul_of_nonneg_left
          (kCompactHeightOperator_sup_L2_bound P T f)
          (Real.sqrt_nonneg _)
    _ = (((512 / P.Y0^2) *
          Real.sqrt ((volume : Measure ℝ).real P.region)) *
          Real.sqrt ((volume : Measure ℝ).real (Icc (-T) T))) *
            ‖regionToL2 P f‖ := by ring

/-- Continuous functions are dense in the physical L2(q) space for the
actual transported Lebesgue measure. -/
theorem regionToL2_denseRange (P : PacketData ι) :
    DenseRange (regionToL2 P) := by
  exact ContinuousMap.toLp_denseRange
    (E := ℂ) (μ := regionVolume P) (𝕜 := ℂ)
    (p := (2 : ℝ≥0∞)) (by norm_num)

/-- The bounded L2(q) to L2(t) operator is the unique continuous
extension of the integral operator on continuous functions. -/
def kCompactL2Operator (P : PacketData ι) (T : ℝ) :
    Lp ℂ 2 (regionVolume P) →L[ℂ] Lp ℂ 2 (heightVolume T) :=
  (continuousInputL2Map P T).extendOfNorm (regionToL2 P).toLinearMap

theorem kCompactL2Operator_norm_le (P : PacketData ι) (T : ℝ) :
    ‖kCompactL2Operator P T‖ ≤
      ((512 / P.Y0^2) *
        Real.sqrt ((volume : Measure ℝ).real P.region)) *
          Real.sqrt ((volume : Measure ℝ).real (Icc (-T) T)) := by
  exact LinearMap.opNorm_extendOfNorm_le
    (regionToL2_denseRange P)
    (by positivity)
    (continuousInputL2_bound P T)

/-- On every continuous input, the extension still is exactly the
original K_{2it}(q)/q integral, now represented in L2(t). -/
theorem kCompactL2Operator_regionToL2 (P : PacketData ι)
    (T : ℝ) (f : C(P.region, ℂ)) :
    kCompactL2Operator P T (regionToL2 P f) =
      heightToL2 T (kCompactHeightOperator P T f) := by
  exact LinearMap.extendOfNorm_eq
    (regionToL2_denseRange P)
    ⟨((512 / P.Y0^2) *
        Real.sqrt ((volume : Measure ℝ).real P.region)) *
          Real.sqrt ((volume : Measure ℝ).real (Icc (-T) T)),
      continuousInputL2_bound P T⟩ f

end
end ImbalancedChen.Part3.ActualKCompactL2OperatorSourceOnly
