import ImbalancedChen.Part3ActualKRegionOperator
import ImbalancedChen.Part3ActualKRestrictedKernelContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCEONLY 20261024z. UNCOMPILED; no acceptance credit.

Assembly fragment after Part3ActualKRegionOperator.lean.txt and the sibling
Part3ActualKRestrictedKernelContinuity.lean.txt. ROOT should stage those as
modules and place their imports before this source. There are deliberately
no imports of draft-only module names here.

This upgrades the actual fixed-height K/q integral functional to a bounded
map into continuous functions on a compact interval of common heights.
The proof uses the sibling's proved continuity of the actual restricted K
kernel in C(P.region, ℂ), and the existing fixed-height operator norm.
No spectral measure or Parseval claim is made.
-/

namespace ImbalancedChen.Part3.ActualKCompactHeightOperatorSourceOnly

noncomputable section

open Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3.ImaginaryOrderKExplicitMajorantSourceOnly (restrictedKKernel)
open ImbalancedChen.Part3.ActualKRegionOperatorSourceOnly
  (regionVolume regionVolume_univ kRegionFunctional kRegionFunctional_norm_le
   restrictedSpectralTest kRegionFunctional_restrictedSpectralTest_eq_kTestTransform)
open ImbalancedChen.Part3.ActualKRestrictedKernelContinuity20261024z
  (restrictedKKernel_joint_continuous)
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly (kTestTransform)

variable {ι : Type*}

/-- The actual integral varies continuously with common height for every
continuous input on the physical region. -/
theorem kRegionFunctional_value_continuous (P : PacketData ι)
    (f : C(P.region, ℂ)) :
    Continuous (fun t : ℝ => kRegionFunctional P t f) := by
  letI : IsFiniteMeasure (regionVolume P) :=
    ⟨by rw [regionVolume_univ]; exact isCompact_Icc.measure_lt_top⟩
  have hjoint : Continuous (fun p : ℝ × P.region =>
      f p.2 * restrictedKKernel P p.1 p.2) :=
    (f.continuous.comp continuous_snd).mul
      (restrictedKKernel_joint_continuous P)
  have hparam : Continuous (fun t : ℝ =>
      ∫ q in (Set.univ : Set P.region),
        f q * restrictedKKernel P t q ∂regionVolume P) :=
    continuous_parametric_integral_of_continuous
      (f := fun t (q : P.region) => f q * restrictedKKernel P t q)
      hjoint isCompact_univ
  change Continuous (fun t : ℝ =>
    ∫ q : P.region, f q * restrictedKKernel P t q ∂regionVolume P)
  simpa only [setIntegral_univ] using hparam

/-- The actual compact-height operator before adding its uniform bound. -/
def kCompactHeightLinearMap (P : PacketData ι) (T : ℝ) :
    C(P.region, ℂ) →ₗ[ℂ] C(Icc (-T) T, ℂ) where
  toFun f :=
    ⟨fun s : Icc (-T) T => kRegionFunctional P (s : ℝ) f,
      (kRegionFunctional_value_continuous P f).comp continuous_subtype_val⟩
  map_add' f g := by
    ext s
    exact map_add (kRegionFunctional P (s : ℝ)) f g
  map_smul' c f := by
    ext s
    exact map_smul (kRegionFunctional P (s : ℝ)) c f

theorem kCompactHeightLinearMap_bound (P : PacketData ι) (T : ℝ)
    (f : C(P.region, ℂ)) :
    ‖kCompactHeightLinearMap P T f‖ ≤
      ((512 / P.Y0^2) * (volume : Measure ℝ).real P.region) * ‖f‖ := by
  have hcost : 0 ≤ (512 / P.Y0^2) * (volume : Measure ℝ).real P.region :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  apply (ContinuousMap.norm_le _ (mul_nonneg hcost (norm_nonneg f))).mpr
  intro s
  change ‖kRegionFunctional P (s : ℝ) f‖ ≤
    ((512 / P.Y0^2) * (volume : Measure ℝ).real P.region) * ‖f‖
  exact (kRegionFunctional P (s : ℝ)).le_of_opNorm_le
    (kRegionFunctional_norm_le P (s : ℝ)) f

/-- C(P.region, ℂ) to continuous height functions on the closed interval;
the same majorant works for every height, including T=0 or T<0. -/
def kCompactHeightOperator (P : PacketData ι) (T : ℝ) :
    C(P.region, ℂ) →L[ℂ] C(Icc (-T) T, ℂ) :=
  (kCompactHeightLinearMap P T).mkContinuous
    ((512 / P.Y0^2) * (volume : Measure ℝ).real P.region)
    (kCompactHeightLinearMap_bound P T)

theorem kCompactHeightOperator_norm_le (P : PacketData ι) (T : ℝ) :
    ‖kCompactHeightOperator P T‖ ≤
      (512 / P.Y0^2) * (volume : Measure ℝ).real P.region := by
  exact LinearMap.mkContinuous_norm_le (kCompactHeightLinearMap P T)
    (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    (kCompactHeightLinearMap_bound P T)

/-- Exact value of the compact-height operator on the actual spectralTest
restriction, with no change of K normalization or physical scale. -/
theorem kCompactHeightOperator_restrictedSpectralTest_apply
    (P : PacketData ι) (T : ℝ) (k : D4 → ℤ) (s : Icc (-T) T) :
    kCompactHeightOperator P T (restrictedSpectralTest P k) s =
      kTestTransform P k (s : ℝ) := by
  change kRegionFunctional P (s : ℝ) (restrictedSpectralTest P k) = _
  exact kRegionFunctional_restrictedSpectralTest_eq_kTestTransform P k (s : ℝ)

/-- The preceding value identity itself supplies continuity of the actual
transform when restricted to the compact height interval. -/
theorem kTestTransform_continuous_compact_height
    (P : PacketData ι) (T : ℝ) (k : D4 → ℤ) :
    Continuous (fun s : Icc (-T) T => kTestTransform P k (s : ℝ)) := by
  have he : (fun s : Icc (-T) T => kTestTransform P k (s : ℝ)) =
      (fun s : Icc (-T) T =>
        kCompactHeightOperator P T (restrictedSpectralTest P k) s) := by
    funext s
    exact (kCompactHeightOperator_restrictedSpectralTest_apply P T k s).symm
  rw [he]
  exact (kCompactHeightOperator P T (restrictedSpectralTest P k)).continuous

theorem kCompactHeightOperator_restrictedSpectralTest_eq
    (P : PacketData ι) (T : ℝ) (k : D4 → ℤ) :
    kCompactHeightOperator P T (restrictedSpectralTest P k) =
      (⟨fun s : Icc (-T) T => kTestTransform P k (s : ℝ),
        kTestTransform_continuous_compact_height P T k⟩ :
          C(Icc (-T) T, ℂ)) := by
  ext s
  exact kCompactHeightOperator_restrictedSpectralTest_apply P T k s

end
end ImbalancedChen.Part3.ActualKCompactHeightOperatorSourceOnly
