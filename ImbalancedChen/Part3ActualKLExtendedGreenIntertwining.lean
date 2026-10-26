import ImbalancedChen.Part3ActualGreenKLCutoffConvergence
import ImbalancedChen.Part3ActualKLL2IsometryExtension
import ImbalancedChen.Part3ActualKLResolventMultiplier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual extended KL/Green intertwining. The SAME smooth compact cutoffs
converge physically to the actual Green output and have literal transform
limits. Continuity of the actual norm-preserving KL extension, followed by
the actual L2-to-a.e.-subsequence theorem, identifies its noncompact Green
output. The true dense compact core then extends the identity to all L2.

At kappa=1/2 the multiplier is the already defined concrete bounded raw-tau
coordinate map. Its invariance of the actual KL range is proved. There is
no assumed norm identity, intertwining equation, or surjectivity premise.
-/
namespace ImbalancedChen.Part3.ActualKLExtendedGreenIntertwining20261025a
noncomputable section
open Set MeasureTheory Filter Topology
open RadialSchrodingerL2Form20261025a ActualKLCoordinateMeasures20261025a
open ActualKLCoreTransform20261025a ActualKLCompactTestIntegrationByParts20261025a
open ActualGreenL2IntegralInverse20261025a ActualGreenKLCutoffConvergence20261025a
open ActualKLL2IsometryExtension20261025a ActualKLResolventCoordinate20261025a
open ActualKLResolventMultiplier20261025a

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual isometry's value on a noncompact Green output equals the
literal multiplier formula. The proof identifies limits of the same
explicit compact tests; it does not extend an integral by fiat. -/
theorem actualKL_green_smooth_ae {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialTest) :
    (actualKLIsometry (actualGreenL2Operator kappa hkappa hkappaUpper (radialCoreL2 F)) :
      ℝ → ℂ) =ᵐ[tauMeasure]
      (fun tau => actualKtransform F.function tau / ((kappa : ℂ)^2+(tau : ℂ)^2)) := by
  have hphysical := greenCutoffTest_physical_tendsto kappa hkappa hkappaUpper F
  have hKL := (actualKLIsometry.continuous.tendsto
    (actualGreenL2Operator kappa hkappa hkappaUpper (radialCoreL2 F))).comp hphysical
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hKL).exists_seq_tendsto_ae
  have hall : ∀ᵐ tau : ℝ ∂tauMeasure, ∀ n : ℕ,
      actualKLIsometry (radialCoreL2 (greenCutoffTest kappa hkappa hkappaUpper F n)) tau =
        actualKtransform (greenCutoffTest kappa hkappa hkappaUpper F n).function tau := by
    exact ae_all_iff.mpr (fun n => actualKLIsometry_on_test_ae
      (greenCutoffTest kappa hkappa hkappaUpper F n))
  filter_upwards [hae, hall, tauMeasure_positive_ae] with tau hr hrow htau
  have he : (fun i => actualKLIsometry
      (radialCoreL2 (greenCutoffTest kappa hkappa hkappaUpper F (ns i))) tau) =
      (fun i => actualKtransform
        (greenCutoffTest kappa hkappa hkappaUpper F (ns i)).function tau) :=
    funext (fun i => hrow (ns i))
  rw [he] at hr
  exact tendsto_nhds_unique hr
    ((greenCutoffTest_transform_resolvent_limit kappa hkappa hkappaUpper F tau htau.ne').comp
      hns.tendsto_atTop)

/-- Fixed genuine physical resolvent coordinate used by the range proof. -/
def halfGreenOperator : RadialL2 →L[ℂ] RadialL2 :=
  actualGreenL2Operator (1/2) (by norm_num) (by norm_num)

theorem actualKL_halfGreen_intertwine_core (F : RadialTest) :
    actualKLIsometry (halfGreenOperator (radialCoreL2 F)) =
      rawKLResolventMultiplier (actualKLIsometry (radialCoreL2 F)) := by
  apply Lp.ext
  have hleft := actualKL_green_smooth_ae (kappa := (1/2 : ℝ))
    (by norm_num) (by norm_num) F
  filter_upwards [hleft, rawKLResolventMultiplier_coe_ae
    (actualKLIsometry (radialCoreL2 F)), actualKLIsometry_on_test_ae F]
      with tau hl hm hf
  change actualKLIsometry (actualGreenL2Operator (1/2) (by norm_num) (by norm_num)
    (radialCoreL2 F)) tau = _
  rw [hl, hm, hf]
  have hden : (((1/4 : ℝ)+tau^2) : ℂ) =
      (((1/2 : ℝ) : ℂ)^2+(tau : ℂ)^2) := by
    push_cast
    norm_num
  rw [klResolventCoordinate, Complex.ofReal_inv, hden, div_eq_mul_inv, mul_comm]

/-- Full-L2 intertwining for the actual extension and the actual native
Green integral operator. Both sides are continuous on the physical space;
their equality is already proved on its actual dense compact core. -/
theorem actualKL_halfGreen_intertwine (F : RadialL2) :
    actualKLIsometry (halfGreenOperator F) =
      rawKLResolventMultiplier (actualKLIsometry F) := by
  have hclosed : IsClosed {u : RadialL2 |
      actualKLIsometry (halfGreenOperator u) = rawKLResolventMultiplier (actualKLIsometry u)} :=
    isClosed_eq (actualKLIsometry.continuous.comp halfGreenOperator.continuous)
      (rawKLResolventMultiplier.continuous.comp actualKLIsometry.continuous)
  have hsub : Set.range radialCoreL2 ⊆ {u : RadialL2 |
      actualKLIsometry (halfGreenOperator u) = rawKLResolventMultiplier (actualKLIsometry u)} := by
    rintro _ ⟨T, rfl⟩
    exact actualKL_halfGreen_intertwine_core T
  exact (closure_minimal hsub hclosed) (radialCoreL2_range_dense F)

theorem actualKLContinuous_halfGreen_intertwine :
    actualKLContinuous.comp halfGreenOperator = rawKLResolventMultiplier.comp actualKLContinuous := by
  apply ContinuousLinearMap.ext
  intro F
  exact actualKL_halfGreen_intertwine F

/-- The actual KL range is invariant under the concrete bounded injective
resolvent-coordinate multiplier. No range condition is assumed. -/
theorem rawKLResolventMultiplier_mem_actualKLRange {u : RawTauL2}
    (hu : u ∈ Set.range actualKLIsometry) :
    rawKLResolventMultiplier u ∈ Set.range actualKLIsometry := by
  obtain ⟨F, rfl⟩ := hu
  exact ⟨halfGreenOperator F, actualKL_halfGreen_intertwine F⟩

end
end ImbalancedChen.Part3.ActualKLExtendedGreenIntertwining20261025a
