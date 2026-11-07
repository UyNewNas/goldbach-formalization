import ImbalancedChen.Part3ActualZeroMeanCylinderFourierUnitary
import ImbalancedChen.Part3NonzeroModeKLHilbertSum
import ImbalancedChen.Part3WeightedHeightNativeUnitary
import ImbalancedChen.Part3CuspCylinderBesselMode

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual whole-cylinder zero-mean Fourier--KL unitary. Three independently
proved native maps are composed: the onto cylinder Fourier map, the
mode-dependent weighted-height Liouville map, and the actual onto KL map.
The modal height scale is exactly a_n=2*pi*|n|. The transverse circle has
period one and Haar mass one. The spectral Hilbert sum uses counting in
n!=0 and tauMeasure=(2/pi^2)*tau*sinh(pi*tau) d tau on tau>0.

No target norm, basis, onto, or spectral-decomposition premise appears.
This theorem is for the entire cylinder. It neither specifies a boundary
operator on a truncated cusp nor identifies a Gamma-quotient spectrum or
the automorphic dt/cosh(pi*t) normalization.
-/

namespace ImbalancedChen.Part3.ActualNonzeroCylinderKLUnitary20261026a
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z CuspCylinderBesselMode20261024z
open ActualCylinderModeEmbeddings20261026a ActualCylinderFourierCoefficients20261026a
open ActualZeroMeanCylinderFourierUnitary20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open NonzeroModeKLHilbertSum20261026a
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLOntoUnitary20261025a
open WeightedHeightNativeUnitary20261026a (weightedHeightUnitary)

def modeLiouville (n : NonzeroMode) : HeightL2 ≃ₗᵢ[ℂ] RadialL2 :=
  weightedHeightUnitary (frequencyScale n) (frequencyScale_pos n.property)

private def heightModesForward (f : NonzeroHeightModes) : NonzeroRadialModes :=
  ⟨fun n => modeLiouville n (f n),
    (lp.memℓp f).mono' (fun n => ((modeLiouville n).norm_map (f n)).le)⟩

private def heightModesInverse (g : NonzeroRadialModes) : NonzeroHeightModes :=
  ⟨fun n => (modeLiouville n).symm (g n),
    (lp.memℓp g).mono' (fun n => ((modeLiouville n).symm.norm_map (g n)).le)⟩

/-- Onto assembly of the actual n-dependent height-to-radial maps. -/
def heightModesToRadial : NonzeroHeightModes ≃ₗᵢ[ℂ] NonzeroRadialModes where
  toFun := heightModesForward
  invFun := heightModesInverse
  left_inv f := by
    ext n
    exact (modeLiouville n).symm_apply_apply (f n)
  right_inv g := by
    ext n
    exact (modeLiouville n).apply_symm_apply (g n)
  map_add' f g := by
    ext n
    exact (modeLiouville n).map_add (f n) (g n)
  map_smul' c f := by
    ext n
    exact (modeLiouville n).map_smul c (f n)
  norm_map' f := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun n => ((modeLiouville n).norm_map (f n)).le)
    · exact lp.norm_mono (by norm_num) (fun n => ((modeLiouville n).norm_map (f n)).ge)

theorem heightModesToRadial_apply (f : NonzeroHeightModes) (n : NonzeroMode) :
    heightModesToRadial f n = modeLiouville n (f n) := rfl

theorem heightModesToRadial_symm_apply (g : NonzeroRadialModes) (n : NonzeroMode) :
    heightModesToRadial.symm g n = (modeLiouville n).symm (g n) := rfl

/-- The actual unitary on the entire zero-horizontal-mean cylinder. -/
def actualCylinderKL : zeroMeanCylinder ≃ₗᵢ[ℂ] NonzeroSpectralModes :=
  actualCylinderFourier.trans (heightModesToRadial.trans nonzeroModeKL)

theorem actualCylinderKL_apply (F : zeroMeanCylinder) (n : NonzeroMode) :
    actualCylinderKL F n = actualKLUnitary
      (modeLiouville n (cylinderCoefficient n (F : CylinderL2))) := by
  change actualKLUnitary (modeLiouville n (actualCylinderFourier F n)) = _
  rw [actualCylinderFourier_apply]

theorem actualCylinderKL_surjective : Function.Surjective actualCylinderKL :=
  actualCylinderKL.surjective

theorem actualCylinderKL_norm (F : zeroMeanCylinder) :
    ‖actualCylinderKL F‖ = ‖(F : CylinderL2)‖ := actualCylinderKL.norm_map F

theorem actualCylinderKL_hasSum_energy (F : zeroMeanCylinder) :
    HasSum (fun n : NonzeroMode => ‖actualCylinderKL F n‖ ^ 2)
      ‖(F : CylinderL2)‖ ^ 2 := by
  have h : HasSum (fun n : NonzeroMode => ‖actualCylinderKL F n‖ ^ 2)
      ‖actualCylinderKL F‖ ^ 2 := by
    apply_mod_cast lp.hasSum_norm (by norm_num) (actualCylinderKL F)
  simpa only [actualCylinderKL_norm] using h

private theorem scalarL2_norm_sq_integral {X : Type*} [MeasurableSpace X]
    {mu : Measure X} (u : Lp ℂ 2 mu) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂mu := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  rw [integral_ofReal] at h
  exact Complex.ofReal_injective h

/-- Actual cylinder Parseval with the literal raw KL density displayed.
There is no circle-width correction at period one. -/
theorem actualCylinderKL_parseval (F : zeroMeanCylinder) :
    (∑' n : NonzeroMode, ∫ tau : ℝ, ‖actualCylinderKL F n tau‖ ^ 2
      ∂(((volume : Measure ℝ).restrict (Ioi 0)).withDensity
        (fun tau => ENNReal.ofReal ((2 / Real.pi ^ 2) * tau * Real.sinh (Real.pi * tau))))) =
      ∫ z : CuspCylinder, ‖(F : CylinderL2) z‖ ^ 2 ∂cylinderMeasure := by
  change (∑' n : NonzeroMode, ∫ tau : ℝ, ‖actualCylinderKL F n tau‖ ^ 2 ∂tauMeasure) = _
  calc
    _ = ∑' n : NonzeroMode, ‖actualCylinderKL F n‖ ^ 2 := by
      apply tsum_congr
      intro n
      exact (scalarL2_norm_sq_integral (actualCylinderKL F n)).symm
    _ = ‖(F : CylinderL2)‖ ^ 2 := (actualCylinderKL_hasSum_energy F).tsum_eq
    _ = _ := scalarL2_norm_sq_integral (F : CylinderL2)

theorem actualCylinderKL_inverse_fourier (a : NonzeroSpectralModes) (n : NonzeroMode) :
    actualCylinderFourier (actualCylinderKL.symm a) n =
      (modeLiouville n).symm (actualKLUnitary.symm (a n)) := by
  change actualCylinderFourier
    (actualCylinderFourier.symm (heightModesToRadial.symm (nonzeroModeKL.symm a))) n = _
  rw [actualCylinderFourier.apply_symm_apply]
  rfl

/-- Every spectral Hilbert-sum element is reconstructed in canonical
cylinder L2 using the ACTUAL inverse KL and inverse height maps. -/
theorem actualCylinderKL_inverse_hasSum (a : NonzeroSpectralModes) :
    HasSum (fun n : NonzeroMode => modeEmbedding n
      ((modeLiouville n).symm (actualKLUnitary.symm (a n))))
      (actualCylinderKL.symm a : CylinderL2) := by
  have h := actualCylinderFourier_hasSum_reconstruction (actualCylinderKL.symm a)
  simpa only [← actualCylinderFourier_apply, actualCylinderKL_inverse_fourier] using h

/-- A genuine single-mode compact radial input, synthesized into the
actual zero-mean cylinder by the native inverse height unitary. -/
def compactRadialMode (n : NonzeroMode) (T : RadialTest) : zeroMeanCylinder :=
  nonzeroCylinderMode n ((modeLiouville n).symm (radialCoreL2 T))

/-- The synthesized compact mode is the actual physical function with
the positive-frequency scale only inside the height logarithm. -/
theorem compactRadialMode_ae (n : NonzeroMode) (T : RadialTest) :
    ((compactRadialMode n T : CylinderL2) : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (fun z => AddCircle.fourier (n : ℤ) z.1 *
        ((Real.sqrt (z.2 : ℝ) : ℂ) *
          T.function (Real.log (frequencyScale n * (z.2 : ℝ))))) := by
  have hheight : ((modeLiouville n).symm (radialCoreL2 T) : PositiveHeight → ℂ)
      =ᵐ[heightMeasure] (fun y => (Real.sqrt (y : ℝ) : ℂ) *
        T.function (Real.log (frequencyScale n * (y : ℝ)))) :=
    WeightedHeightNativeUnitary20261026a.weightedHeightUnitary_inverse_on_core_ae
      (frequencyScale n) (frequencyScale_pos n.property) T
  have hprod := (quasiMeasurePreserving_snd
    (μ := AddCircle.haarAddCircle) (ν := heightMeasure)).ae hheight
  change (modeEmbedding (n : ℤ) ((modeLiouville n).symm (radialCoreL2 T)) :
    CuspCylinder → ℂ) =ᵐ[cylinderMeasure] _
  filter_upwards [modeEmbedding_ae (n : ℤ) ((modeLiouville n).symm (radialCoreL2 T)),
    hprod] with z hz hy
  rw [hz, hy]

theorem actualCylinderKL_compactRadialMode (n : NonzeroMode) (T : RadialTest) :
    actualCylinderKL (compactRadialMode n T) = lp.single 2 n (rawKLTestTransform T) := by
  ext m
  rw [actualCylinderKL_apply]
  change actualKLUnitary (modeLiouville m
    (cylinderCoefficient m (modeEmbedding n ((modeLiouville n).symm (radialCoreL2 T))))) = _
  rw [cylinderCoefficient_mode]
  by_cases hmn : m = n
  · subst m
    simp only [if_pos rfl, LinearIsometryEquiv.apply_symm_apply,
      actualKLUnitary_on_test, lp.single_apply, Pi.single_eq_same]
  · have hv : (m : ℤ) ≠ (n : ℤ) := Subtype.val_injective.ne hmn
    simp [hv, hmn, lp.single_apply, Pi.single_apply]

/-- Exact literal K_i*tau transform on a compact physical mode; this
pins the assembled unitary to the actual transform, not just its norm. -/
theorem actualCylinderKL_compactRadialMode_ae (n : NonzeroMode) (T : RadialTest) :
    (actualCylinderKL (compactRadialMode n T) n : ℝ → ℂ) =ᵐ[tauMeasure]
      ActualKLCompactTestIntegrationByParts20261025a.actualKtransform T.function := by
  rw [actualCylinderKL_compactRadialMode]
  simpa only [lp.single_apply, Pi.single_eq_same] using rawKLTestTransform_ae T

end
end ImbalancedChen.Part3.ActualNonzeroCylinderKLUnitary20261026a
