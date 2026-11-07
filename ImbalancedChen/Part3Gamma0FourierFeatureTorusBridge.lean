import ImbalancedChen.Part3Gamma0QuantitativeCutoffGeometry
import ImbalancedChen.Part3ActualPoincareSpectralCoefficient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual quotient linear Fourier feature is the Fourier coefficient of
the actual normalized compact chart seed, with EXACT coefficient equality.
The physical y^-2 density and affine Jacobian are paid explicitly. Only
a genuine C2 representative with the original local-AE meaning is used;
no completed weak derivative, Fourier error or rank bound is assumed.
-/

namespace ImbalancedChen.Part3.Gamma0FourierFeatureTorusBridge20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane BigOperators
open Gamma0FiniteFourierFeatures20261026b Gamma0QuantitativeCutoffGeometry20261026b
open QuantitativeChartCutoffFirstDerivatives20261026b
open Gamma0FiniteChartReconstruction20261026b Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0PositiveRectangleRellichCharts20261026b
open Gamma0CompletedLocalizedChartValue20261026b Gamma0LocalizedChartIntegralBudget20261026b
open PositiveRectangleAffineNormalization20261026b PositiveRectangleNativeHyperbolicL220261026b
open CompactRectanglePhysicalRellich20261026a ProductCircleFiniteBoxRellich20261026a
open CanonicalTensorHyperbolicLaplacianForm20261024z
open ActualPoincareSpectralCoefficient20261026a UpperHalfPlaneHyperbolicMeasure20261024z
open Gamma0LocalFourierTailCharts20261026a MaassWeakOperatorCore20261024zz
open ActualGamma0MaassDescent20261025a

/-- Complex affine substitution, proved from the literal real-plane
change of variables on real and imaginary parts. -/
theorem complex_integral_affine_plane (R : Rectangle) (G : Plane → ℂ)
    (hG : Integrable G) (hGA : Integrable (fun p => G (R.affine p))) :
    (∫ p : Plane, G (R.affine p)) = ((R.width*R.height)⁻¹ : ℝ) • ∫ p : Plane, G p := by
  apply Complex.ext
  · change (∫ p : Plane, G (R.affine p)).re =
      (R.width*R.height)⁻¹*(∫ p : Plane, G p).re
    rw [← integral_re hGA, ← integral_re hG]
    exact integral_affine_plane R (fun p => (G p).re) hG.re hGA.re
  · change (∫ p : Plane, G (R.affine p)).im =
      (R.width*R.height)⁻¹*(∫ p : Plane, G p).im
    rw [← integral_im hGA, ← integral_im hG]
    exact integral_affine_plane R (fun p => (G p).im) hG.im hGA.im

def planeFourierIntegrand (R : Rectangle) (k : Frequency) (F : Plane → ℂ) (p : Plane) : ℂ :=
  phase (k 0) (R.inverse p).1 * phase (k 1) (R.inverse p).2 * F p

theorem normalized_seed_coefficient {R : Rectangle} {δ : ℝ} (hδ : 0 < δ)
    (s : RectangleSeed R δ) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (torusSeed (normalized s)) k =
      ((R.width*R.height)⁻¹ : ℝ) • ∫ p : Plane, planeFourierIntegrand R k s.function p := by
  let G := planeFourierIntegrand R k s.function
  have hsc : Continuous s.function := s.smooth.continuous
  have hGc : Continuous G := by
    dsimp [G, planeFourierIntegrand, Rectangle.inverse, phase]
    fun_prop
  have hGA : Continuous (fun p => G (R.affine p)) := hGc.comp R.affine_contDiff.continuous
  have hG : Integrable G := hGc.integrable_of_hasCompactSupport
    ((compact_of_support R s.support_subset).mul_left)
  have hGAc : HasCompactSupport (fun p => G (R.affine p)) := by
    exact (compact_pull R s.support_subset).mul_left
  have hGAi : Integrable (fun p => G (R.affine p)) := hGA.integrable_of_hasCompactSupport hGAc
  change UnitAddTorus.mFourierCoeff (liftL2 (normalized s).function
    (normalized s).smooth.continuous) k = _
  rw [coefficient_rectangle]
  calc
    _ = ∫ p : Plane, G (R.affine p) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
        have hz : (normalized s).function p=0 := by
          by_contra hn
          have hh := (normalized s).support_subset hn
          apply hp
          change (0 < p.1 ∧ p.1 ≤ 1) ∧ (0 < p.2 ∧ p.2 ≤ 1)
          dsimp [marginRectangle] at hh
          constructor
          · exact ⟨hδ.trans_le hh.1.1, by linarith [hh.1.2]⟩
          · exact ⟨hδ.trans_le hh.2.1, by linarith [hh.2.2]⟩
        simp only [hz, mul_zero])]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        simp only [G, planeFourierIntegrand, R.inverse_affine, normalized])
    _ = _ := complex_integral_affine_plane R G hG hGAi

/-- The native physical density cancels exactly against the y² in the
linear Fourier test. The bottom-positive support removes the complement. -/
theorem native_seed_fourier_integral {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) (k : Frequency) :
    (∫ z : UpperHalfPlane, inner ℂ (fourierTest R k z) (nativeFunction s z)) =
      ((R.width*R.height)⁻¹ : ℝ) • ∫ p : Plane, planeFourierIntegrand R k s.function p := by
  let G : Plane → ℂ := fun p => inner ℂ
    (((p.2^2/(R.width*R.height) : ℝ) : ℂ) *
      (AddCircle.fourier (k 0) (((p.1-R.left)/R.width : ℝ) : UnitAddCircle) *
        AddCircle.fourier (k 1) (((p.2-R.bottom)/R.height : ℝ) : UnitAddCircle))) (s.function p)
  have hcancel (p : Plane) (hp : p ∈ upperChart) :
      chartWeight p • G p = ((R.width*R.height)⁻¹ : ℝ) •
        planeFourierIntegrand R k s.function p := by
    have hp0 : p.2 ≠ 0 := ne_of_gt hp
    dsimp [G, planeFourierIntegrand, Rectangle.inverse, phase]
    simp only [RCLike.inner_apply', NNReal.smul_def, chartWeight, Complex.real_smul,
      map_mul, Complex.star_def, Complex.conj_ofReal, ← AddCircle.fourier_neg,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp [hp0, R.width_pos.ne', R.height_pos.ne']
    <;> ring
  calc
    _ = ∫ z : UpperHalfPlane, G (chartMap z) := rfl
    _ = ∫ p : Plane, G p ∂chartMeasure := canonical_complex_integral_eq_chart G
    _ = ∫ p in upperChart, chartWeight p • G p := by
      exact integral_withDensity_eq_integral_smul chartWeight_measurable G
    _ = ∫ p in upperChart, ((R.width*R.height)⁻¹ : ℝ) •
        planeFourierIntegrand R k s.function p :=
      setIntegral_congr_fun upperChart_measurable hcancel
    _ = ∫ p : Plane, ((R.width*R.height)⁻¹ : ℝ) •
        planeFourierIntegrand R k s.function p := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : s.function p=0 := by
        by_contra hn
        exact hp (R.bottom_pos.trans_le (region_height hδ (s.support_subset hn)).1)
      simp only [planeFourierIntegrand, hz, mul_zero, smul_zero]
    _ = _ := integral_smul _ _

theorem native_seed_integral_eq_torus_coefficient {R : Rectangle} {δ : ℝ} (hδ : 0 < δ)
    (s : RectangleSeed R δ) (k : Frequency) :
    (∫ z : UpperHalfPlane, inner ℂ (fourierTest R k z) (nativeFunction s z)) =
      UnitAddTorus.mFourierCoeff (torusSeed (normalized s)) k := by
  rw [native_seed_fourier_integral hδ.le, normalized_seed_coefficient hδ]

/-- A genuine smooth representative is used ONLY through its original
same-AE value meaning. It need not belong to global upper-plane L2. -/
theorem actual_quantitative_feature_eq_torus_coefficient (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (u : QuotientL2 N) (f : SmoothFunction)
    (hf : f.function =ᵐ[(volume : Measure UpperHalfPlane)]
      (fun z => u (orbitProjection N z))) (i : ChartIndex N) (k : Frequency) :
    actualChartFourierCoefficient N (quantitativeRectangle Y hY)
      (quantitativeCutoffCompactSet_isCompact Y hY) (quantitativeUpperCutoff Y)
      (quantitativeUpperCutoff_continuous Y) 1 (quantitativeUpperCutoff_norm_le_one Y) i k u =
        UnitAddTorus.mFourierCoeff (torusSeed (normalized
          (quantitativeClassSeed N Y hY f (chartClass N i)))) k := by
  have ha := (classAction_measurePreserving N (chartClass N i)).quasiMeasurePreserving.ae_eq hf
  have har : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict (quantitativeCutoffCompactSet Y)),
      f.function (classAction N (chartClass N i) z) =
        u (orbitProjection N (classAction N (chartClass N i) z)) :=
    ha.filter_mono (ae_mono Measure.restrict_le_self)
  rw [actualChartFourierCoefficient_integral]
  calc
    _ = ∫ z in quantitativeCutoffCompactSet Y, inner ℂ
        (fourierTest (quantitativeRectangle Y hY) k z)
        (localizedClassChart N f.function (quantitativeUpperCutoff Y) (chartClass N i) z) := by
      apply integral_congr_ae
      filter_upwards [har] with z hz
      rw [localizedClassChart, hz]
      rfl
    _ = ∫ z : UpperHalfPlane, inner ℂ (fourierTest (quantitativeRectangle Y hY) k z)
        (nativeFunction (quantitativeClassSeed N Y hY f (chartClass N i)) z) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        have hr : quantitativeUpperCutoff Y z=0 := image_eq_zero_of_notMem_tsupport hz
        simp only [localizedClassChart, hr, zero_mul, inner_zero_right])]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        rw [nativeFunction, quantitativeClassSeed, classSeed]
        exact congrArg (fun c => inner ℂ (fourierTest (quantitativeRectangle Y hY) k z) c)
          (extendUpper_pair _ z).symm)
    _ = _ := native_seed_integral_eq_torus_coefficient (quantitativeMargin_pos hY) _ k

theorem quantitative_features_zero_iff_torus_box_zero (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (M : ℕ) (u : QuotientL2 N) (f : SmoothFunction)
    (hf : f.function =ᵐ[(volume : Measure UpperHalfPlane)]
      (fun z => u (orbitProjection N z))) :
    quantitativeFourierFeatures N Y hY M u=0 ↔
      ∀ i k, k ∈ box M → UnitAddTorus.mFourierCoeff (torusSeed (normalized
        (quantitativeClassSeed N Y hY f (chartClass N i)))) k=0 := by
  rw [quantitativeFourierFeatures, actualFourierFeatures_eq_zero_iff]
  simp_rw [actual_quantitative_feature_eq_torus_coefficient N Y hY u f hf]

end
end ImbalancedChen.Part3.Gamma0FourierFeatureTorusBridge20261026b
