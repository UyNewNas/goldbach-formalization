import ImbalancedChen.Part3ActualOppositeBesselTransform
import ImbalancedChen.Part3OriginalFullModulusTestJets
import ImbalancedChen.Part3ActualKLCompactPointwiseInversion
import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram

/-! The manuscript cutoff and its literal period-64 phase under the
native opposite-sign transform, in the variables q and t. -/
namespace ImbalancedChen.Part3.ActualPrescribedOppositeKL20261112

noncomputable section
open Set MeasureTheory Complex
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open ActualOppositeBruhatCoordinates20261112 ActualOppositeBesselTransform20261112
open OriginalFullModulusTestJets20261102 RadialSchrodingerL2Form20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ActualKLCompactTestIntegrationByParts20261025a ActualKLCompactTestWeightedL220261025a
open ActualKLInversionBounds20261025a ActualKLInversionContinuity20261025a
open ActualKLCompactPointwiseInversion20261025a ActualCommonHeightKGramSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly ImaginaryOrderKBesselSourceOnly

private def logTest (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) : RadialTest where
  function := fun r => spectralTest ell Y (Real.exp r)
  smooth := (spectralTest_contDiff ell Y).comp Real.contDiff_exp
  compact := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (Real.log (Y/16)) (Real.log (16*Y))))
    intro r hr
    have h := spectralTest_tsupport_strict ell hY
      (subset_tsupport (spectralTest ell Y) (show spectralTest ell Y (Real.exp r) ≠ 0 from hr))
    exact ⟨by simpa only [Real.log_exp] using Real.log_le_log (div_pos hY (by norm_num)) h.1.le,
      by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos r) h.2.le⟩

private theorem order_double (t : ℝ) : 2*((t : ℂ)*I)=(((2*t : ℝ) : ℂ)*I) := by
  push_cast
  ring

private theorem log_transform (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) (t : ℝ) :
    actualKtransform (logTest ell hY).function (2*t) =
      kTransform ((t : ℂ)*I) (spectralTest ell Y) := by
  let f := fun q : ℝ => complexOrderK (((2*t : ℝ) : ℂ)*I) q*spectralTest ell Y q/(q : ℂ)
  have J := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ)) measurableSet_univ
    (fun r _ => (Real.hasDerivAt_exp r).hasDerivWithinAt)
    (fun _ _ _ _ h => Real.exp_injective h) f
  simp only [image_univ,Real.range_exp,integral_univ,abs_of_pos (Real.exp_pos _),Complex.real_smul] at J
  rw [actualKtransform,kTransform,order_double]
  change (∫ r : ℝ,spectralTest ell Y (Real.exp r)*complexOrderK (((2*t : ℝ) : ℂ)*I) (Real.exp r)) =
    ∫ q in Ioi (0 : ℝ),f q
  rw [J]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    dsimp only [f]
    field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_pos r).ne'] <;> ring)

/-- The previously constructed common-height transform uses the same
standard Macdonald function, the same physical argument and dq/q. -/
theorem packet_forward {ι : Type*} (P : PacketData ι) (ell : D4 → ℤ) (t : ℝ) :
    kTransform ((t : ℂ)*I) (spectralTest ell P.Y0)=kTestTransform P ell t := by
  rw [kTransform,order_double,kTestTransform]
  change (∫ q in Ioi (0 : ℝ),complexOrderK (((2*t : ℝ) : ℂ)*I) q*spectralTest ell P.Y0 q/(q : ℂ))=_
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  by_cases hq : q ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hq,complexOrderK_imaginary]
    ring
  · have hz : spectralTest ell P.Y0 q=0 := by
      by_contra h
      have l := (spectralTest_tsupport_strict ell P.Y0_pos (subset_tsupport _ h)).1
      exact hq ((div_pos P.Y0_pos (by norm_num : (0:ℝ)<16)).trans l)
    simp only [indicator_of_notMem hq,hz,zero_mul]

def inverseDensity (Φ : ℝ → ℂ) (q t : ℝ) : ℂ :=
  (((2/Real.pi^2)*t*Real.sinh (Real.pi*t) : ℝ) : ℂ)*oppositeWeight Φ t*
    complexOrderK (2*((t : ℂ)*I)) q

/-- Exact pointwise recovery and absolute convergence at every positive
physical argument. The native positive-t coefficient is 2/pi² after
the doubling in the order and the eight in oppositeWeight. -/
theorem prescribed_inverse (ell : D4 → ℤ) {Y q : ℝ} (hY : 0<Y) (hq : 0<q) :
    IntegrableOn (inverseDensity (spectralTest ell Y) q) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ),inverseDensity (spectralTest ell Y) q t)=spectralTest ell Y q := by
  let T := logTest ell hY
  let r := Real.log q
  let A := actualKLInversionIntegrand T r
  have er : Real.exp r=q := Real.exp_log hq
  have point (t : ℝ) : (2 : ℂ)*A (2*t)=inverseDensity (spectralTest ell Y) q t := by
    dsimp only [A,actualKLInversionIntegrand,actualKLWeight,normalization,radialK,T]
    rw [er,log_transform,show Real.pi*(2*t)=2*(Real.pi*t) by ring,Real.sinh_two_mul,
      inverseDensity,oppositeWeight,order_double]
    push_cast
    ring
  have src : IntegrableOn A (Ioi (0 : ℝ)) := actualKLInversionIntegrand_integrable T r
  have scaled := (integrableOn_Ioi_comp_mul_left_iff A 0 (by norm_num : (0:ℝ)<2)).mpr
    (by simpa only [mul_zero] using src)
  refine ⟨(scaled.const_mul (2:ℂ)).congr (ae_of_all _ point),?_⟩
  have J := integral_comp_mul_left_Ioi' A 0 (by norm_num : (0:ℝ)<2)
  rw [mul_zero,Complex.real_smul] at J
  calc
    _ = ∫ t in Ioi (0 : ℝ),(2 : ℂ)*A (2*t) :=
      integral_congr_ae (ae_of_all _ (fun t => (point t).symm))
    _ = ∫ tau in Ioi (0 : ℝ),A tau := by simpa only [integral_const_mul,Complex.ofReal_ofNat] using J
    _ = spectralTest ell Y q := by
      simpa only [A,actualKLInversionIntegrand,actualKLWeight,normalization,radialK,T,logTest,er] using
        actualKL_compact_pointwise_inversion T r

end
end ImbalancedChen.Part3.ActualPrescribedOppositeKL20261112
