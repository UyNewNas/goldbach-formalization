import ImbalancedChen.Part3ActualContinuousSpatialProfiles
import ImbalancedChen.Part3NormalizedCuspCompactPoincare
import ImbalancedChen.Part3CompactSeedArbitraryQuotientPairing

/-! Spatial testing in the two manuscript frames. The test vector lives
on the actual finite-level quotient with its hyperbolic measure. Local
normal convergence of the actual Eisenstein lift supplies compact
absolute integrability, without an Eisenstein L² assumption. -/
namespace ImbalancedChen.Part3.ActualContinuousPoincarePairing20261110

noncomputable section
open Set Filter MeasureTheory Matrix Complex UpperHalfPlane AddCircle
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualContinuousSpatialProfiles20261110 ActualContinuousClassFourier20261110
open ActualOrdinaryContinuousModes20261110 ActualYoungFormalClass20261110
open ActualCriticalCuspEvaluation20261110 ActualYoungCriticalCusps20261110
open ActualCuspDenominatorClasses20261110
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open Gamma0ActualCuspsSourceOnly Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0ActualParabolicUnfolding20261025a GammaInfinityTranslationStrip20261025a
open Gamma0ParabolicCosetRows20261025a ActualInfinityKloostermanSeed20261025a
open CompactCuspParabolicL220261025a ActualPoincareSpectralCoefficient20261026a
open NormalizedCuspCompactPoincare20261026b NormalizedCuspCompactFourierFubini20261026b
open NormalizedCuspCompactQuotientLp20261026b CompactSeedArbitraryQuotientPairing20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z CanonicalPlanarL2UnitarySourceOnly
open MaassWeightedCoordinateL220261024zz ActualFrickeCuspPhase20261025a
open ActualCuspFourierSectionSourceOnly ActualEisensteinFourierInterchange20261025a
open PowerSeedFourierLaplaceFubini ComplexOrderKQCalculus

private theorem scaling_infty (N : ℕ) (hN : 0 < N) :
    normalizedScaling N hN (1 : SL(2,ℤ)) = 1 := by
  apply Subtype.ext
  rw [normalizedScaling_entries,cuspWidth_infinity N hN]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- The infinity branch is the genuine parabolic quotient Poincare
series. The other branch uses the normalized source sigmaOne. -/
def originalPoincare (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (ψ : ℝ → ℂ) :
    Gamma0OrbitSpace N → ℂ :=
  if one then complexPoincare N (physicalFrameSeed N (NeZero.pos N) cuspOneMatrix m ψ)
  else parabolicComplexPoincare N (fourierRadialSeed m ψ)

def originalFrame (one : Bool) : SL(2,ℤ) := if one then cuspOneMatrix else 1

theorem original_eq_framed (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (ψ : ℝ → ℂ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    originalPoincare N one m ψ = complexPoincare N (physicalFrameSeed N (NeZero.pos N) (originalFrame one) m ψ) := by
  cases one
  · simp only [originalPoincare,Bool.false_eq_true,if_false,compactCusp_quotient_eq_full N m ψ hc hpos]
    congr 1
    funext z
    simp [physicalFrameSeed,originalFrame,scaling_infty]
  · rfl

private theorem strip_pair_integrable {N : ℕ} [NeZero N] (g : SL(2,ℤ))
    (a : Parameters N) (t : ℝ) (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Integrable (strip.indicator (framePairSeed N (NeZero.pos N) g (quotientProfile a t) m ψ)) := by
  let P := framePairSeed N (NeZero.pos N) g (quotientProfile a t) m ψ
  have hP : Continuous P := (fourierRadialSeed_continuous m ψ hψ).star.mul
    ((native_spatial a t).comp (frameAction_continuous N (NeZero.pos N) g))
  have hlocal := hP.locallyIntegrable.indicator (μ := (volume : Measure ℍ)) strip_measurable
  have hsupp : Function.support (strip.indicator P) ⊆ cuspSupportK ψ := by
    intro z hz
    apply cuspStripSeed_support_subset m ψ
    intro he
    by_cases hz' : z ∈ strip
    · have hzero : fourierRadialSeed m ψ z = 0 := by simpa only [cuspStripSeed,indicator_of_mem hz'] using he
      exact hz (by simp [hz',P,framePairSeed,hzero])
    · exact hz (by simp [hz'])
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (hlocal.integrableOn_isCompact (cuspSupportK_isCompact ψ hc hpos))

private theorem framed_pair {N : ℕ} [NeZero N] (g : SL(2,ℤ)) (a : Parameters N) (t : ℝ)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    let f := physicalFrameSeed N (NeZero.pos N) g m ψ
    let F := quotientProfile a t
    Integrable (fun q => star (complexPoincare N f q)*F q) (carrierPushforward N) ∧
    (∫ q, star (complexPoincare N f q)*F q ∂carrierPushforward N) =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) •
        (star (ψ y)*frameFourier N (NeZero.pos N) g F m y) := by
  let f := physicalFrameSeed N (NeZero.pos N) g m ψ
  let F := quotientProfile a t
  let P := framePairSeed N (NeZero.pos N) g F m ψ
  let A := fun w => star (f w)*testLift N F w
  have hstrip := strip_pair_integrable g a t m ψ hψ hc hpos
  have hat : A ∘ frameAction N (NeZero.pos N) g = strip.indicator P := by
    funext z
    by_cases hz : z ∈ strip <;>
      simp [A,P,f,Function.comp_apply,physicalFrameSeed,frameAction,cuspStripSeed,framePairSeed,frameLift,testLift,hz]
  have hA : Integrable A (volume : Measure ℍ) := by
    apply ((frame_measurePreserving N (NeZero.pos N) g).integrable_comp_emb
      (frameAction_measurableEmbedding N (NeZero.pos N) g)).mp
    rw [hat]
    exact hstrip
  have hproj : complexPoincare N A =ᵐ[carrierPushforward N] (fun q => star (complexPoincare N f q)*F q) := by
    rw [← reducedProjection_map_measure N,(reducedProjection_measurableEmbedding N).ae_map_iff]
    exact ae_of_all _ (fun z => by
      rw [complexPoincare_projection,complexPoincare_projection]
      exact compact_pair_full_trace N f F z)
  refine ⟨(complexPoincare_integrable N A hA).congr hproj,?_⟩
  let G := framePlanarPair N (NeZero.pos N) g F m ψ
  have hchart : G ∘ chartMap = strip.indicator P := framePlanarPair_at_chart N (NeZero.pos N) g F m ψ
  have hG : Integrable G chartMeasure := (canonical_complex_integrable_iff_chart G).mp (by
    rw [hchart]
    exact hstrip)
  letI : SigmaFinite verticalWeightedMeasure := by unfold verticalWeightedMeasure; infer_instance
  rw [chartMeasure_eq_product] at hG
  calc
    _ = ∫ q, complexPoincare N A q ∂carrierPushforward N := integral_congr_ae hproj.symm
    _ = ∫ z : ℍ, A z := complex_poincare_unfolding N A hA
    _ = ∫ z : ℍ, A (frameAction N (NeZero.pos N) g z) :=
      ((frame_measurePreserving N (NeZero.pos N) g).integral_comp (frameAction_measurableEmbedding N (NeZero.pos N) g) A).symm
    _ = ∫ p, G p ∂chartMeasure := by
      change (∫ z : ℍ, (A ∘ frameAction N (NeZero.pos N) g) z) = _
      rw [hat,← hchart,canonical_complex_integral_eq_chart]
    _ = _ := by
      rw [chartMeasure_eq_product,integral_prod_symm _ hG]
      simp_rw [show ∀ y, (∫ x, G (x,y)) = star (ψ y)*frameFourier N (NeZero.pos N) g F m y from
        framePlanarPair_horizontal_integral N (NeZero.pos N) g F m ψ]
      simpa only [verticalWeightedMeasure,NNReal.smul_def,verticalWeight] using
        (integral_withDensity_eq_integral_smul verticalWeight_measurable
          (fun y => star (ψ y)*frameFourier N (NeZero.pos N) g F m y)
          (μ := (volume : Measure ℝ).restrict (Ioi 0)))

private theorem neg_phase (m : ℤ) (x : ℝ) : fourier (-m) (x : UnitAddCircle) = fourierPhase m x := by
  rw [fourier_coe_apply]
  unfold fourierPhase
  simp only [div_one]
  push_cast
  congr 1
  ring

private theorem actual_frame_mode {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool)
    (m : ℤ) (hm : m ≠ 0) (t y : ℝ) (hy : 0 < y) :
    frameFourier N (NeZero.pos N) (originalFrame one) (quotientProfile a t) m y = radial m t y*nativeR a one m t := by
  rw [frameFourier_positive_height N (NeZero.pos N) _ _ m hy,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  cases one
  · simp only [originalFrame,Bool.false_eq_true,if_false,frameAction,scaling_infty,one_smul,quotientProfile_projection,neg_phase]
    simpa only [sectionMode,Bool.false_eq_true,if_false,cuspFamily,Equiv.symm_apply_apply,physicalFamily,horizontalPoint] using
      native_mode a false m hm t y hy
  · rw [← native_sigmaOne a m hm t y hy,fourierCoeff_eq_intervalIntegral _ m (0 : ℝ)]
    simp only [div_one,one_smul,zero_add,smul_eq_mul]
    apply intervalIntegral.integral_congr
    intro x _
    have hh : (⟨⟨x,y⟩,hy⟩ : ℍ) = horizontal y hy x := by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp [horizontal]
    change fourier (-m) (x : UnitAddCircle) * quotientProfile a t
      (orbitProjection N (normalizedScaling N (NeZero.pos N) cuspOneMatrix • (⟨⟨x,y⟩,hy⟩ : ℍ))) =
        fourier (-m) (x : UnitAddCircle) * physicalFamily N t a
        (normalizedScaling N (NeZero.pos N) cuspOneMatrix • horizontal y hy x)
    rw [quotientProfile_projection,hh]

def radialProbe (m : ℤ) (ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) • (star (ψ y)*radial m t y)

theorem radialProbe_integrable (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    IntegrableOn (fun y : ℝ => ((y⁻¹)^2 : ℝ) • (star (ψ y)*radial m t y)) (Ioi 0) := by
  let P := fun y : ℝ => ((y⁻¹)^2 : ℝ) • (star (ψ y)*radial m t y)
  have hM : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  have hK : ContinuousOn (fun y : ℝ => ComplexOrderKBridgeSourceOnly.complexOrderK
      (criticalPoint t-1/2) (2*Real.pi*|(m : ℝ)|*y)) (tsupport ψ) := by
    intro y hy
    exact ((complexOrderK_hasDerivAt_q _ (show 0 < 2*Real.pi*|(m : ℝ)|*y from
      mul_pos (by positivity) (hpos hy))).continuousAt.comp (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  have hP : ContinuousOn P (tsupport ψ) :=
    ((continuousOn_id.inv₀ (fun y hy => (hpos hy).ne')).pow 2).smul
      (hψ.star.continuousOn.mul ((continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sqrt)).continuousOn.mul hK))
  have hsupp : Function.support P ⊆ tsupport ψ := by
    intro y hy
    by_contra h
    exact hy (by simp [P,image_eq_zero_of_notMem_tsupport h])
  exact ((integrableOn_iff_integrable_of_support_subset hsupp).mp
    (ContinuousOn.integrableOn_compact hc hP)).integrableOn

/-- Both genuine compact Poincare vectors test every actual incoming
cusp function. The negative Fourier phase belongs to the conjugated
seed, and R is the original sqrt(|m|) rho_W at the same physical cusp. -/
theorem original_spatial_pairing {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool)
    (m : ℤ) (hm : m ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (t : ℝ) :
    Integrable (fun q => star (originalPoincare N one m ψ q)*quotientProfile a t q) (carrierPushforward N) ∧
    (∫ q, star (originalPoincare N one m ψ q)*quotientProfile a t q ∂carrierPushforward N) =
      radialProbe m ψ t*nativeR a one m t := by
  rw [original_eq_framed N one m ψ hc hpos]
  obtain ⟨hI,hE⟩ := framed_pair (originalFrame one) a t m ψ hψ hc hpos
  refine ⟨hI,hE.trans ?_⟩
  rw [radialProbe,← integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  rw [actual_frame_mode a one m hm t y hy,← mul_assoc,smul_mul_assoc]

end
end ImbalancedChen.Part3.ActualContinuousPoincarePairing20261110
