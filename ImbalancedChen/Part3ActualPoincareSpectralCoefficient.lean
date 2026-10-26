import ImbalancedChen.Part3CompactCuspParabolicL2
import ImbalancedChen.Part3CanonicalPlanarL2Unitary
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The actual compact cusp Poincare series paired with an arbitrary quotient
function whose lift is continuous. Compact radial support proves the true
strip L1 premise. The actual Gamma0 unfolding and actual dx dy/y^2 chart
give its literal horizontal Fourier coefficient, with the seed conjugated.
No eigenfunction coefficient formula or spectral expansion is assumed.
The Whittaker classification of that Fourier coefficient remains separate.
-/

namespace ImbalancedChen.Part3.ActualPoincareSpectralCoefficient20261026a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly

/-- The test is a function on the actual orbit quotient, not an assumed
invariant formula on the upper half plane. -/
def testLift (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) : UpperHalfPlane → ℂ :=
  U ∘ orbitProjection N

theorem testLift_invariant (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    testLift N U (g • z) = testLift N U z := by
  simp only [testLift, Function.comp_apply, orbitProjection_smul]

theorem testLift_periodic (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (k : ℤ) (z : UpperHalfPlane) :
    testLift N U (translate k z) = testLift N U z :=
  testLift_invariant N U ⟨ModularGroup.T ^ k, translation_mem_gamma0 N k⟩ z

def spectralPairSeed (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (U : Gamma0OrbitSpace N → ℂ) (z : UpperHalfPlane) : ℂ :=
  star (fourierRadialSeed m ψ z) * testLift N U z

theorem spectralPairSeed_continuous (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) : Continuous (spectralPairSeed N m ψ U) :=
  (fourierRadialSeed_continuous m ψ hψ).star.mul hU

theorem spectralPairSeed_periodic (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (U : Gamma0OrbitSpace N → ℂ) (k : ℤ) (z : UpperHalfPlane) :
    spectralPairSeed N m ψ U (translate k z) = spectralPairSeed N m ψ U z := by
  simp only [spectralPairSeed, fourierRadialSeed_periodic, testLift_periodic]

/-- True integrability: the test need not be globally bounded. Its lift
is bounded on the actual compact support container of the strip seed. -/
theorem spectralPairSeed_integrableOn_strip (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) : IntegrableOn (spectralPairSeed N m ψ U) strip := by
  have hlocal : LocallyIntegrable (strip.indicator (spectralPairSeed N m ψ U))
      (volume : Measure UpperHalfPlane) :=
    (spectralPairSeed_continuous N m ψ hψ U hU).locallyIntegrable.indicator strip_measurable
  have hsupp : Function.support (strip.indicator (spectralPairSeed N m ψ U)) ⊆
      cuspSupportK ψ := by
    intro z hz
    apply cuspStripSeed_support_subset m ψ
    intro he
    by_cases hs : z ∈ strip
    · have hzero : fourierRadialSeed m ψ z = 0 := by
        simpa only [cuspStripSeed, indicator_of_mem hs] using he
      exact hz (by simp [indicator_of_mem hs, spectralPairSeed, hzero])
    · exact hz (by simp [hs])
  apply (integrable_indicator_iff strip_measurable).mp
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (hlocal.integrableOn_isCompact (cuspSupportK_isCompact ψ hc hpos))

theorem spectralPairSeed_trace (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (U : Gamma0OrbitSpace N → ℂ) (z : UpperHalfPlane) :
    parabolicTraceComplex N (spectralPairSeed N m ψ U) z =
      star (parabolicTraceComplex N (fourierRadialSeed m ψ) z) * testLift N U z := by
  unfold parabolicTraceComplex spectralPairSeed
  simp_rw [testLift_invariant]
  rw [tsum_mul_right, ← tsum_star]

/-- Actual quotient pairing unfolded to the actual width-one strip.
The first argument is conjugate-linear, as in the complex Hilbert inner product. -/
theorem actual_quotient_pairing_eq_strip (N : ℕ) [NeZero N] (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) :
    (∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) * U u
      ∂carrierPushforward N) = ∫ z in strip, spectralPairSeed N m ψ U z := by
  calc
    _ = ∫ z : reducedCarrier N,
        star (parabolicTraceComplex N (fourierRadialSeed m ψ) z) * testLift N U z
          ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        rw [parabolicComplexPoincare_projection]; rfl)
    _ = ∫ z in reducedCarrier N, parabolicTraceComplex N (spectralPairSeed N m ψ U) z := by
      rw [integral_subtype_comap (reducedCarrier_measurable N)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => (spectralPairSeed_trace N m ψ U z).symm)
    _ = _ := complex_parabolic_carrier_unfolding N _
      (spectralPairSeed_periodic N m ψ U)
      (spectralPairSeed_continuous N m ψ hψ U hU).measurable
      (spectralPairSeed_integrableOn_strip N m ψ hψ hc hpos U hU)

/-- Complex-valued canonical chart transport, retaining the actual density. -/
theorem canonical_complex_integral_eq_chart (G : ℝ × ℝ → ℂ) :
    (∫ z : UpperHalfPlane, G (chartMap z)) = ∫ p, G p ∂chartMeasure := by
  change (∫ z, G (chartMap z)
    ∂coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul upperDensityNN_measurable]
  have heq : (fun z => upperDensityNN z • G (chartMap z)) =
      (fun p => chartWeight p • G p) ∘ chartMap := by
    funext z
    simp only [Function.comp_apply, chartMap, upperDensityNN_eq_chartWeight]
  rw [heq, ← chartMap_measurableEmbedding.integral_map, map_coordinateMeasure]
  exact (integral_withDensity_eq_integral_smul chartWeight_measurable G).symm

theorem canonical_complex_integrable_iff_chart (G : ℝ × ℝ → ℂ) :
    Integrable (G ∘ chartMap) (volume : Measure UpperHalfPlane) ↔
      Integrable G chartMeasure := by
  change Integrable (G ∘ chartMap)
    (coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul upperDensityNN_measurable]
  unfold chartMeasure
  rw [integrable_withDensity_iff_integrable_smul chartWeight_measurable,
    ← map_coordinateMeasure, chartMap_measurableEmbedding.integrable_map_iff]
  congr 1
  funext z
  simp only [Function.comp_apply, chartMap, upperDensityNN_eq_chartWeight]

/-- Literal negative-exponential coefficient on one actual horizontal period.
Zero extension below height zero is irrelevant to every final integral. -/
def actualTestFourier (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (m : ℤ) (y : ℝ) : ℂ :=
  ∫ x in Ico (0 : ℝ) 1,
    AddCircle.fourier (-m) (x : UnitAddCircle) * chartPullback (testLift N U) (x, y)

theorem actualTestFourier_eq_interval (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (m : ℤ) (y : ℝ) : actualTestFourier N U m y =
      ∫ x in (0 : ℝ)..1,
        AddCircle.fourier (-m) (x : UnitAddCircle) * chartPullback (testLift N U) (x, y) := by
  rw [actualTestFourier, intervalIntegral.integral_of_le zero_le_one,
    integral_Ico_eq_integral_Ioc]

def planarPairSeed (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (U : Gamma0OrbitSpace N → ℂ) (p : ℝ × ℝ) : ℂ :=
  (Ico (0 : ℝ) 1).indicator (fun x =>
    star (AddCircle.fourier m (x : UnitAddCircle) * ψ p.2) *
      chartPullback (testLift N U) (x, p.2)) p.1

theorem planarPairSeed_at_chart (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (U : Gamma0OrbitSpace N → ℂ) : planarPairSeed N m ψ U ∘ chartMap =
      strip.indicator (spectralPairSeed N m ψ U) := by
  funext z
  have hp := chartPullback_at_upper (testLift N U) z
  by_cases hz : z ∈ strip
  · simpa only [Function.comp_apply, planarPairSeed, chartMap, strip,
      fourierRadialSeed, spectralPairSeed, indicator_of_mem hz] using
      congrArg (fun c => star (fourierRadialSeed m ψ z) * c) hp
  · simp only [Function.comp_apply, planarPairSeed, chartMap, strip,
      indicator_of_notMem hz]

theorem planarPairSeed_integrable (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) : Integrable (planarPairSeed N m ψ U) chartMeasure := by
  apply (canonical_complex_integrable_iff_chart _).mp
  rw [planarPairSeed_at_chart]
  exact (integrable_indicator_iff strip_measurable).mpr
    (spectralPairSeed_integrableOn_strip N m ψ hψ hc hpos U hU)

theorem planarPairSeed_horizontal_integral (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (U : Gamma0OrbitSpace N → ℂ) (y : ℝ) :
    (∫ x, planarPairSeed N m ψ U (x, y)) = star (ψ y) * actualTestFourier N U m y := by
  rw [planarPairSeed, integral_indicator measurableSet_Ico, actualTestFourier,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [star_mul, Complex.star_def, ← AddCircle.fourier_neg]
    ring)

/-- Exact seed/Fourier pairing, obtained by actual Fubini after proved
absolute integrability. The height measure is literally y^-2 dy. -/
theorem actual_quotient_pairing_eq_fourier (N : ℕ) [NeZero N] (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) :
    (∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) * U u
      ∂carrierPushforward N) =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) • (star (ψ y) * actualTestFourier N U m y) := by
  letI : SigmaFinite verticalWeightedMeasure := by
    unfold verticalWeightedMeasure
    infer_instance
  have hi := planarPairSeed_integrable N m ψ hψ hc hpos U hU
  rw [chartMeasure_eq_product] at hi
  rw [actual_quotient_pairing_eq_strip N m ψ hψ hc hpos U hU,
    ← integral_indicator strip_measurable, ← planarPairSeed_at_chart,
    canonical_complex_integral_eq_chart, chartMeasure_eq_product,
    integral_prod_symm _ hi]
  simp_rw [planarPairSeed_horizontal_integral]
  simpa only [verticalWeightedMeasure, NNReal.smul_def, verticalWeight] using
    (integral_withDensity_eq_integral_smul verticalWeight_measurable
      (fun y => star (ψ y) * actualTestFourier N U m y)
      (μ := (volume : Measure ℝ).restrict (Ioi 0)))

/-- The coefficient-side integral is genuinely absolutely integrable;
the equality above is not an equality of default-zero divergent integrals. -/
theorem actual_fourier_pairing_integrable (N : ℕ) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) :
    IntegrableOn (fun y => ((y⁻¹)^2 : ℝ) •
      (star (ψ y) * actualTestFourier N U m y)) (Ioi (0 : ℝ)) := by
  letI : SigmaFinite verticalWeightedMeasure := by
    unfold verticalWeightedMeasure
    infer_instance
  have hi := planarPairSeed_integrable N m ψ hψ hc hpos U hU
  rw [chartMeasure_eq_product] at hi
  have houter := hi.integral_prod_right
  simp_rw [planarPairSeed_horizontal_integral] at houter
  simpa only [NNReal.smul_def, verticalWeight] using
    (integrable_withDensity_iff_integrable_smul verticalWeight_measurable).mp houter

/-- In positive height the coefficient uses the actual point x+iy. -/
theorem actualTestFourier_positive_height (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (m : ℤ) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N U m y = ∫ x in Ico (0 : ℝ) 1,
      AddCircle.fourier (-m) (x : UnitAddCircle) *
        U (orbitProjection N (⟨⟨x, y⟩, hy⟩ : UpperHalfPlane)) := by
  unfold actualTestFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [chartPullback, upperChart, mem_setOf_eq, hy, dif_pos,
      testLift, Function.comp_apply])

/-- The quotient side is a true L1 pairing whenever the test is actual L2. -/
theorem actual_quotient_pairing_integrable (N : ℕ) [NeZero N] (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (U : Gamma0OrbitSpace N → ℂ)
    (hU2 : MemLp U 2 (carrierPushforward N)) :
    Integrable (fun u => star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) * U u)
      (carrierPushforward N) :=
  MemLp.integrable_mul (p := 2) (q := 2)
    (compactCuspPoincare_memLp_two N m ψ hψ hc hpos).star hU2

/-- The literal quotient Hilbert inner product, with actual L2 representatives.
In particular this applies to smooth L2 Maass tests, without using or
assuming a spectral basis or the Whittaker classification of their modes. -/
theorem actual_poincare_L2_inner_eq_fourier (N : ℕ) [NeZero N] (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N)) :
    inner ℂ ((compactCuspPoincare_memLp_two N m ψ hψ hc hpos).toLp
      (parabolicComplexPoincare N (fourierRadialSeed m ψ))) (hU2.toLp U) =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) •
        (star (ψ y) * actualTestFourier N U m y) := by
  rw [← actual_quotient_pairing_eq_fourier N m ψ hψ hc hpos U hU, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compactCuspPoincare_memLp_two N m ψ hψ hc hpos).coeFn_toLp,
    hU2.coeFn_toLp] with u hP hV
  rw [hP, hV]
  simp only [RCLike.inner_apply', Complex.star_def]

end
end ImbalancedChen.Part3.ActualPoincareSpectralCoefficient20261026a
