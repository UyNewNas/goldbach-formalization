import ImbalancedChen.Part3ActualInfinityCuspAnnihilator
import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Compact-height Poincare pairing for arbitrary actual quotient L2 functions.
The compact quotient-pullback measure domination supplies true strip L1.
Continuity of a quotient representative is never assumed. For an actual
L2 vector, its canonical strongly measurable representative supplies the
pointwise measurable unfolding. No density/completeness input is needed.
-/
namespace ImbalancedChen.Part3.ActualInfinityL2Pairing20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.ActualPoincareSpectralCoefficient20261026a
open ImbalancedChen.Part3.ActualInfinityCuspAnnihilator20261026b
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly

/-- Compact quotient L2 pullback, finite compact volume and the continuous
radial multiplier establish the actual strip pair L1. -/
theorem l2_spectralPairSeed_integrableOn_strip (N : ℕ) [NeZero N]
    (m : ℤ) (s : HeightSeed) (U : Gamma0OrbitSpace N → ℂ)
    (hU2 : MemLp U 2 (carrierPushforward N)) :
    IntegrableOn (spectralPairSeed N m s.toFun U) strip := by
  let K := cuspSupportK s.toFun
  have hK : IsCompact K := cuspSupportK_isCompact s.toFun s.compact s.positive
  letI : IsFiniteMeasure ((volume : Measure UpperHalfPlane).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hK.measure_lt_top⟩
  have hlocal : IntegrableOn (testLift N U) K :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (quotient_memLp_pullback_compact N hK hU2)
  have hpair : IntegrableOn (spectralPairSeed N m s.toFun U) K :=
    (fourierRadialSeed_continuous m s.toFun s.continuous).star.continuousOn.continuousOn_mul
      hlocal hK
  have hsupp : Function.support (strip.indicator (spectralPairSeed N m s.toFun U)) ⊆ K := by
    intro z hz
    apply cuspStripSeed_support_subset m s.toFun
    intro he
    by_cases hs : z ∈ strip
    · have hzero : fourierRadialSeed m s.toFun z = 0 := by
        simpa only [cuspStripSeed, indicator_of_mem hs] using he
      exact hz (by simp [indicator_of_mem hs, spectralPairSeed, hzero])
    · exact hz (by simp [hs])
  apply (integrable_indicator_iff strip_measurable).mp
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    (hpair.indicator strip_measurable)

/-- Actual quotient pairing unfolded without continuous representatives. -/
theorem l2_quotient_pairing_eq_strip (N : ℕ) [NeZero N]
    (m : ℤ) (s : HeightSeed) (U : Gamma0OrbitSpace N → ℂ)
    (hUm : Measurable U) (hU2 : MemLp U 2 (carrierPushforward N)) :
    (∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m s.toFun) u) * U u
      ∂carrierPushforward N) = ∫ z in strip, spectralPairSeed N m s.toFun U z := by
  calc
    _ = ∫ z : reducedCarrier N,
        star (parabolicTraceComplex N (fourierRadialSeed m s.toFun) z) * testLift N U z
          ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        rw [parabolicComplexPoincare_projection]; rfl)
    _ = ∫ z in reducedCarrier N, parabolicTraceComplex N (spectralPairSeed N m s.toFun U) z := by
      rw [integral_subtype_comap (reducedCarrier_measurable N)]
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun z => (spectralPairSeed_trace N m s.toFun U z).symm))
    _ = _ := complex_parabolic_carrier_unfolding N _
      (spectralPairSeed_periodic N m s.toFun U)
      (((fourierRadialSeed_continuous m s.toFun s.continuous).star.measurable).mul
        (hUm.comp (orbitProjection_measurable N)))
      (l2_spectralPairSeed_integrableOn_strip N m s U hU2)

/-- The product-plane pair is genuinely L1 for arbitrary quotient L2. -/
theorem l2_planarPairSeed_integrable (N : ℕ) [NeZero N]
    (m : ℤ) (s : HeightSeed) (U : Gamma0OrbitSpace N → ℂ)
    (hU2 : MemLp U 2 (carrierPushforward N)) :
    Integrable (planarPairSeed N m s.toFun U) chartMeasure := by
  apply (canonical_complex_integrable_iff_chart _).mp
  rw [planarPairSeed_at_chart]
  exact (integrable_indicator_iff strip_measurable).mpr
    (l2_spectralPairSeed_integrableOn_strip N m s U hU2)

/-- Actual Fourier/height identity for measurable L2 representatives. -/
theorem l2_quotient_pairing_eq_fourier (N : ℕ) [NeZero N]
    (m : ℤ) (s : HeightSeed) (U : Gamma0OrbitSpace N → ℂ)
    (hUm : Measurable U) (hU2 : MemLp U 2 (carrierPushforward N)) :
    (∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m s.toFun) u) * U u
      ∂carrierPushforward N) =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) •
        (star (s.toFun y) * actualTestFourier N U m y) := by
  letI : SigmaFinite verticalWeightedMeasure := by
    unfold verticalWeightedMeasure
    infer_instance
  have hi := l2_planarPairSeed_integrable N m s U hU2
  rw [chartMeasure_eq_product] at hi
  rw [l2_quotient_pairing_eq_strip N m s U hUm hU2,
    ← integral_indicator strip_measurable, ← planarPairSeed_at_chart,
    canonical_complex_integral_eq_chart, chartMeasure_eq_product,
    integral_prod_symm _ hi]
  simp_rw [planarPairSeed_horizontal_integral]
  simpa only [verticalWeightedMeasure, NNReal.smul_def, verticalWeight] using
    (integral_withDensity_eq_integral_smul verticalWeight_measurable
      (fun y => star (s.toFun y) * actualTestFourier N U m y)
      (μ := (volume : Measure ℝ).restrict (Ioi 0)))

/-- Arbitrary quotient L2 produces absolutely integrable tested modes. -/
theorem l2_fourier_pairing_integrable (N : ℕ) [NeZero N]
    (m : ℤ) (s : HeightSeed) (U : Gamma0OrbitSpace N → ℂ)
    (hU2 : MemLp U 2 (carrierPushforward N)) :
    IntegrableOn (fun y => ((y⁻¹)^2 : ℝ) •
      (star (s.toFun y) * actualTestFourier N U m y)) (Ioi (0 : ℝ)) := by
  letI : SigmaFinite verticalWeightedMeasure := by
    unfold verticalWeightedMeasure
    infer_instance
  have hi := l2_planarPairSeed_integrable N m s U hU2
  rw [chartMeasure_eq_product] at hi
  have houter := hi.integral_prod_right
  simp_rw [planarPairSeed_horizontal_integral] at houter
  simpa only [NNReal.smul_def, verticalWeight] using
    (integrable_withDensity_iff_integrable_smul verticalWeight_measurable).mp houter

/-- Literal arbitrary-vector Hilbert identity. Lp's canonical representative
is strongly measurable, so no continuity or choice of dense smooth core is required. -/
theorem actualL2_poincare_inner_eq_fourier (N : ℕ) [NeZero N]
    (m : ℤ) (s : HeightSeed) (V : QuotientL2 N) :
    inner ℂ (compactCuspPoincareL2 N m s.toFun s.continuous s.compact s.positive) V =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) •
        (star (s.toFun y) * actualTestFourier N V m y) := by
  rw [← l2_quotient_pairing_eq_fourier N m s V V.stronglyMeasurable.measurable V.memLp,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compactCuspPoincare_memLp_two N m s.toFun s.continuous s.compact
    s.positive).coeFn_toLp] with u hP
  rw [hP]
  simp only [RCLike.inner_apply', Complex.star_def]

end
end ImbalancedChen.Part3.ActualInfinityL2Pairing20261026b
