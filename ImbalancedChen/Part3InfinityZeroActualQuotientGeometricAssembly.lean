import ImbalancedChen.Part3InfinityZeroActualFiniteGeometricAssembly
import ImbalancedChen.Part3CompactCuspQuotientGeometricPairing

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The literal sigma0 pullback of the ORIGINAL infinity Poincare sum descends
to the ACTUAL Gamma0 orbit quotient. Matrix conjugation proves its Gamma0
invariance; the actual compact transporter bound proves strip L1 of the
paired seed. Genuine parabolic quotient unfolding and canonical chart
transport then give the finite all-d mixed geometric pairing. Every sum,
phase and measure is the existing actual one. No spectral or Bessel
normalization, assumed Fubini, or canonical replacement series is used.
-/

noncomputable section

namespace ImbalancedChen.Part3.InfinityZeroActualQuotientGeometricAssembly20261026b

open Set MeasureTheory Filter Matrix Matrix.SpecialLinearGroup
open scoped UpperHalfPlane BigOperators Pointwise
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.InfinityZeroActualFiberFourier20261026a
open ImbalancedChen.Part3.InfinityZeroActualFiberGeometricPair20261026a
open ImbalancedChen.Part3.InfinityZeroActualFiniteGeometricAssembly20261026b
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a
open ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.CompactCuspParabolicPairing20261025a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
open ImbalancedChen.Part3.CompactCuspQuotientGeometricPairing20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

/-- The original actual coset sum evaluated at the literal normalized zero chart. -/
def zeroChartTrace (N : ℕ) (hN : 0 < N) (n : ℤ) (φ : ℝ → ℂ)
    (z : UpperHalfPlane) : ℂ :=
  actualCompactPoincare N n φ (zeroSL N hN • z)

/-- The conjugate is an actual integer Gamma0 matrix; no normalizer premise. -/
theorem zeroSL_intertwines (N : ℕ) (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    zeroSL N hN • (g • z) = frickeGamma0 N g • (zeroSL N hN • z) := by
  have hc := frickeSL_conjugate_gamma0 N hN (frickeGamma0 N g)
  rw [frickeGamma0_involutive N hN g] at hc
  have hm : frickeSL N hN * realSL (g : SL(2, ℤ)) =
      realSL (frickeGamma0 N g : SL(2, ℤ)) * frickeSL N hN := by
    rw [← hc]
    group
  have ha := congrArg (fun A : SL(2, ℝ) => A • z) hm
  simpa only [zeroSL_eq_frickeSL, mul_smul, realSL] using ha

theorem zeroChartTrace_gamma0_invariant (N : ℕ) (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    zeroChartTrace N hN n φ (g • z) = zeroChartTrace N hN n φ z := by
  simp only [zeroChartTrace, zeroSL_intertwines, actualCompactPoincare_eq_parabolicTrace]
  exact compactCusp_trace_gamma0_invariant N n φ hcφ hposφ (frickeGamma0 N g) _

/-- Exact unit period comes from the actual width-N integer zero parabolic. -/
theorem zeroChartTrace_periodic (N : ℕ) (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (k : ℤ) (z : UpperHalfPlane) :
    zeroChartTrace N hN n φ (translate k z) = zeroChartTrace N hN n φ z := by
  simp only [zeroChartTrace, translate_eq_vadd,
    ← zeroParabolic_normalized_action N hN k z, actualCompactPoincare_eq_parabolicTrace]
  exact compactCusp_trace_gamma0_invariant N n φ hcφ hposφ
    ⟨zeroParabolic N k, zeroParabolic_mem_gamma0 N k⟩ _

theorem zeroChartTrace_measurable (N : ℕ) (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) : Measurable (zeroChartTrace N hN n φ) := by
  have hs : Measurable (fun z : UpperHalfPlane => zeroSL N hN • z) := by
    change Measurable (fun z : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ (zeroSL N hN)) • z)
    exact (continuous_const_smul _).measurable
  have ht := (parabolicTraceComplex_measurable N _ (fourierRadialSeed_measurable n φ hφ)).comp hs
  simpa only [zeroChartTrace, actualCompactPoincare_eq_parabolicTrace] using ht

/-- A genuine function on the entire actual orbit quotient, defined by the
original scaled coset sum. Representative independence is proved above. -/
def zeroCuspPoincare (N : ℕ) (hN : 0 < N) (n : ℤ) (φ : ℝ → ℂ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (zeroChartTrace N hN n φ) (by
    intro z w hrel
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hrel
    rw [← hg]
    exact zeroChartTrace_gamma0_invariant N hN n φ hcφ hposφ g w)

theorem zeroCuspPoincare_projection (N : ℕ) [NeZero N] (hN : 0 < N) (n : ℤ)
    (φ : ℝ → ℂ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (z : reducedCarrier N) :
    zeroCuspPoincare N hN n φ hcφ hposφ (reducedProjection N z) =
      zeroChartTrace N hN n φ z := rfl

def mixedPairingSeed (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  star (fourierRadialSeed m ψ z) * zeroChartTrace N hN n φ z

theorem mixedPairingSeed_measurable (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ) :
    Measurable (mixedPairingSeed N hN m n ψ φ) :=
  (fourierRadialSeed_measurable m ψ hψ).star.mul (zeroChartTrace_measurable N hN n φ hφ)

theorem mixedPairingSeed_periodic (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∀ k : ℤ, ∀ z, mixedPairingSeed N hN m n ψ φ (translate k z) =
      mixedPairingSeed N hN m n ψ φ z := by
  intro k z
  simp only [mixedPairingSeed, fourierRadialSeed_periodic m ψ k z,
    zeroChartTrace_periodic N hN n φ hcφ hposφ k z]

/-- Strip L1 is derived from the genuine compact-overlap bound, without
any integrability assumption on a periodic seed over all of H. -/
theorem mixedPairingSeed_integrableOn_strip (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    IntegrableOn (mixedPairingSeed N hN m n ψ φ) strip := by
  obtain ⟨C, _hC, hb⟩ := compactCusp_trace_global_bound N n φ hφ hcφ hposφ
  have hfirst := fourierRadialSeed_integrableOn_strip m ψ hψ hcψ hposψ
  apply (hfirst.norm.mul_const C).mono'
    (mixedPairingSeed_measurable N hN m n ψ φ hψ hφ).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change ‖star (fourierRadialSeed m ψ z) * zeroChartTrace N hN n φ z‖ ≤ _
  rw [norm_mul, norm_star]
  have hbound : ‖zeroChartTrace N hN n φ z‖ ≤ C := by
    simpa only [zeroChartTrace, actualCompactPoincare_eq_parabolicTrace] using hb (zeroSL N hN • z)
  exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

theorem mixedPairingSeed_trace (N : ℕ) (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (z : UpperHalfPlane) :
    parabolicTraceComplex N (mixedPairingSeed N hN m n ψ φ) z =
      star (parabolicTraceComplex N (fourierRadialSeed m ψ) z) * zeroChartTrace N hN n φ z := by
  change (∑' q : GammaInfinityCosets N,
    mixedPairingSeed N hN m n ψ φ (parabolicRepresentative N q • z)) = _
  simp only [mixedPairingSeed, zeroChartTrace_gamma0_invariant N hN n φ hcφ hposφ]
  rw [tsum_mul_right, ← tsum_star]
  rfl

theorem mixedPairingSeed_quotient (N : ℕ) [NeZero N] (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    parabolicComplexPoincare N (mixedPairingSeed N hN m n ψ φ) =
      fun u => star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
        zeroCuspPoincare N hN n φ hcφ hposφ u := by
  funext u
  by_cases hu : u ∈ range (reducedProjection N)
  · obtain ⟨z, rfl⟩ := hu
    rw [parabolicComplexPoincare_projection, parabolicComplexPoincare_projection,
      zeroCuspPoincare_projection]
    exact mixedPairingSeed_trace N hN m n ψ φ hcφ hposφ z
  · have hz (F : UpperHalfPlane → ℂ) : parabolicComplexPoincare N F u = 0 :=
      Function.extend_apply' _ _ u hu
    simp only [hz, star_zero, zero_mul]

/-- Genuine mixed spatial quotient unfolding, with the literal sigma0
inside the original second coset sum and the actual quotient measure. -/
theorem mixed_quotient_pairing_unfolding (N : ℕ) [NeZero N] (hN : 0 < N) (m n : ℤ)
    (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
      zeroCuspPoincare N hN n φ hcφ hposφ u ∂carrierPushforward N) =
      ∫ z in strip, mixedPairingSeed N hN m n ψ φ z := by
  rw [← mixedPairingSeed_quotient N hN m n ψ φ hcφ hposφ]
  exact complex_parabolic_quotient_unfolding N _
    (mixedPairingSeed_periodic N hN m n ψ φ hcφ hposφ)
    (mixedPairingSeed_measurable N hN m n ψ φ hψ hφ)
    (mixedPairingSeed_integrableOn_strip N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ)

/-- Literal strip-pair integrand, extended by zero outside the upper chart. -/
def mixedStripPairChart (N : ℕ) (hN : 0 < N) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if hy : 0 < p.2 then
    (Ico (0 : ℝ) 1).indicator
      (fun x => mixedPairingSeed N hN m n ψ φ (horizontalPoint p.2 hy x)) p.1
  else 0

/-- The chart density is the genuine canonical hyperbolic density. -/
def weightedMixedStripPairChart (N : ℕ) (hN : 0 < N) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  chartWeight p • mixedStripPairChart N hN m n ψ φ p

theorem mixedStripPairChart_coord (N : ℕ) (hN : 0 < N) (m n : ℤ) (ψ φ : ℝ → ℂ) (z : UpperHalfPlane) :
    mixedStripPairChart N hN m n ψ φ (Complex.measurableEquivRealProd (z : ℂ)) =
      strip.indicator (mixedPairingSeed N hN m n ψ φ) z := by
  have hpoint : horizontalPoint z.im z.im_pos z.re = z := by
    apply UpperHalfPlane.ext
    ext <;> rfl
  change (if hy : 0 < z.im then
    (Ico (0 : ℝ) 1).indicator
      (fun x => mixedPairingSeed N hN m n ψ φ (horizontalPoint z.im hy x)) z.re else 0) = _
  rw [dif_pos z.im_pos]
  by_cases hx : z.re ∈ Ico (0 : ℝ) 1 <;> simp [strip, hx, hpoint]

theorem weightedMixedStripPairChart_support (N : ℕ) (hN : 0 < N) (m n : ℤ) (ψ φ : ℝ → ℂ) :
    Function.support (weightedMixedStripPairChart N hN m n ψ φ) ⊆ upperChart := by
  intro p hp
  change 0 < p.2
  by_contra hy
  exact hp (by simp [weightedMixedStripPairChart, mixedStripPairChart, hy])

/-- Joint product L1 is transported from the real compact-cusp strip L1
proof. In particular no product-integrability/Fubini premise is assumed. -/
theorem weightedMixedStripPairChart_integrable (N : ℕ) (hN : 0 < N) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (weightedMixedStripPairChart N hN m n ψ φ) (volume : Measure (ℝ × ℝ)) := by
  have hstrip := mixedPairingSeed_integrableOn_strip N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
  have hH : Integrable (fun z : UpperHalfPlane =>
      mixedStripPairChart N hN m n ψ φ (Complex.measurableEquivRealProd (z : ℂ))) := by
    have hind := (integrable_indicator_iff strip_measurable).mpr hstrip
    exact hind.congr (Filter.Eventually.of_forall fun z => (mixedStripPairChart_coord N hN m n ψ φ z).symm)
  have hchart := chart_integrable_of_canonical_integrable _ hH
  have hweighted : IntegrableOn (weightedMixedStripPairChart N hN m n ψ φ) upperChart
      (volume : Measure (ℝ × ℝ)) :=
    (integrable_withDensity_iff_integrable_smul chartWeight_measurable).mp hchart
  exact (integrableOn_iff_integrable_of_support_subset
    (weightedMixedStripPairChart_support N hN m n ψ φ)).mp hweighted

/-- Exact canonical-density x integral, retaining the actual scaled sum. -/
theorem weightedMixedStripPairChart_integral_x (N : ℕ) (hN : 0 < N)
    (m n : ℤ) (ψ φ : ℝ → ℂ) (y : ℝ) :
    (∫ x : ℝ, weightedMixedStripPairChart N hN m n ψ φ (x, y)) =
      mixedActualPairSlice N hN m n ψ φ y := by
  by_cases hy : 0 < y
  · have heq (x : ℝ) : weightedMixedStripPairChart N hN m n ψ φ (x, y) =
        (Ico (0 : ℝ) 1).indicator (fun t => ((y⁻¹ ^ 2 : ℝ) : ℂ) *
          star (fourierRadialSeed m ψ (horizontalPoint y hy t)) *
            actualCompactPoincare N n φ (zeroSL N hN • horizontalPoint y hy t)) x := by
      by_cases hx : x ∈ Ico (0 : ℝ) 1
      · simp only [weightedMixedStripPairChart, mixedStripPairChart, dif_pos hy,
          indicator_of_mem hx, mixedPairingSeed, zeroChartTrace, chartWeight,
          NNReal.smul_def, Complex.real_smul]
        ring
      · simp [weightedMixedStripPairChart, mixedStripPairChart, hy, hx]
    calc
      _ = ∫ x : ℝ, (Ico (0 : ℝ) 1).indicator (fun t => ((y⁻¹ ^ 2 : ℝ) : ℂ) *
          star (fourierRadialSeed m ψ (horizontalPoint y hy t)) *
            actualCompactPoincare N n φ (zeroSL N hN • horizontalPoint y hy t)) x :=
        integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = mixedActualPairSlice N hN m n ψ φ y := by
        rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact (dif_pos hy).symm
  · simp [weightedMixedStripPairChart, mixedStripPairChart, mixedActualPairSlice, hy]

/-- Actual hyperbolic strip integral equals the finite-assembly slices.
Fubini is licensed by the proved joint L1 in the canonical chart. -/
theorem mixed_strip_pairing_eq_integrated_slices (N : ℕ) (hN : 0 < N)
    (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ z in strip, mixedPairingSeed N hN m n ψ φ z) =
      ∫ y : ℝ, mixedActualPairSlice N hN m n ψ φ y := by
  have hG := weightedMixedStripPairChart_integrable N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
  have hprod : Integrable (weightedMixedStripPairChart N hN m n ψ φ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa only [← Measure.volume_eq_prod] using hG
  calc
    _ = ∫ z : UpperHalfPlane, strip.indicator (mixedPairingSeed N hN m n ψ φ) z :=
      (integral_indicator strip_measurable).symm
    _ = ∫ z : UpperHalfPlane,
        mixedStripPairChart N hN m n ψ φ (Complex.measurableEquivRealProd (z : ℂ)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z =>
        (mixedStripPairChart_coord N hN m n ψ φ z).symm)
    _ = ∫ p : ℝ × ℝ, mixedStripPairChart N hN m n ψ φ p ∂chartMeasure :=
      canonical_integral_eq_chart_integral _
    _ = ∫ p in upperChart, weightedMixedStripPairChart N hN m n ψ φ p := by
      rw [chartMeasure, integral_withDensity_eq_integral_smul chartWeight_measurable]
      rfl
    _ = ∫ p : ℝ × ℝ, weightedMixedStripPairChart N hN m n ψ φ p := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      exact notMem_support.mp (fun hs => hp (weightedMixedStripPairChart_support N hN m n ψ φ hs))
    _ = ∫ y : ℝ, ∫ x : ℝ, weightedMixedStripPairChart N hN m n ψ φ (x, y) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod_symm _ hprod
    _ = _ := integral_congr_ae
      (Filter.Eventually.of_forall (weightedMixedStripPairChart_integral_x N hN m n ψ φ))

/-- The literal mixed quotient product is integrable, by true unfolding
of the compact strip-L1 paired seed. -/
theorem mixed_quotient_pair_integrable (N : ℕ) [NeZero N] (hN : 0 < N)
    (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun u => star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
      zeroCuspPoincare N hN n φ hcφ hposφ u) (carrierPushforward N) := by
  rw [← mixedPairingSeed_quotient N hN m n ψ φ hcφ hposφ]
  exact parabolicComplexPoincare_integrable N _
    (mixedPairingSeed_periodic N hN m n ψ φ hcφ hposφ)
    (mixedPairingSeed_measurable N hN m n ψ φ hψ hφ)
    (mixedPairingSeed_integrableOn_strip N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ)

/-- Finite geometric formula for the ACTUAL mixed-cusp spatial quotient
pairing. The original signed quotient, literal sigma0 and N*d^2 kernel
have all been retained; the sole d=0 class contributes only at level one. -/
theorem mixed_quotient_pairing_eq_finite_geometric (N : ℕ) [NeZero N]
    (hN : 0 < N) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℕ+,
      (∫ u, star (parabolicComplexPoincare N (fourierRadialSeed m ψ) u) *
        zeroCuspPoincare N hN n φ hcφ hposφ u ∂carrierPushforward N) =
        (if N = 1 ∧ m = n then ∫ y : ℝ, radialWeight ψ y * φ y else 0) +
        ∑ d ∈ Finset.Icc (1 : ℕ+) C,
          (if N.Coprime (d : ℕ) then
            kloosterman (d : ℕ) (-m * inverseResidue (d : ℕ) (N : ℤ)) (-n) else 0) *
              ∫ x : ℝ, ∫ y : ℝ, mixedOrbitKernel N (d : ℕ) m n ψ φ (x, y) := by
  obtain ⟨C, hC⟩ := integrated_mixedActualPairSlice_eq_finite_geometric N hN m n ψ φ
    hψ hcψ hposψ hφ hcφ hposφ
  refine ⟨C, ?_⟩
  rw [mixed_quotient_pairing_unfolding N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ,
    mixed_strip_pairing_eq_integrated_slices N hN m n ψ φ hψ hcψ hposψ hφ hcφ hposφ]
  exact hC

end ImbalancedChen.Part3.InfinityZeroActualQuotientGeometricAssembly20261026b
