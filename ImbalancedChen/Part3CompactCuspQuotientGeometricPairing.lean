import ImbalancedChen.Part3CompactCuspFiniteGeometricIntegral
import ImbalancedChen.Part3MaassWeakOperatorCore

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Literal actual quotient L2 pairing -> actual strip pairing -> canonical
upper-half-plane chart density -> absolutely integrable product Fubini
-> actual compact Poincare Fourier coefficient -> finite geometric
Kloosterman double integrals. All chart integrability is transported from
the proved literal strip L1 supplier, rather than assumed. The original
coset Poincare sum and the orbit-representative trace are identified term
by term using the actual quotient lift. No Bessel or spectral identity.
-/

namespace ImbalancedChen.Part3.CompactCuspQuotientGeometricPairing20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a
open ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.CompactCuspParabolicL220261025a
open ImbalancedChen.Part3.CompactCuspParabolicPairing20261025a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
open ImbalancedChen.Part3.CompactCuspFiniteGeometricIntegral20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.CoprimeCRTSourceOnly

/-- The two actual parabolic definitions agree, with their actual chosen
representatives and their actual quotient lift. No convergence assumption
is needed for this termwise equality. -/
theorem actualCompactPoincare_eq_parabolicTrace (N : ℕ) (n : ℤ)
    (φ : ℝ → ℂ) (z : UpperHalfPlane) :
    actualCompactPoincare N n φ z = parabolicTraceComplex N (fourierRadialSeed n φ) z := by
  apply tsum_congr
  intro q
  have h := periodicSeedOnCosets_mk N (fourierRadialSeed n φ)
    (fourierRadialSeed_integer_periodic n φ) z (Quotient.out q)
  simpa only [Quotient.out_eq] using h

/-- Reverse integrability transport through the ACTUAL canonical measure.
This proves the direction required by Fubini from the already proved
hyperbolic strip L1 theorem. -/
theorem chart_integrable_of_canonical_integrable (F : ℝ × ℝ → ℂ)
    (hF : Integrable (fun z : UpperHalfPlane => F (Complex.measurableEquivRealProd (z : ℂ)))) :
    Integrable F chartMeasure := by
  let G : ℝ × ℝ → ℂ := fun p => chartWeight p • F p
  have hvol : (volume : Measure UpperHalfPlane) =
      ((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
        (fun z => (upperDensityNN z : ℝ≥0∞)) := UpperHalfPlane.volume_def
  rw [hvol] at hF
  have hweighted := (integrable_withDensity_iff_integrable_smul upperDensityNN_measurable).mp hF
  have hcomap : Integrable
      (fun z : UpperHalfPlane => G (Complex.measurableEquivRealProd (z : ℂ)))
      ((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
    apply hweighted.congr
    exact Filter.Eventually.of_forall fun z => by simp only [G, upperDensityNN_eq_chartWeight]
  have hmap : Integrable (fun z : ℂ => G (Complex.measurableEquivRealProd z))
      (((volume : Measure ℂ).comap UpperHalfPlane.coe).map UpperHalfPlane.coe) :=
    UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mpr hcomap
  rw [UpperHalfPlane.measurableEmbedding_coe.map_comap,
    range_upperHalfPlane_coe_eq_chart_preimage] at hmap
  have hcoord : IntegrableOn G upperChart (volume : Measure (ℝ × ℝ)) :=
    (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).1 hmap
  exact (integrable_withDensity_iff_integrable_smul chartWeight_measurable).mpr hcoord

/-- Literal strip-pair integrand, extended by zero outside the upper chart. -/
def stripPairChart (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if hy : 0 < p.2 then
    (Ico (0 : ℝ) 1).indicator
      (fun x => cuspPairingSeed N m n ψ φ (horizontalPoint p.2 hy x)) p.1
  else 0

/-- The chart density is the genuine canonical hyperbolic density. -/
def weightedStripPairChart (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  chartWeight p • stripPairChart N m n ψ φ p

theorem stripPairChart_coord (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (z : UpperHalfPlane) :
    stripPairChart N m n ψ φ (Complex.measurableEquivRealProd (z : ℂ)) =
      strip.indicator (cuspPairingSeed N m n ψ φ) z := by
  have hpoint : horizontalPoint z.im z.im_pos z.re = z := by
    apply UpperHalfPlane.ext
    ext <;> rfl
  change (if hy : 0 < z.im then
    (Ico (0 : ℝ) 1).indicator
      (fun x => cuspPairingSeed N m n ψ φ (horizontalPoint z.im hy x)) z.re else 0) = _
  rw [dif_pos z.im_pos]
  by_cases hx : z.re ∈ Ico (0 : ℝ) 1 <;> simp [strip, hx, hpoint]

theorem weightedStripPairChart_support (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) :
    Function.support (weightedStripPairChart N m n ψ φ) ⊆ upperChart := by
  intro p hp
  change 0 < p.2
  by_contra hy
  exact hp (by simp [weightedStripPairChart, stripPairChart, hy])

/-- Joint product L1 is transported from the real compact-cusp strip L1
proof. In particular no product-integrability/Fubini premise is assumed. -/
theorem weightedStripPairChart_integrable (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (weightedStripPairChart N m n ψ φ) (volume : Measure (ℝ × ℝ)) := by
  have hstrip := cuspPairingSeed_integrableOn_strip N m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
  have hH : Integrable (fun z : UpperHalfPlane =>
      stripPairChart N m n ψ φ (Complex.measurableEquivRealProd (z : ℂ))) := by
    have hind := (integrable_indicator_iff strip_measurable).mpr hstrip
    exact hind.congr (Filter.Eventually.of_forall fun z => (stripPairChart_coord N m n ψ φ z).symm)
  have hchart := chart_integrable_of_canonical_integrable _ hH
  have hweighted : IntegrableOn (weightedStripPairChart N m n ψ φ) upperChart
      (volume : Measure (ℝ × ℝ)) :=
    (integrable_withDensity_iff_integrable_smul chartWeight_measurable).mp hchart
  exact (integrableOn_iff_integrable_of_support_subset
    (weightedStripPairChart_support N m n ψ φ)).mp hweighted

/-- The inner x-integral is precisely the actual Fourier coefficient.
The star on the first seed gives phase -m, not +m. -/
theorem weightedStripPairChart_integral_x (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (y : ℝ) :
    (∫ x : ℝ, weightedStripPairChart N m n ψ φ (x, y)) =
      weightedActualPoincareFourier N m n ψ φ y := by
  by_cases hy : 0 < y
  · have heq (x : ℝ) : weightedStripPairChart N m n ψ φ (x, y) =
        (Ico (0 : ℝ) 1).indicator (fun t => radialWeight ψ y *
          (phase (-m) t * actualCompactPoincare N n φ (horizontalPoint y hy t))) x := by
      by_cases hx : x ∈ Ico (0 : ℝ) 1
      · simp only [weightedStripPairChart, stripPairChart, dif_pos hy, indicator_of_mem hx]
        rw [cuspPairingSeed, ← actualCompactPoincare_eq_parabolicTrace]
        simp only [fourierRadialSeed, horizontalPoint, star_mul', Complex.star_def,
          ← AddCircle.fourier_neg, NNReal.smul_def, Complex.real_smul]
        change (((y⁻¹ ^ 2 : ℝ) : ℂ) *
          ((AddCircle.fourier (-m) (x : UnitAddCircle) * star (ψ y)) * _)) = _
        dsimp [radialWeight, phase]
        ring
      · simp [weightedStripPairChart, stripPairChart, hy, hx]
    calc
      _ = ∫ x : ℝ, (Ico (0 : ℝ) 1).indicator (fun t => radialWeight ψ y *
            (phase (-m) t * actualCompactPoincare N n φ (horizontalPoint y hy t))) x :=
        integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = radialWeight ψ y * ∫ x in Ico (0 : ℝ) 1,
          phase (-m) x * actualCompactPoincare N n φ (horizontalPoint y hy x) := by
        rw [integral_indicator measurableSet_Ico, integral_const_mul]
      _ = weightedActualPoincareFourier N m n ψ φ y := by
        rw [integral_Ico_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rfl
  · simp [weightedStripPairChart, stripPairChart, weightedActualPoincareFourier, hy]

/-- Actual canonical strip pairing equals the weighted Fourier expression,
with Fubini justified by the transported genuine joint L1 theorem. -/
theorem compactCusp_strip_pairing_eq_weightedFourier (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ z in strip, cuspPairingSeed N m n ψ φ z) =
      ∫ y : ℝ, weightedActualPoincareFourier N m n ψ φ y := by
  have hG := weightedStripPairChart_integrable N m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
  have hprod : Integrable (weightedStripPairChart N m n ψ φ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa only [← Measure.volume_eq_prod] using hG
  calc
    _ = ∫ z : UpperHalfPlane, strip.indicator (cuspPairingSeed N m n ψ φ) z :=
      (integral_indicator strip_measurable).symm
    _ = ∫ z : UpperHalfPlane,
        stripPairChart N m n ψ φ (Complex.measurableEquivRealProd (z : ℂ)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => (stripPairChart_coord N m n ψ φ z).symm)
    _ = ∫ p : ℝ × ℝ, stripPairChart N m n ψ φ p ∂chartMeasure :=
      canonical_integral_eq_chart_integral _
    _ = ∫ p in upperChart, weightedStripPairChart N m n ψ φ p := by
      rw [chartMeasure, integral_withDensity_eq_integral_smul chartWeight_measurable]
      rfl
    _ = ∫ p : ℝ × ℝ, weightedStripPairChart N m n ψ φ p := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      exact notMem_support.mp (fun hs => hp (weightedStripPairChart_support N m n ψ φ hs))
    _ = ∫ y : ℝ, ∫ x : ℝ, weightedStripPairChart N m n ψ φ (x, y) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod_symm _ hprod
    _ = _ := integral_congr_ae
      (Filter.Eventually.of_forall (weightedStripPairChart_integral_x N m n ψ φ))

/-- Literal actual quotient L2 inner product has the finite geometric
Kloosterman double-integral expansion. The cutoff is DERIVED from the two
actual compact positive supports. The diagonal occurs exactly once.
Bessel evaluation and spectral expansion remain separate open obligations. -/
theorem compactCuspPoincareL2_inner_eq_finite_geometric (N : ℕ) [NeZero N]
    (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℕ+,
      inner ℂ (compactCuspPoincareL2 N m ψ hψ hcψ hposψ)
        (compactCuspPoincareL2 N n φ hφ hcφ hposφ) =
      (if m = n then ∫ y : ℝ, radialWeight ψ y * φ y else 0) +
      ∑ c ∈ Finset.Icc (1 : ℕ+) C,
        if N ∣ (c : ℕ) then kloosterman (c : ℕ) m n *
          ∫ x : ℝ, ∫ y : ℝ, geometricPairKernel (c : ℝ) m n ψ φ (x, y)
        else 0 := by
  obtain ⟨C, hC⟩ := exists_integrated_actualFourier_finite_geometric N m n ψ φ
    hψ hcψ hposψ hφ hcφ hposφ
  refine ⟨C, ?_⟩
  rw [compactCuspPoincareL2_inner_unfolding N m n ψ φ hψ hcψ hposψ hφ hcφ hposφ]
  change (∫ z in strip, cuspPairingSeed N m n ψ φ z) = _
  rw [compactCusp_strip_pairing_eq_weightedFourier N m n ψ φ hψ hcψ hposψ hφ hcφ hposφ]
  exact hC

end
end ImbalancedChen.Part3.CompactCuspQuotientGeometricPairing20261025a
