import ImbalancedChen.Part3CanonicalTensorHyperbolicLaplacianForm
import ImbalancedChen.Part3CompactCrossGreenIdentity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Span.Basic

/-!
SOURCE ONLY / UNCOMPILED, 2026-10-24.

The canonical tensor draft proves the diagonal quadratic identity.  Here
the test tensor and the tensor acted on by the negative Maass Laplacian
are allowed to differ.  The compact cross Green identity imported above
supplies actual one-dimensional integration by parts.  The resulting
mixed form is the concrete weak action on the algebraic tensor test core. Density
of that core in the intended Hilbert/Sobolev domain and self-adjoint
closure are separate questions and are not claimed here.
-/

namespace ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z

private theorem deriv_contDiff_one (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (deriv f) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by simpa using hf
  exact (contDiff_succ_iff_deriv.mp hs).2.2

private theorem cross_second_integrable (u a : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (ha : ContDiff ℝ 2 a)
    (hac : HasCompactSupport a) :
    Integrable (fun x : ℝ => star (u x) * deriv (deriv a) x) := by
  exact (hu.continuous.star.mul
    (deriv_contDiff_one a ha).continuous_deriv_one).integrable_of_hasCompactSupport
      hac.deriv.deriv.mul_left

private theorem cross_mass_integrable (u a : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (ha : ContDiff ℝ 2 a)
    (hac : HasCompactSupport a) :
    Integrable (fun x : ℝ => star (u x) * a x) :=
  (hu.continuous.star.mul ha.continuous).integrable_of_hasCompactSupport
    hac.mul_left

private theorem cross_first_integrable (u a : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (ha : ContDiff ℝ 2 a)
    (hac : HasCompactSupport a) :
    Integrable (fun x : ℝ => star (deriv u x) * deriv a x) :=
  ((deriv_contDiff_one u hu).continuous.star.mul
    (deriv_contDiff_one a ha).continuous).integrable_of_hasCompactSupport
      hac.deriv.mul_left

/-- Unweighted cross term after the hyperbolic density cancels `y²`. -/
def mixedForm (u v a b : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -((star (u p.1) * deriv (deriv a) p.1) *
        (star (v p.2) * b p.2) +
      (star (u p.1) * a p.1) *
        (star (v p.2) * deriv (deriv b) p.2))

/-- Sesquilinear Dirichlet pairing on two pure tensors. -/
def weakTensorEnergy (u v a b : ℝ → ℂ) : ℂ :=
  (∫ x : ℝ, star (deriv u x) * deriv a x) *
      (∫ y : ℝ, star (v y) * b y) +
    (∫ x : ℝ, star (u x) * a x) *
      (∫ y : ℝ, star (deriv v y) * deriv b y)

private theorem cross_integral_hermitian (f g : ℝ → ℂ) :
    (∫ x : ℝ, star (f x) * g x) =
      star (∫ x : ℝ, star (g x) * f x) := by
  change (∫ x : ℝ, Complex.conj (f x) * g x) =
    Complex.conj (∫ x : ℝ, Complex.conj (g x) * f x)
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [map_mul, Complex.conj_conj]
    ring

/-- The tensor weak form is Hermitian on every pair of pure tensors.
This is an algebraic property of the actual first-derivative integrals. -/
theorem weakTensorEnergy_hermitian (u v a b : ℝ → ℂ) :
    weakTensorEnergy u v a b =
      star (weakTensorEnergy a b u v) := by
  unfold weakTensorEnergy
  simp only [star_add, star_mul]
  rw [← cross_integral_hermitian (deriv u) (deriv a),
    ← cross_integral_hermitian v b,
    ← cross_integral_hermitian u a,
    ← cross_integral_hermitian (deriv v) (deriv b)]
  ring

theorem chartWeight_mul_mixedForm (u v a b : ℝ → ℂ)
    {p : ℝ × ℝ} (hp : p ∈ upperChart) :
    chartWeight p •
      (star (tensorFunction u v p) * tensorHyperbolicLaplacian a b p) =
        mixedForm u v a b p := by
  have hy : 0 < p.2 := hp
  have hqReal : (p.2⁻¹) ^ 2 * p.2 ^ 2 = (1 : ℝ) := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hy), one_pow]
  have hq : ((chartWeight p : ℝ) : ℂ) * (p.2 : ℂ) ^ 2 = 1 := by
    change (((p.2⁻¹) ^ 2 : ℝ) : ℂ) * (p.2 : ℂ) ^ 2 = 1
    exact_mod_cast hqReal
  calc
    chartWeight p •
      (star (tensorFunction u v p) * tensorHyperbolicLaplacian a b p) =
        (((chartWeight p : ℝ) : ℂ) * (p.2 : ℂ) ^ 2) *
          mixedForm u v a b p := by
      simp only [tensorFunction, tensorHyperbolicLaplacian,
        mixedForm, NNReal.smul_def, Complex.real_smul, star_mul]
      ring
    _ = mixedForm u v a b p := by rw [hq, one_mul]

theorem mixedForm_integrable (u v a b : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) :
    Integrable (mixedForm u v a b) (volume : Measure (ℝ × ℝ)) := by
  change Integrable (fun p : ℝ × ℝ =>
      -((star (u p.1) * deriv (deriv a) p.1) *
          (star (v p.2) * b p.2) +
        (star (u p.1) * a p.1) *
          (star (v p.2) * deriv (deriv b) p.2)))
    ((volume : Measure ℝ).prod (volume : Measure ℝ))
  exact (((cross_second_integrable u a hu ha hac).mul_prod
    (cross_mass_integrable v b hv hb hbc)).add
    ((cross_mass_integrable u a hu ha hac).mul_prod
      (cross_second_integrable v b hv hb hbc))).neg

/-- The cross form is an integral of first derivatives, by two genuine
real-line integration-by-parts proofs and product Fubini. -/
theorem mixedForm_integral_eq_weakTensorEnergy (u v a b : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) :
    (∫ p : ℝ × ℝ, mixedForm u v a b p) =
      weakTensorEnergy u v a b := by
  have hA := cross_second_integrable u a hu ha hac
  have hB := cross_mass_integrable v b hv hb hbc
  have hC := cross_mass_integrable u a hu ha hac
  have hD := cross_second_integrable v b hv hb hbc
  have hAB : Integrable (fun p : ℝ × ℝ =>
      (star (u p.1) * deriv (deriv a) p.1) *
        (star (v p.2) * b p.2)) := hA.mul_prod hB
  have hCD : Integrable (fun p : ℝ × ℝ =>
      (star (u p.1) * a p.1) *
        (star (v p.2) * deriv (deriv b) p.2)) := hC.mul_prod hD
  calc
    (∫ p : ℝ × ℝ, mixedForm u v a b p) =
        -((∫ p : ℝ × ℝ,
          (star (u p.1) * deriv (deriv a) p.1) *
            (star (v p.2) * b p.2)) +
          (∫ p : ℝ × ℝ,
          (star (u p.1) * a p.1) *
            (star (v p.2) * deriv (deriv b) p.2))) := by
      simp only [mixedForm]
      rw [integral_neg, integral_add hAB hCD]
    _ = -((∫ x : ℝ, star (u x) * deriv (deriv a) x) *
          (∫ y : ℝ, star (v y) * b y) +
        (∫ x : ℝ, star (u x) * a x) *
          (∫ y : ℝ, star (v y) * deriv (deriv b) y)) := by
      rw [integral_prod_mul, integral_prod_mul]
    _ = weakTensorEnergy u v a b := by
      have hx :=
        ImbalancedChen.Part3.CompactCrossGreenIdentity20261024zz.integral_star_mul_secondDeriv
          u a hu ha huc hac
      have hy :=
        ImbalancedChen.Part3.CompactCrossGreenIdentity20261024zz.integral_star_mul_secondDeriv
          v b hv hb hvc hbc
      simp only [weakTensorEnergy]
      rw [hx, hy]
      ring

/-- Canonical upper-half-plane transport of an arbitrary chart integrand.
This is the same measure change used by the diagonal tensor source, now
stated generically so it can be applied to off-diagonal operator values. -/
theorem canonical_integral_eq_chart_integral (F : ℝ × ℝ → ℂ) :
    (∫ z : UpperHalfPlane,
      F (Complex.measurableEquivRealProd (z : ℂ))) =
      ∫ p : ℝ × ℝ, F p ∂chartMeasure := by
  let G : ℝ × ℝ → ℂ := fun p => chartWeight p • F p
  have hvol : (volume : Measure UpperHalfPlane) =
      ((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
        (fun z => (upperDensityNN z : ℝ≥0∞)) := UpperHalfPlane.volume_def
  rw [hvol, integral_withDensity_eq_integral_smul
    upperDensityNN_measurable]
  calc
    (∫ z : UpperHalfPlane,
        upperDensityNN z • F (Complex.measurableEquivRealProd (z : ℂ))
        ∂((volume : Measure ℂ).comap UpperHalfPlane.coe)) =
      ∫ z : UpperHalfPlane,
        G (Complex.measurableEquivRealProd (z : ℂ))
        ∂((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            simp only [G, upperDensityNN_eq_chartWeight]
    _ = ∫ z : ℂ, G (Complex.measurableEquivRealProd z)
          ∂(((volume : Measure ℂ).comap UpperHalfPlane.coe).map
            UpperHalfPlane.coe) := by
          exact (UpperHalfPlane.measurableEmbedding_coe.integral_map
            (μ := (volume : Measure ℂ).comap UpperHalfPlane.coe)
            (g := fun z : ℂ => G (Complex.measurableEquivRealProd z))).symm
    _ = ∫ z : ℂ in Set.range
          (UpperHalfPlane.coe : UpperHalfPlane → ℂ),
          G (Complex.measurableEquivRealProd z)
          ∂(volume : Measure ℂ) := by
          rw [UpperHalfPlane.measurableEmbedding_coe.map_comap
            (volume : Measure ℂ)]
    _ = ∫ p : ℝ × ℝ in upperChart, G p
          ∂(volume : Measure (ℝ × ℝ)) := by
          rw [range_upperHalfPlane_coe_eq_chart_preimage]
          exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
            Complex.measurableEquivRealProd.measurableEmbedding G upperChart
    _ = ∫ p : ℝ × ℝ, F p ∂chartMeasure := by
          unfold chartMeasure
          rw [integral_withDensity_eq_integral_smul
            chartWeight_measurable]
          rfl

/-- Integrability under canonical hyperbolic volume, transported from
the chart with the same two measure-preserving coordinate maps. -/
theorem canonical_integrable_of_chart_integrable (F : ℝ × ℝ → ℂ)
    (hF : Integrable F chartMeasure) :
    Integrable (fun z : UpperHalfPlane =>
      F (Complex.measurableEquivRealProd (z : ℂ))) := by
  let G : ℝ × ℝ → ℂ := fun p => chartWeight p • F p
  have hcoord : IntegrableOn G upperChart
      (volume : Measure (ℝ × ℝ)) := by
    simpa only [G] using
      ((integrable_withDensity_iff_integrable_smul
        chartWeight_measurable).mp hF)
  have hcomplex : Integrable
      (fun z : ℂ => G (Complex.measurableEquivRealProd z))
      ((volume : Measure ℂ).restrict
        (Set.range (UpperHalfPlane.coe : UpperHalfPlane → ℂ))) := by
    rw [range_upperHalfPlane_coe_eq_chart_preimage]
    exact (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).2 hcoord
  have hcomap : Integrable
      (fun z : UpperHalfPlane =>
        G (Complex.measurableEquivRealProd (z : ℂ)))
      ((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
    have hmap : Integrable
        (fun z : ℂ => G (Complex.measurableEquivRealProd z))
        (((volume : Measure ℂ).comap UpperHalfPlane.coe).map
          UpperHalfPlane.coe) := by
      rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]
      exact hcomplex
    exact UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp hmap
  have hvol : (volume : Measure UpperHalfPlane) =
      ((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
        (fun z => (upperDensityNN z : ℝ≥0∞)) := UpperHalfPlane.volume_def
  rw [hvol]
  apply (integrable_withDensity_iff_integrable_smul
    upperDensityNN_measurable).2
  apply hcomap.congr
  exact Filter.Eventually.of_forall fun z => by
    simpa only [G, upperDensityNN_eq_chartWeight]

/-- The off-diagonal Maass pairing is genuinely integrable under
canonical hyperbolic volume for two smooth compact tensors. -/
theorem canonical_mixed_integrable (u v a b : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b) :
    Integrable (fun z : UpperHalfPlane =>
      star (tensorFunctionH u v z) * tensorHyperbolicLaplacianH a b z) := by
  have hchart : Integrable (fun p : ℝ × ℝ =>
      star (tensorFunction u v p) * tensorHyperbolicLaplacian a b p)
      chartMeasure := by
    unfold chartMeasure
    apply (integrable_withDensity_iff_integrable_smul
      chartWeight_measurable).2
    have hbase : Integrable (mixedForm u v a b)
        ((volume : Measure (ℝ × ℝ)).restrict upperChart) :=
      (mixedForm_integrable u v a b hu hv ha hb hac hbc).integrableOn upperChart
    apply hbase.congr
    apply (ae_restrict_iff' upperChart_measurable).2
    exact Filter.Eventually.of_forall fun p hp =>
      (chartWeight_mul_mixedForm u v a b hp).symm
  exact canonical_integrable_of_chart_integrable
    (fun p : ℝ × ℝ =>
      star (tensorFunction u v p) * tensorHyperbolicLaplacian a b p) hchart

/-- The actual negative Maass Laplacian paired with a different compact
test tensor equals its first-derivative weak form under canonical volume.
All four real-line factors lie in the explicit smooth compact tensor core. -/
theorem canonical_weakMaass_on_tensor_core (u v a b : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (hvpos : tsupport v ⊆ Set.Ioi (0 : ℝ)) :
    (∫ z : UpperHalfPlane,
      star (tensorFunctionH u v z) *
        tensorHyperbolicLaplacianH a b z) =
      weakTensorEnergy u v a b := by
  change (∫ z : UpperHalfPlane,
      (fun p : ℝ × ℝ =>
        star (tensorFunction u v p) * tensorHyperbolicLaplacian a b p)
          (Complex.measurableEquivRealProd (z : ℂ))) = _
  rw [canonical_integral_eq_chart_integral]
  unfold chartMeasure
  rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
  change (∫ p in upperChart,
      chartWeight p •
        (star (tensorFunction u v p) * tensorHyperbolicLaplacian a b p)
      ∂(volume : Measure (ℝ × ℝ))) = _
  calc
    (∫ p in upperChart,
      chartWeight p •
        (star (tensorFunction u v p) * tensorHyperbolicLaplacian a b p)
      ∂(volume : Measure (ℝ × ℝ))) =
        ∫ p in upperChart, mixedForm u v a b p
          ∂(volume : Measure (ℝ × ℝ)) := by
      apply setIntegral_congr_fun upperChart_measurable
      intro p hp
      exact chartWeight_mul_mixedForm u v a b hp
    _ = ∫ p : ℝ × ℝ, mixedForm u v a b p := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hyNot : p.2 ∉ tsupport v := by
        intro hy
        exact hp (hvpos hy)
      have hz : v p.2 = 0 := image_eq_zero_of_notMem_tsupport hyNot
      simp [mixedForm, hz]
    _ = weakTensorEnergy u v a b :=
      mixedForm_integral_eq_weakTensorEnergy u v a b
        hu hv ha hb huc hvc hac hbc

/-- Symmetry of the canonical weak Maass action on two compact tensor
test functions.  This is a form statement on the explicit tensor core;
it does not assert self-adjointness of an unbounded closure. -/
theorem canonical_weakMaass_tensor_core_symmetric (u v a b : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (hvpos : tsupport v ⊆ Set.Ioi (0 : ℝ))
    (hbpos : tsupport b ⊆ Set.Ioi (0 : ℝ)) :
    (∫ z : UpperHalfPlane,
      star (tensorFunctionH u v z) *
        tensorHyperbolicLaplacianH a b z) =
      star (∫ z : UpperHalfPlane,
        star (tensorFunctionH a b z) *
          tensorHyperbolicLaplacianH u v z) := by
  rw [canonical_weakMaass_on_tensor_core u v a b
    hu hv ha hb huc hvc hac hbc hvpos]
  rw [canonical_weakMaass_on_tensor_core a b u v
    ha hb hu hv hac hbc huc hvc hbpos]
  exact weakTensorEnergy_hermitian u v a b

/-- The weak action is nonnegative on a diagonal pure tensor of the
explicit smooth compact test core.  The preceding mixed identity is the
new operator statement; positivity follows from the canonical diagonal
energy result. -/
theorem weakMaass_tensor_core_nonneg (u v : ℝ → ℂ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hvpos : tsupport v ⊆ Set.Ioi (0 : ℝ)) :
    0 ≤ (weakTensorEnergy u v u v).re := by
  rw [← canonical_weakMaass_on_tensor_core u v u v
    hu hv hu hv huc hvc huc hvc hvpos]
  exact canonicalTensorHyperbolicLaplacian_form_nonneg
    u v hu hv huc hvc hvpos

/-!
## The finite algebraic tensor core

The following type records exactly the regularity and support properties
used by the cross Green formula. Finite sums of its functions form an
explicit algebraic test core. No Hilbert-space density assertion is made.
-/

structure CompactTensor where
  horizontal : ℝ → ℂ
  vertical : ℝ → ℂ
  horizontal_smooth : ContDiff ℝ 2 horizontal
  vertical_smooth : ContDiff ℝ 2 vertical
  horizontal_compact : HasCompactSupport horizontal
  vertical_compact : HasCompactSupport vertical
  vertical_positive : tsupport vertical ⊆ Set.Ioi (0 : ℝ)

def finiteCoreFunction {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (z : UpperHalfPlane) : ℂ :=
  ∑ i ∈ s, tensorFunctionH (T i).horizontal (T i).vertical z

def finiteCoreLaplacian {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (z : UpperHalfPlane) : ℂ :=
  ∑ i ∈ s, tensorHyperbolicLaplacianH
    (T i).horizontal (T i).vertical z

def finiteCoreEnergy {ι κ : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ t,
    weakTensorEnergy (T i).horizontal (T i).vertical
      (U j).horizontal (U j).vertical

/-- Every cross term in the product of two finite tensor sums is a
canonical integrable Maass pairing. This supplies the integrability
premises used by `integral_finsetSum` in the finite-core identity. -/
private theorem finite_pair_integrable {ι κ : Type*}
    (T : ι → CompactTensor) (U : κ → CompactTensor) (i : ι) (j : κ) :
    Integrable (fun z : UpperHalfPlane =>
      star (tensorFunctionH (T i).horizontal (T i).vertical z) *
        tensorHyperbolicLaplacianH
          (U j).horizontal (U j).vertical z) :=
  canonical_mixed_integrable
    (T i).horizontal (T i).vertical
    (U j).horizontal (U j).vertical
    (T i).horizontal_smooth (T i).vertical_smooth
    (U j).horizontal_smooth (U j).vertical_smooth
    (U j).horizontal_compact (U j).vertical_compact

/-- Actual weak Maass identity on two finite sums of compact tensors.
The double sum retains every off-diagonal cross term. -/
theorem canonical_weakMaass_on_finite_tensor_span
    {ι κ : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) * finiteCoreLaplacian t U z) =
      finiteCoreEnergy s T t U := by
  have hpoint (z : UpperHalfPlane) :
      star (finiteCoreFunction s T z) * finiteCoreLaplacian t U z =
        ∑ i ∈ s, ∑ j ∈ t,
          star (tensorFunctionH (T i).horizontal (T i).vertical z) *
            tensorHyperbolicLaplacianH
              (U j).horizontal (U j).vertical z := by
    simp only [finiteCoreFunction, finiteCoreLaplacian,
      star_sum, Finset.sum_mul, Finset.mul_sum]
  have hinner (i : ι) : Integrable (fun z : UpperHalfPlane =>
      ∑ j ∈ t,
        star (tensorFunctionH (T i).horizontal (T i).vertical z) *
          tensorHyperbolicLaplacianH
            (U j).horizontal (U j).vertical z) :=
    integrable_finsetSum t (fun j _ => finite_pair_integrable T U i j)
  calc
    (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) * finiteCoreLaplacian t U z) =
        ∫ z : UpperHalfPlane,
          ∑ i ∈ s, ∑ j ∈ t,
            star (tensorFunctionH (T i).horizontal (T i).vertical z) *
              tensorHyperbolicLaplacianH
                (U j).horizontal (U j).vertical z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∑ i ∈ s, ∑ j ∈ t,
          (∫ z : UpperHalfPlane,
            star (tensorFunctionH (T i).horizontal (T i).vertical z) *
              tensorHyperbolicLaplacianH
                (U j).horizontal (U j).vertical z) := by
      rw [integral_finsetSum s (fun i _ => hinner i)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum t
        (fun j _ => finite_pair_integrable T U i j)
    _ = finiteCoreEnergy s T t U := by
      unfold finiteCoreEnergy
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact canonical_weakMaass_on_tensor_core
        (T i).horizontal (T i).vertical
        (U j).horizontal (U j).vertical
        (T i).horizontal_smooth (T i).vertical_smooth
        (U j).horizontal_smooth (U j).vertical_smooth
        (T i).horizontal_compact (T i).vertical_compact
        (U j).horizontal_compact (U j).vertical_compact
        (T i).vertical_positive

theorem finiteCoreEnergy_hermitian {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    finiteCoreEnergy s T t U = star (finiteCoreEnergy t U s T) := by
  unfold finiteCoreEnergy
  simp only [star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact weakTensorEnergy_hermitian
    (T i).horizontal (T i).vertical
    (U j).horizontal (U j).vertical

theorem canonical_weakMaass_finite_tensor_span_symmetric
    {ι κ : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) * finiteCoreLaplacian t U z) =
      star (∫ z : UpperHalfPlane,
        star (finiteCoreFunction t U z) * finiteCoreLaplacian s T z) := by
  rw [canonical_weakMaass_on_finite_tensor_span s T t U,
    canonical_weakMaass_on_finite_tensor_span t U s T]
  exact finiteCoreEnergy_hermitian s T t U

/-- Euclidean first derivatives of a pure tensor in the coordinate chart. -/
def tensorDx (T : CompactTensor) (p : ℝ × ℝ) : ℂ :=
  deriv T.horizontal p.1 * T.vertical p.2

def tensorDy (T : CompactTensor) (p : ℝ × ℝ) : ℂ :=
  T.horizontal p.1 * deriv T.vertical p.2

def finiteDx {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (p : ℝ × ℝ) : ℂ :=
  ∑ i ∈ s, tensorDx (T i) p

def finiteDy {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (p : ℝ × ℝ) : ℂ :=
  ∑ i ∈ s, tensorDy (T i) p

private theorem tensorDx_pair_integrable (T U : CompactTensor) :
    Integrable (fun p : ℝ × ℝ =>
      star (tensorDx T p) * tensorDx U p)
      (volume : Measure (ℝ × ℝ)) := by
  have hprod : Integrable (fun p : ℝ × ℝ =>
      (star (deriv T.horizontal p.1) * deriv U.horizontal p.1) *
        (star (T.vertical p.2) * U.vertical p.2)) :=
    (cross_first_integrable T.horizontal U.horizontal
      T.horizontal_smooth U.horizontal_smooth U.horizontal_compact).mul_prod
      (cross_mass_integrable T.vertical U.vertical
        T.vertical_smooth U.vertical_smooth U.vertical_compact)
  apply hprod.congr
  exact Filter.Eventually.of_forall fun p => by
    simp only [tensorDx, star_mul]
    ring

private theorem tensorDy_pair_integrable (T U : CompactTensor) :
    Integrable (fun p : ℝ × ℝ =>
      star (tensorDy T p) * tensorDy U p)
      (volume : Measure (ℝ × ℝ)) := by
  have hprod : Integrable (fun p : ℝ × ℝ =>
      (star (T.horizontal p.1) * U.horizontal p.1) *
        (star (deriv T.vertical p.2) * deriv U.vertical p.2)) :=
    (cross_mass_integrable T.horizontal U.horizontal
      T.horizontal_smooth U.horizontal_smooth U.horizontal_compact).mul_prod
      (cross_first_integrable T.vertical U.vertical
        T.vertical_smooth U.vertical_smooth U.vertical_compact)
  apply hprod.congr
  exact Filter.Eventually.of_forall fun p => by
    simp only [tensorDy, star_mul]
    ring

private theorem tensorDx_pair_integral (T U : CompactTensor) :
    (∫ p : ℝ × ℝ, star (tensorDx T p) * tensorDx U p) =
      (∫ x : ℝ, star (deriv T.horizontal x) * deriv U.horizontal x) *
        (∫ y : ℝ, star (T.vertical y) * U.vertical y) := by
  calc
    (∫ p : ℝ × ℝ, star (tensorDx T p) * tensorDx U p) =
      ∫ p : ℝ × ℝ,
        (star (deriv T.horizontal p.1) * deriv U.horizontal p.1) *
          (star (T.vertical p.2) * U.vertical p.2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [tensorDx, star_mul]
        ring
    _ = _ := by rw [integral_prod_mul]

private theorem tensorDy_pair_integral (T U : CompactTensor) :
    (∫ p : ℝ × ℝ, star (tensorDy T p) * tensorDy U p) =
      (∫ x : ℝ, star (T.horizontal x) * U.horizontal x) *
        (∫ y : ℝ, star (deriv T.vertical y) * deriv U.vertical y) := by
  calc
    (∫ p : ℝ × ℝ, star (tensorDy T p) * tensorDy U p) =
      ∫ p : ℝ × ℝ,
        (star (T.horizontal p.1) * U.horizontal p.1) *
          (star (deriv T.vertical p.2) * deriv U.vertical p.2) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [tensorDy, star_mul]
        ring
    _ = _ := by rw [integral_prod_mul]

private theorem integral_square_finsetSum {ι : Type*}
    (s : Finset ι) (f : ι → ℝ × ℝ → ℂ)
    (hf : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun p : ℝ × ℝ => star (f i p) * f j p)
        (volume : Measure (ℝ × ℝ))) :
    (∫ p : ℝ × ℝ,
      star (∑ i ∈ s, f i p) * (∑ j ∈ s, f j p)) =
      ∑ i ∈ s, ∑ j ∈ s,
        (∫ p : ℝ × ℝ, star (f i p) * f j p) := by
  have hpoint (p : ℝ × ℝ) :
      star (∑ i ∈ s, f i p) * (∑ j ∈ s, f j p) =
        ∑ i ∈ s, ∑ j ∈ s, star (f i p) * f j p := by
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  calc
    (∫ p : ℝ × ℝ,
      star (∑ i ∈ s, f i p) * (∑ j ∈ s, f j p)) =
        ∫ p : ℝ × ℝ,
          ∑ i ∈ s, ∑ j ∈ s, star (f i p) * f j p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∑ i ∈ s, ∑ j ∈ s,
          (∫ p : ℝ × ℝ, star (f i p) * f j p) := by
      rw [integral_finsetSum s (fun i hi =>
        integrable_finsetSum s (fun j hj => hf i hi j hj))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (fun j hj => hf i hi j hj)

/-- The finite form is the sum of the squared horizontal and vertical
derivative norms. All cross terms are retained when the squares expand. -/
theorem finiteCoreEnergy_eq_gradient_integrals {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    finiteCoreEnergy s T s T =
      (∫ p : ℝ × ℝ, star (finiteDx s T p) * finiteDx s T p) +
        (∫ p : ℝ × ℝ, star (finiteDy s T p) * finiteDy s T p) := by
  have hpair (i j : ι) :
      weakTensorEnergy (T i).horizontal (T i).vertical
          (T j).horizontal (T j).vertical =
        (∫ p : ℝ × ℝ, star (tensorDx (T i) p) * tensorDx (T j) p) +
          (∫ p : ℝ × ℝ, star (tensorDy (T i) p) * tensorDy (T j) p) := by
    unfold weakTensorEnergy
    rw [tensorDx_pair_integral, tensorDy_pair_integral]
  calc
    finiteCoreEnergy s T s T =
        ∑ i ∈ s, ∑ j ∈ s,
          ((∫ p : ℝ × ℝ,
              star (tensorDx (T i) p) * tensorDx (T j) p) +
            (∫ p : ℝ × ℝ,
              star (tensorDy (T i) p) * tensorDy (T j) p)) := by
      unfold finiteCoreEnergy
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpair i j
    _ = (∑ i ∈ s, ∑ j ∈ s,
          (∫ p : ℝ × ℝ,
            star (tensorDx (T i) p) * tensorDx (T j) p)) +
        (∑ i ∈ s, ∑ j ∈ s,
          (∫ p : ℝ × ℝ,
            star (tensorDy (T i) p) * tensorDy (T j) p)) := by
      simp only [Finset.sum_add_distrib]
    _ = (∫ p : ℝ × ℝ, star (finiteDx s T p) * finiteDx s T p) +
          (∫ p : ℝ × ℝ, star (finiteDy s T p) * finiteDy s T p) := by
      rw [show (∑ i ∈ s, ∑ j ∈ s,
          (∫ p : ℝ × ℝ,
            star (tensorDx (T i) p) * tensorDx (T j) p)) =
          (∫ p : ℝ × ℝ,
            star (finiteDx s T p) * finiteDx s T p) from by
              simpa only [finiteDx] using
                (integral_square_finsetSum s
                  (fun i => tensorDx (T i))
                  (fun i _ j _ => tensorDx_pair_integrable (T i) (T j))).symm,
        show (∑ i ∈ s, ∑ j ∈ s,
          (∫ p : ℝ × ℝ,
            star (tensorDy (T i) p) * tensorDy (T j) p)) =
          (∫ p : ℝ × ℝ,
            star (finiteDy s T p) * finiteDy s T p) from by
              simpa only [finiteDy] using
                (integral_square_finsetSum s
                  (fun i => tensorDy (T i))
                  (fun i _ j _ => tensorDy_pair_integrable (T i) (T j))).symm]

private theorem re_integral_star_mul_self (f : ℝ × ℝ → ℂ) :
    (∫ p : ℝ × ℝ, star (f p) * f p).re =
      ∫ p : ℝ × ℝ, ‖f p‖ ^ 2 := by
  have hpoint (p : ℝ × ℝ) :
      star (f p) * f p = ((‖f p‖ ^ 2 : ℝ) : ℂ) := by
    calc
      star (f p) * f p = (Complex.normSq (f p) : ℂ) := by
        simpa only [Complex.star_def] using
          (Complex.normSq_eq_conj_mul_self (z := f p)).symm
      _ = ((‖f p‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  simp

/-- Nonnegativity of the actual Maass weak form on the full finite
algebraic tensor span, including all mixed cross terms. -/
theorem finiteCoreEnergy_nonneg {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    0 ≤ (finiteCoreEnergy s T s T).re := by
  rw [finiteCoreEnergy_eq_gradient_integrals]
  rw [Complex.add_re,
    re_integral_star_mul_self (finiteDx s T),
    re_integral_star_mul_self (finiteDy s T)]
  exact add_nonneg
    (integral_nonneg fun p : ℝ × ℝ => sq_nonneg (‖finiteDx s T p‖))
    (integral_nonneg fun p : ℝ × ℝ => sq_nonneg (‖finiteDy s T p‖))

theorem canonical_weakMaass_finite_tensor_span_nonneg {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    0 ≤ (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) * finiteCoreLaplacian s T z).re := by
  rw [canonical_weakMaass_on_finite_tensor_span]
  exact finiteCoreEnergy_nonneg s T

/-!
## Representation independence

The preceding finite sum could a priori be a formula attached only to a
chosen decomposition. The next lemmas identify its Laplacian with the
two coordinate second derivatives of the sum function itself. Hence
equal finite tensor functions have equal Laplacians. Positive vertical
support allows equality on the upper half-plane to extend to the whole
real coordinate plane, where ordinary `deriv` congruence applies.
-/

def finiteChartFunction {ι : Type*} (s : Finset ι)
    (T : ι → CompactTensor) (p : ℝ × ℝ) : ℂ :=
  ∑ i ∈ s, (T i).horizontal p.1 * (T i).vertical p.2

/-- The negative Maass Laplacian as an operation on a chart function,
defined from its actual coordinate derivatives. -/
def chartMaass (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -((p.2 : ℂ) ^ 2 *
    (deriv (deriv (fun x : ℝ => F (x, p.2))) p.1 +
      deriv (deriv (fun y : ℝ => F (p.1, y))) p.2))

private theorem finiteChart_second_x {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (x y : ℝ) :
    deriv (deriv (fun t : ℝ => finiteChartFunction s T (t, y))) x =
      ∑ i ∈ s, deriv (deriv (T i).horizontal) x * (T i).vertical y := by
  have hfirst (t : ℝ) :
      deriv (fun r : ℝ => finiteChartFunction s T (r, y)) t =
        ∑ i ∈ s, deriv (T i).horizontal t * (T i).vertical y := by
    change deriv (fun r : ℝ =>
      ∑ i ∈ s, (T i).horizontal r * (T i).vertical y) t = _
    rw [deriv_fun_sum (fun i _ =>
      ((T i).horizontal_smooth.differentiable (by norm_num) t).mul_const _)]
    simp only [deriv_mul_const_field]
  have hfirst_fun :
      deriv (fun r : ℝ => finiteChartFunction s T (r, y)) =
        (fun t : ℝ =>
          ∑ i ∈ s, deriv (T i).horizontal t * (T i).vertical y) :=
    funext hfirst
  rw [hfirst_fun]
  rw [deriv_fun_sum (fun i _ =>
    (((T i).horizontal_smooth.differentiable_deriv_two) x).mul_const _)]
  simp only [deriv_mul_const_field]

private theorem finiteChart_second_y {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (x y : ℝ) :
    deriv (deriv (fun t : ℝ => finiteChartFunction s T (x, t))) y =
      ∑ i ∈ s, (T i).horizontal x * deriv (deriv (T i).vertical) y := by
  have hfirst (t : ℝ) :
      deriv (fun r : ℝ => finiteChartFunction s T (x, r)) t =
        ∑ i ∈ s, (T i).horizontal x * deriv (T i).vertical t := by
    change deriv (fun r : ℝ =>
      ∑ i ∈ s, (T i).horizontal x * (T i).vertical r) t = _
    rw [deriv_fun_sum (fun i _ =>
      ((T i).vertical_smooth.differentiable (by norm_num) t).const_mul _)]
    simp only [deriv_const_mul_field]
  have hfirst_fun :
      deriv (fun r : ℝ => finiteChartFunction s T (x, r)) =
        (fun t : ℝ =>
          ∑ i ∈ s, (T i).horizontal x * deriv (T i).vertical t) :=
    funext hfirst
  rw [hfirst_fun]
  rw [deriv_fun_sum (fun i _ =>
    (((T i).vertical_smooth.differentiable_deriv_two) y).const_mul _)]
  simp only [deriv_const_mul_field]

/-- The representation formula agrees pointwise with the function-level
coordinate Maass operator. -/
theorem chartMaass_finiteChartFunction {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (p : ℝ × ℝ) :
    chartMaass (finiteChartFunction s T) p =
      ∑ i ∈ s, tensorHyperbolicLaplacian
        (T i).horizontal (T i).vertical p := by
  rw [chartMaass, finiteChart_second_x, finiteChart_second_y]
  simp only [tensorHyperbolicLaplacian]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum, Finset.sum_neg_distrib]

/-- Each finite upper-half-plane function is the restriction of its
coordinate-chart sum. -/
theorem finiteCoreFunction_eq_chart {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane) :
    finiteCoreFunction s T z =
      finiteChartFunction s T
        (Complex.measurableEquivRealProd (z : ℂ)) := by
  rfl

theorem finiteCoreLaplacian_eq_chart {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (z : UpperHalfPlane) :
    finiteCoreLaplacian s T z =
      chartMaass (finiteChartFunction s T)
        (Complex.measurableEquivRealProd (z : ℂ)) := by
  rw [chartMaass_finiteChartFunction]
  rfl

/-- Equality of two finite sums on the upper half-plane extends to the
full real coordinate chart because each vertical factor vanishes at
nonpositive y. -/
theorem finiteChartFunction_eq_of_finiteCoreFunction_eq
    {ι κ : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor)
    (h : finiteCoreFunction s T = finiteCoreFunction t U) :
    finiteChartFunction s T = finiteChartFunction t U := by
  funext p
  by_cases hy : 0 < p.2
  · let z : UpperHalfPlane := ⟨⟨p.1, p.2⟩, hy⟩
    have hz : Complex.measurableEquivRealProd (z : ℂ) = p := by
      simp [z, Complex.measurableEquivRealProd_apply]
    have hp := congrFun h z
    simpa only [finiteCoreFunction_eq_chart, hz] using hp
  · have hzero (V : CompactTensor) : V.vertical p.2 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hy (V.vertical_positive hm)
    have hzT (i : ι) : (T i).vertical p.2 = 0 := hzero (T i)
    have hzU (j : κ) : (U j).vertical p.2 = 0 := hzero (U j)
    simp [finiteChartFunction, hzT, hzU]

/-- The Laplacian of a finite tensor function depends only on the
function, not on a particular finite tensor decomposition. -/
theorem finiteCoreLaplacian_representation_independent
    {ι κ : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor)
    (h : finiteCoreFunction s T = finiteCoreFunction t U) :
    finiteCoreLaplacian s T = finiteCoreLaplacian t U := by
  have hchart := finiteChartFunction_eq_of_finiteCoreFunction_eq s T t U h
  funext z
  simp only [finiteCoreLaplacian_eq_chart, hchart]

/-- Canonical zero extension of any upper-half-plane function to real
coordinates. This makes the operator below a function-level construction
independent of tensor representations. -/
def extendUpper (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℂ :=
  if hp : 0 < p.2 then F ⟨⟨p.1, p.2⟩, hp⟩ else 0

theorem extendUpper_finiteCoreFunction {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    extendUpper (finiteCoreFunction s T) = finiteChartFunction s T := by
  funext p
  by_cases hp : 0 < p.2
  · let z : UpperHalfPlane := ⟨⟨p.1, p.2⟩, hp⟩
    have hz : Complex.measurableEquivRealProd (z : ℂ) = p := by
      simp [z, Complex.measurableEquivRealProd_apply]
    simp only [extendUpper, dif_pos hp]
    change finiteCoreFunction s T z = finiteChartFunction s T p
    rw [finiteCoreFunction_eq_chart, hz]
  · have hzero (V : CompactTensor) : V.vertical p.2 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hp (V.vertical_positive hm)
    have hzT (i : ι) : (T i).vertical p.2 = 0 := hzero (T i)
    simp [extendUpper, hp, finiteChartFunction, hzT]

/-- Function-level Maass operator, obtained from the actual two
coordinate second derivatives of the canonical zero extension. -/
def upperMaass (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  chartMaass (extendUpper F)
    (Complex.measurableEquivRealProd (z : ℂ))

theorem upperMaass_finiteCoreFunction {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    upperMaass (finiteCoreFunction s T) = finiteCoreLaplacian s T := by
  funext z
  rw [upperMaass, extendUpper_finiteCoreFunction]
  exact (finiteCoreLaplacian_eq_chart s T z).symm

/-- An actual subspace of upper-half-plane functions, generated by
smooth compactly supported pure tensors. Membership is a property of
the function, independent of any chosen finite presentation. -/
def finiteTensorCore : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ
    (Set.range (fun T : CompactTensor =>
      tensorFunctionH T.horizontal T.vertical))

theorem finiteCoreFunction_mem_core {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    finiteCoreFunction s T ∈ finiteTensorCore := by
  have hsum :
      (∑ i ∈ s,
        (fun z : UpperHalfPlane =>
          tensorFunctionH (T i).horizontal (T i).vertical z)) ∈
        finiteTensorCore := by
    apply finiteTensorCore.sum_mem
    intro i _
    exact Submodule.subset_span ⟨T i, rfl⟩
  have hfun : finiteCoreFunction s T =
      ∑ i ∈ s,
        (fun z : UpperHalfPlane =>
          tensorFunctionH (T i).horizontal (T i).vertical z) := by
    funext z
    simp only [finiteCoreFunction, Finset.sum_apply]
  rw [hfun]
  exact hsum

/-- The operator is defined on the subspace as a function of its
underlying element. No decomposition is selected. -/
def coreMaass (F : finiteTensorCore) : UpperHalfPlane → ℂ :=
  upperMaass (F : UpperHalfPlane → ℂ)

def coreWeakPairing (F G : finiteTensorCore) : ℂ :=
  ∫ z : UpperHalfPlane, star (F z) * coreMaass G z

theorem coreMaass_finiteCoreFunction {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    coreMaass ⟨finiteCoreFunction s T, finiteCoreFunction_mem_core s T⟩ =
      finiteCoreLaplacian s T :=
  upperMaass_finiteCoreFunction s T

/-- The intrinsic weak pairing on the function subspace agrees with
the finite double-sum form for each presentation. Combined with the
representation-independence theorem, this is a well-defined weak form
on the quotient of finite tensor presentations by function equality. -/
theorem coreWeakPairing_finiteCoreFunctions
    {ι κ : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    coreWeakPairing
      ⟨finiteCoreFunction s T, finiteCoreFunction_mem_core s T⟩
      ⟨finiteCoreFunction t U, finiteCoreFunction_mem_core t U⟩ =
        finiteCoreEnergy s T t U := by
  change (∫ z : UpperHalfPlane,
      star (finiteCoreFunction s T z) *
        upperMaass (finiteCoreFunction t U) z) = _
  rw [upperMaass_finiteCoreFunction]
  exact canonical_weakMaass_on_finite_tensor_span s T t U

end

end ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
