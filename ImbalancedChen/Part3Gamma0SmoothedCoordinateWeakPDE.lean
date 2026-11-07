import ImbalancedChen.Part3ProductConvolutionSecondDerivatives

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Ordinary product convolution of the actual compact Gamma0 quotient
pullback is identified with the original canonical kernel pairings.
The coordinate transport explicitly cancels the canonical y^-2 density.
The twice differentiated ordinary convolution therefore has EXACTLY
the second-kernel integral previously supplied by the native defect
equation. Its right side remains the canonical weighted mass V.
The original variable-height commutator is retained, not set to zero.

This proves a genuine smooth local equation from the actual adjoint
defect condition, without assuming H1, C2, or an equation for the
mollified function. Uniform Caccioppoli and extraction of a weak L2
gradient of the original function are not claimed.
-/

namespace ImbalancedChen.Part3.Gamma0SmoothedCoordinateWeakPDE20261026a

noncomputable section
open Set Function Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution UpperHalfPlane
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalShiftRange20261025a
open ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.Gamma0CompactDefectMollifier20261026a
open ImbalancedChen.Part3.Gamma0TranslatedProductWeakPDE20261026a
open ImbalancedChen.Part3.ProductConvolutionSecondDerivatives20261026a

/-- Actual canonical density cancellation, valid for arbitrary integrands. -/
theorem heightSquared_integral_coordinate (g : UpperHalfPlane → ℂ) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^2 * g z) =
      ∫ z : UpperHalfPlane, g z ∂coordinateMeasure := by
  have hvol : (volume : Measure UpperHalfPlane) =
      coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞)) :=
    UpperHalfPlane.volume_def
  rw [hvol, integral_withDensity_eq_integral_smul upperDensityNN_measurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    rw [upperDensityNN_eq_chartWeight]
    simp only [NNReal.smul_def, Complex.real_smul]
    change (((z.im⁻¹)^2 : ℝ) : ℂ) * ((z.im : ℂ)^2 * g z) = g z
    have hc : (((z.im⁻¹)^2 : ℝ) : ℂ) * (z.im : ℂ)^2 = 1 := by
      have hr : (z.im⁻¹)^2 * z.im^2 = (1 : ℝ) := by
        rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt z.im_pos), one_pow]
      exact_mod_cast hr
    rw [← mul_assoc, hc, one_mul]

/-- Compact localization can be removed in a pairing precisely when
the tested kernel vanishes outside that compact set. -/
theorem localizedPlane_kernel_pair (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} {B : ℝ} (hbound : ∀ z ∈ K, z.im ≤ B)
    (f : QuotientL2 N) (a : Plane → ℂ)
    (hazero : ∀ z ∉ K, a (chartMap z) = 0) :
    (∫ p : Plane, a p * localizedPlane N K B f p) =
      ∫ z : UpperHalfPlane, (z.im : ℂ)^2 * a (chartMap z) * f (orbitProjection N z) := by
  calc
    _ = ∫ p in upperChart, a p * localizedPlane N K B f p := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      simp only [localizedPlane, forwardFunction_zero_outside _ p hp, smul_zero, mul_zero]
    _ = ∫ z : UpperHalfPlane,
        a (chartMap z) * localizedPlane N K B f (chartMap z) ∂coordinateMeasure := by
      rw [← map_coordinateMeasure, chartMap_measurableEmbedding.integral_map]
    _ = ∫ z : UpperHalfPlane, a (chartMap z) * f (orbitProjection N z)
        ∂coordinateMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        rw [localizedPlane_at_upper N hbound f z]
        by_cases hz : z ∈ K
        · simp [compactPullback, hz]
        · simp [compactPullback, hz, hazero z hz]
    _ = _ := by
      rw [← heightSquared_integral_coordinate]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring

theorem complexKernel_first_real (n : ℕ) :
    deriv (complexKernel n) = fun t => (deriv (lineKernel n) t : ℂ) := by
  funext t
  exact (((lineKernel_cinfty n).differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv

theorem complexKernel_second_real (n : ℕ) (t : ℝ) :
    deriv (deriv (complexKernel n)) t = (deriv (deriv (lineKernel n)) t : ℂ) := by
  rw [complexKernel_first_real]
  have hd : ContDiff ℝ ∞ (deriv (lineKernel n)) :=
    (contDiff_infty_iff_deriv.mp (lineKernel_cinfty n)).2
  exact ((hd.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv

theorem secondKernel_real (n : ℕ) (x y : ℝ) (z : UpperHalfPlane) :
    secondKernel n x y z =
      ((deriv (deriv (lineKernel n)) (x - z.re) * lineKernel n (y - z.im) +
        lineKernel n (x - z.re) * deriv (deriv (lineKernel n)) (y - z.im) : ℝ) : ℂ) := by
  simp [secondKernel, complexKernel_second_real, reflectedKernel, reflected, complexKernel]

theorem massKernel_zero_outside (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    {K : Set UpperHalfPlane} (hrect : productRectangle n x y ⊆ K)
    (z : UpperHalfPlane) (hz : z ∉ K) : massKernel n x y z = 0 := by
  have hnot : z ∉ finiteCompactTensorSupportK Finset.univ
      (seedTensors (productSeed n x y hy)) :=
    fun hm => hz (hrect (productSeed_support_rectangle n x y hy hm))
  have hzero : finiteCoreFunction Finset.univ
      (seedTensors (productSeed n x y hy)) z = 0 :=
    notMem_support.mp (fun hm => hnot (finiteCoreFunction_support_subset _ _ hm))
  rw [productSeed_input] at hzero
  simp only [massKernel, hzero, star_zero]

theorem secondKernel_zero_outside (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    {K : Set UpperHalfPlane} (hrect : productRectangle n x y ⊆ K)
    (z : UpperHalfPlane) (hz : z ∉ K) : secondKernel n x y z = 0 := by
  have hnot : z ∉ finiteCompactTensorSupportK Finset.univ
      (seedTensors (productSeed n x y hy)) :=
    fun hm => hz (hrect (productSeed_support_rectangle n x y hy hm))
  have hzero : finiteCoreLaplacian Finset.univ
      (seedTensors (productSeed n x y hy)) z = 0 :=
    notMem_support.mp (fun hm => hnot (finiteCoreLaplacian_support_subset _ _ hm))
  rw [productSeed_output] at hzero
  have hyc : (z.im : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt z.im_pos
  have hraw := (mul_eq_zero.mp (neg_eq_zero.mp hzero)).resolve_left (pow_ne_zero 2 hyc)
  simp only [secondKernel, hraw, star_zero]

def actualProductSmooth (N : ℕ) [NeZero N] (K : Set UpperHalfPlane) (B : ℝ)
    (f : QuotientL2 N) (n : ℕ) : Plane → ℂ :=
  productSmooth n (localizedPlane N K B f)

theorem actualProductSmooth_cinfty (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (f : QuotientL2 N) (n : ℕ) :
    ContDiff ℝ ∞ (actualProductSmooth N K B f n) :=
  productSmooth_cinfty ((localizedPlane_memLp N hK hB f).locallyIntegrable (by norm_num)) n

theorem actualProductSmooth_value (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} {B : ℝ} (hbound : ∀ z ∈ K, z.im ≤ B)
    (f : QuotientL2 N) (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (hrect : productRectangle n x y ⊆ K) :
    actualProductSmooth N K B f n (x, y) = productEuclideanMass N f n x y := by
  let a : Plane → ℂ := fun p => (productKernel n ((x, y) - p) : ℂ)
  have hat (z : UpperHalfPlane) : a (chartMap z) = massKernel n x y z := by
    simpa [a, productKernel, chartMap] using (massKernel_real n x y z).symm
  have hazero : ∀ z ∉ K, a (chartMap z) = 0 := by
    intro z hz
    rw [hat]
    exact massKernel_zero_outside n x y hy hrect z hz
  unfold actualProductSmooth productSmooth
  rw [convolution_eq_swap]
  simp only [planeAction, lsmul_apply, Complex.real_smul]
  calc
    _ = ∫ p : Plane, a p * localizedPlane N K B f p := rfl
    _ = ∫ z : UpperHalfPlane,
        (z.im : ℂ)^2 * a (chartMap z) * f (orbitProjection N z) :=
      localizedPlane_kernel_pair N hbound f a hazero
    _ = _ := by simp only [hat, productEuclideanMass]

/-- The actual second-kernel pairing A is the Euclidean Laplacian of
the genuinely ordinary smoothed local pullback, derived twice. -/
theorem actualProductSmooth_laplacian (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N)
    (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (hrect : productRectangle n x y ⊆ K) :
    euclideanLaplacian (actualProductSmooth N K B f n) (x, y) =
      productSecondRegularization N f n x y := by
  have hg := (localizedPlane_memLp N hK hB f).locallyIntegrable (by norm_num)
  let a : Plane → ℂ := fun p => (euclideanLaplacian (productKernel n) ((x, y) - p) : ℂ)
  have hat (z : UpperHalfPlane) : a (chartMap z) = secondKernel n x y z := by
    simpa [a, productKernel_laplacian, chartMap] using (secondKernel_real n x y z).symm
  have hazero : ∀ z ∉ K, a (chartMap z) = 0 := by
    intro z hz
    rw [hat]
    exact secondKernel_zero_outside n x y hy hrect z hz
  unfold actualProductSmooth productSmooth
  rw [euclideanLaplacian_convolution (productKernel_hasCompactSupport n)
    (productKernel_cinfty n) hg, convolution_eq_swap]
  simp only [planeAction, lsmul_apply, Complex.real_smul]
  calc
    _ = ∫ p : Plane, a p * localizedPlane N K B f p := rfl
    _ = ∫ z : UpperHalfPlane,
        (z.im : ℂ)^2 * a (chartMap z) * f (orbitProjection N z) :=
      localizedPlane_kernel_pair N hbound f a hazero
    _ = _ := by simp only [hat, productSecondRegularization]

/-- Genuine local smoothed elliptic equation for the actual deficiency
vector. V is the smoothed y^-2*f term, not a constant multiple of S. -/
theorem actual_defect_smoothed_equation (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N) (n : ℕ) (x y : ℝ)
    (hy : mollifierRadius n < y) (hrect : productRectangle n x y ⊆ K)
    (hinterior : productRectangle n x y ⊆ reducedCarrier N) :
    euclideanLaplacian (actualProductSmooth N K B f n) (x, y) =
      productMassRegularization N f n x y := by
  rw [actualProductSmooth_laplacian N hK hB hbound f n x y hy hrect]
  exact actual_defect_second_kernel_equation N f hf n x y hy hinterior

theorem actual_defect_smoothed_height_commutator (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N) (n : ℕ) (x y : ℝ)
    (hy : mollifierRadius n < y) (hrect : productRectangle n x y ⊆ K)
    (hinterior : productRectangle n x y ⊆ reducedCarrier N) :
    -((y : ℂ)^2 * euclideanLaplacian (actualProductSmooth N K B f n) (x, y)) +
      actualProductSmooth N K B f n (x, y) =
      ∫ z : UpperHalfPlane, ((z.im : ℂ)^2 - (y : ℂ)^2) *
        massKernel n x y z * f (orbitProjection N z) := by
  rw [actualProductSmooth_laplacian N hK hB hbound f n x y hy hrect,
    actualProductSmooth_value N hbound f n x y hy hrect]
  exact actual_defect_height_commutator N f hf n x y hy hinterior

end
end ImbalancedChen.Part3.Gamma0SmoothedCoordinateWeakPDE20261026a
