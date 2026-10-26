import ImbalancedChen.Part3Gamma0SmoothedCoordinateWeakPDE
import ImbalancedChen.Part3CompactProductBochnerAEJoin

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Fix the compact localization and a POSITIVE lower height margin a first.
The bounded potential cap (max(a,y))^-2 gives a compact ordinary L2
function, with norm at most a^-2 times the actual localized input norm.
The native product-average contraction and its proved scalar AE bridge
then give the SAME bound for every smoothing scale. The two product
kernels are identified by their literal bump data, not by normalization
alone. On every legal interior test rectangle the smoothed potential is
exactly the canonical weighted mass V in the actual defect equation.

No H1 regularity, Caccioppoli estimate or gradient extraction is assumed
or concluded. All norms below use ordinary coordinate L2.
-/

namespace ImbalancedChen.Part3.Gamma0SmoothedPotentialL2Budget20261026a

noncomputable section
open Set Function Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalShiftRange20261025a
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.Gamma0CompactDefectMollifier20261026a
open ImbalancedChen.Part3.Gamma0TranslatedProductWeakPDE20261026a
open ImbalancedChen.Part3.ProductConvolutionSecondDerivatives20261026a
open ImbalancedChen.Part3.Gamma0SmoothedCoordinateWeakPDE20261026a

/-- Both records literally use rIn=r/2 and rOut=r, including the same
normalized bump function. Equality is stronger than equal total mass. -/
theorem productKernel_eq_realProductKernel (n : ℕ) :
    productKernel n = CompactC2ProductMollifier20261026a.realProductKernel
      (mollifierRadius n) (mollifierRadius_pos n) := rfl

theorem productSmooth_eq_nativeSmoothing (n : ℕ) (g : Plane → ℂ) :
    productSmooth n g = CompactC2ProductMollifier20261026a.productSmoothing
      (mollifierRadius n) (mollifierRadius_pos n) g := by
  funext p
  simp only [productSmooth, CompactC2ProductMollifier20261026a.productSmoothing,
    CompactC2ProductMollifier20261026a.convolutionC, convolution_def,
    planeAction, lsmul_apply, ContinuousLinearMap.mul_apply',
    CompactC2ProductMollifier20261026a.complexProductKernel_eq,
    ← productKernel_eq_realProductKernel, Complex.real_smul]

theorem productSmooth_memLp {g : Plane → ℂ} (hg : MemLp g 2 volume)
    (hgc : HasCompactSupport g) (n : ℕ) : MemLp (productSmooth n g) 2 volume := by
  rw [productSmooth_eq_nativeSmoothing]
  exact CompactProductBochnerAEJoin20261026a.smoothing_memLp hg hgc
    (mollifierRadius n) (mollifierRadius_pos n)

theorem productSmooth_L2_contraction {g : Plane → ℂ} (hg : MemLp g 2 volume)
    (hgc : HasCompactSupport g) (n : ℕ) :
    ‖(productSmooth_memLp hg hgc n).toLp (productSmooth n g)‖ ≤ ‖hg.toLp g‖ := by
  have h := ProductKernelL2TranslationAverage20261026a.productAverage_norm_le
    (mollifierRadius n) (mollifierRadius_pos n) (hg.toLp g)
  rw [CompactProductBochnerAEJoin20261026a.productAverage_eq_scalar_toLp hg hgc
    (mollifierRadius n) (mollifierRadius_pos n)] at h
  simpa only [← productSmooth_eq_nativeSmoothing] using h

def cappedPotential (a : ℝ) (p : Plane) : ℝ := ((max a p.2)⁻¹)^2

theorem cappedPotential_continuous {a : ℝ} (ha : 0 < a) : Continuous (cappedPotential a) :=
  ((continuous_const.max continuous_snd).inv₀
    (fun p => ne_of_gt (ha.trans_le (le_max_left _ _)))).pow 2

theorem cappedPotential_nonneg (a : ℝ) (p : Plane) : 0 ≤ cappedPotential a p :=
  sq_nonneg _

theorem cappedPotential_le {a : ℝ} (ha : 0 < a) (p : Plane) :
    cappedPotential a p ≤ (a⁻¹)^2 := by
  have hmax : 0 < max a p.2 := ha.trans_le (le_max_left _ _)
  have hi : (max a p.2)⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha (le_max_left a p.2)
  have hnonneg : 0 ≤ (max a p.2)⁻¹ := (inv_pos.mpr hmax).le
  have hp := mul_nonneg (sub_nonneg.mpr hi) (add_nonneg (inv_pos.mpr ha).le hnonneg)
  change ((max a p.2)⁻¹)^2 ≤ (a⁻¹)^2
  nlinarith

theorem localizedPlane_hasCompactSupport (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ}
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N) :
    HasCompactSupport (localizedPlane N K B f) := by
  have hc : Continuous chartMap :=
    UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im
  apply HasCompactSupport.of_support_subset_isCompact (hK.image hc)
  intro p hp
  have hn : localizedComplex N K B f (Complex.measurableEquivRealProd.symm p) ≠ 0 := by
    simpa only [localizedComplex, Function.comp_apply,
      MeasurableEquiv.apply_symm_apply] using hp
  obtain ⟨z, hz, hzp⟩ := localizedComplex_support N hbound f hn
  refine ⟨z, hz, ?_⟩
  change Complex.measurableEquivRealProd (z : ℂ) = p
  rw [hzp, MeasurableEquiv.apply_symm_apply]

theorem actualProductSmooth_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N) (n : ℕ) :
    MemLp (actualProductSmooth N K B f n) 2 volume :=
  productSmooth_memLp (localizedPlane_memLp N hK hB f)
    (localizedPlane_hasCompactSupport N hK hbound f) n

theorem actualProductSmooth_uniform_L2_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N) (n : ℕ) :
    ‖(actualProductSmooth_memLp N hK hB hbound f n).toLp (actualProductSmooth N K B f n)‖ ≤
      ‖(localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)‖ :=
  productSmooth_L2_contraction (localizedPlane_memLp N hK hB f)
    (localizedPlane_hasCompactSupport N hK hbound f) n

def localizedPotential (N : ℕ) [NeZero N] (K : Set UpperHalfPlane) (B a : ℝ)
    (f : QuotientL2 N) (p : Plane) : ℂ :=
  cappedPotential a p • localizedPlane N K B f p

theorem localizedPotential_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (f : QuotientL2 N) :
    MemLp (localizedPotential N K B a f) 2 volume := by
  have hF := localizedPlane_memLp N hK hB f
  apply (hF.const_smul ((a⁻¹)^2)).of_le
    ((cappedPotential_continuous ha).aestronglyMeasurable.smul hF.aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    simp only [localizedPotential, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (cappedPotential_nonneg a p), abs_of_nonneg (sq_nonneg (a⁻¹))]
    exact mul_le_mul_of_nonneg_right (cappedPotential_le ha p) (norm_nonneg _)

theorem localizedPotential_hasCompactSupport (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N) :
    HasCompactSupport (localizedPotential N K B a f) := by
  have hF := localizedPlane_hasCompactSupport N hK hbound f
  apply HasCompactSupport.of_support_subset_isCompact hF.isCompact
  intro p hp
  apply subset_closure
  intro hz
  exact hp (by simp [localizedPotential, hz])

theorem localizedPotential_norm_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (f : QuotientL2 N) :
    ‖(localizedPotential_memLp N hK hB ha f).toLp (localizedPotential N K B a f)‖ ≤
      (a⁻¹)^2 * ‖(localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)‖ := by
  have hF := localizedPlane_memLp N hK hB f
  have hP := localizedPotential_memLp N hK hB ha f
  have hdom : ∀ᵐ p ∂(volume : Measure Plane),
      ‖localizedPotential N K B a f p‖ ≤ ‖(((a⁻¹)^2) • localizedPlane N K B f) p‖ := by
    exact Eventually.of_forall fun p => by
      simp only [localizedPotential, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (cappedPotential_nonneg a p), abs_of_nonneg (sq_nonneg (a⁻¹))]
      exact mul_le_mul_of_nonneg_right (cappedPotential_le ha p) (norm_nonneg _)
  have he := eLpNorm_mono_ae hdom (p := (2 : ℝ≥0∞))
  have hn : ‖hP.toLp (localizedPotential N K B a f)‖ ≤
      ‖(hF.const_smul ((a⁻¹)^2)).toLp (((a⁻¹)^2) • localizedPlane N K B f)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono (hF.const_smul ((a⁻¹)^2)).2.ne he
  simpa only [MemLp.toLp_const_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (a⁻¹))] using hn

def potentialSmooth (N : ℕ) [NeZero N] (K : Set UpperHalfPlane) (B a : ℝ)
    (f : QuotientL2 N) (n : ℕ) : Plane → ℂ :=
  productSmooth n (localizedPotential N K B a f)

theorem potentialSmooth_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (f : QuotientL2 N) (n : ℕ) : MemLp (potentialSmooth N K B a f n) 2 volume :=
  productSmooth_memLp (localizedPotential_memLp N hK hB ha f)
    (localizedPotential_hasCompactSupport N hK hbound f) n

/-- The compact lower height margin a is fixed BEFORE n. Hence this
genuine forcing L2 bound is uniform in the mollifier scale. -/
theorem potentialSmooth_uniform_L2_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (f : QuotientL2 N) (n : ℕ) :
    ‖(potentialSmooth_memLp N hK hB ha hbound f n).toLp (potentialSmooth N K B a f n)‖ ≤
      (a⁻¹)^2 * ‖(localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)‖ :=
  (productSmooth_L2_contraction (localizedPotential_memLp N hK hB ha f)
    (localizedPotential_hasCompactSupport N hK hbound f) n).trans
      (localizedPotential_norm_le N hK hB ha f)

theorem potentialSmooth_eq_nativeMass (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} {B a : ℝ} (ha : 0 < a)
    (hbound : ∀ z ∈ K, z.im ≤ B) (hlower : ∀ z ∈ K, a ≤ z.im)
    (f : QuotientL2 N) (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (hrect : productRectangle n x y ⊆ K) :
    potentialSmooth N K B a f n (x, y) = productMassRegularization N f n x y := by
  let b : Plane → ℂ := fun p =>
    (productKernel n ((x, y) - p) : ℂ) * (cappedPotential a p : ℂ)
  have hkernel (z : UpperHalfPlane) :
      (productKernel n ((x, y) - chartMap z) : ℂ) = massKernel n x y z := by
    simpa [productKernel, chartMap] using (massKernel_real n x y z).symm
  have hbzero : ∀ z ∉ K, b (chartMap z) = 0 := by
    intro z hz
    simp only [b, hkernel, massKernel_zero_outside n x y hy hrect z hz, zero_mul]
  unfold potentialSmooth productSmooth
  rw [convolution_eq_swap]
  simp only [planeAction, lsmul_apply, localizedPotential, Complex.real_smul]
  calc
    _ = ∫ p : Plane, b p * localizedPlane N K B f p := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by dsimp [b]; ring
    _ = ∫ z : UpperHalfPlane,
        (z.im : ℂ)^2 * b (chartMap z) * f (orbitProjection N z) :=
      localizedPlane_kernel_pair N hbound f b hbzero
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp [b]
        rw [hkernel]
        by_cases hz : z ∈ K
        · have hcap : cappedPotential a (chartMap z) = (z.im⁻¹)^2 := by
            change ((max a z.im)⁻¹)^2 = (z.im⁻¹)^2
            rw [max_eq_right (hlower z hz)]
          rw [hcap]
          have hc : (z.im : ℂ)^2 * (((z.im⁻¹)^2 : ℝ) : ℂ) = 1 := by
            have hr : z.im^2 * (z.im⁻¹)^2 = (1 : ℝ) := by
              rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt z.im_pos), one_pow]
            exact_mod_cast hr
          calc
            _ = ((z.im : ℂ)^2 * (((z.im⁻¹)^2 : ℝ) : ℂ)) *
                (massKernel n x y z * f (orbitProjection N z)) := by ring
            _ = _ := by rw [hc, one_mul]
        · simp [massKernel_zero_outside n x y hy hrect z hz]

/-- Actual local defect equation with a globally ordinary-L2 forcing
whose preceding budget is uniform in n. -/
theorem actual_smoothed_equation_with_L2_forcing (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N) (n : ℕ) (x y : ℝ)
    (hy : mollifierRadius n < y) (hrect : productRectangle n x y ⊆ K)
    (hinterior : productRectangle n x y ⊆ reducedCarrier N) :
    euclideanLaplacian (actualProductSmooth N K B f n) (x, y) =
      potentialSmooth N K B a f n (x, y) := by
  rw [actual_defect_smoothed_equation N hK hB hbound f hf n x y hy hrect hinterior]
  exact (potentialSmooth_eq_nativeMass N ha hbound hlower f n x y hy hrect).symm

end
end ImbalancedChen.Part3.Gamma0SmoothedPotentialL2Budget20261026a
