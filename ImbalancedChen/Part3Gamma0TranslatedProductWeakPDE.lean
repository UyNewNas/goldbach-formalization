import ImbalancedChen.Part3Gamma0CompactDefectMollifier
import ImbalancedChen.Part3Gamma0ActualAdjointInteriorWeakEquation
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.RealDeriv

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Explicit one-dimensional normalized kernels, using the radius already
fixed by the actual compact-mollifier construction, give reflected
product tests in the EXISTING finite smooth tensor core. Their CLOSED
support rectangles are controlled, their actual second derivatives
are computed, and the native actual minimal-adjoint (-1) defect equation
applies to each test when its rectangle lies inside the reduced carrier.

The resulting second-kernel equation retains the original height weight.
Its Euclidean-mass residual has an exact variable-height commutator.
The product kernel here is NOT identified with the earlier radial
complex-plane kernel. No uniform gradient bound, H1 regularity, or
unjustified commutation of a variable-coefficient operator is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0TranslatedProductWeakPDE20261026a

noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane Topology ContDiff
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalShiftRange20261025a
open ImbalancedChen.Part3.Gamma0ActualAdjointInteriorWeakEquation20261025a
open ImbalancedChen.Part3.Gamma0CompactDefectMollifier20261026a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a

def lineBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := mollifierRadius n / 2
  rOut := mollifierRadius n
  rIn_pos := half_pos (mollifierRadius_pos n)
  rIn_lt_rOut := half_lt_self (mollifierRadius_pos n)

def lineKernel (n : ℕ) : ℝ → ℝ := (lineBump n).normed volume

def complexKernel (n : ℕ) (t : ℝ) : ℂ := (lineKernel n t : ℂ)

theorem lineKernel_integral (n : ℕ) : (∫ t : ℝ, lineKernel n t) = 1 :=
  (lineBump n).integral_normed

theorem lineKernel_nonneg (n : ℕ) (t : ℝ) : 0 ≤ lineKernel n t :=
  (lineBump n).nonneg_normed t

def productKernel (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  lineKernel n p.1 * lineKernel n p.2

theorem productKernel_cinfty (n : ℕ) : ContDiff ℝ ∞ (productKernel n) :=
  ((lineBump n).contDiff_normed.comp contDiff_fst).mul
    ((lineBump n).contDiff_normed.comp contDiff_snd)

theorem productKernel_nonneg (n : ℕ) (p : ℝ × ℝ) : 0 ≤ productKernel n p :=
  mul_nonneg (lineKernel_nonneg n p.1) (lineKernel_nonneg n p.2)

theorem productKernel_integral (n : ℕ) : (∫ p : ℝ × ℝ, productKernel n p) = 1 := by
  change (∫ p : ℝ × ℝ, lineKernel n p.1 * lineKernel n p.2) = 1
  simp only [integral_prod_mul, lineKernel_integral, one_mul]

theorem productKernel_hasCompactSupport (n : ℕ) :
    HasCompactSupport (productKernel n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((lineBump n).hasCompactSupport_normed.prod (lineBump n).hasCompactSupport_normed)
  intro p hp
  exact ⟨subset_closure (mul_ne_zero_iff.mp hp).1,
    subset_closure (mul_ne_zero_iff.mp hp).2⟩

theorem complexKernel_cinfty (n : ℕ) : ContDiff ℝ ∞ (complexKernel n) :=
  Complex.ofRealCLM.contDiff.comp (lineBump n).contDiff_normed

def reflected (h : ℝ → ℂ) (c t : ℝ) : ℂ := h (c - t)

theorem reflected_deriv {h : ℝ → ℂ} (hh : Differentiable ℝ h) (c t : ℝ) :
    deriv (reflected h c) t = -(deriv h (c - t)) := by
  simpa only [reflected, Function.comp_def, zero_sub, neg_smul, one_smul] using
    ((hh (c - t)).hasDerivAt.scomp t
      ((hasDerivAt_const t c).sub (hasDerivAt_id t))).deriv

theorem reflected_second {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (c t : ℝ) :
    deriv (deriv (reflected h c)) t = deriv (deriv h) (c - t) := by
  have hfun : deriv (reflected h c) = -reflected (deriv h) c :=
    funext (fun s => reflected_deriv (hh.differentiable (by simp)) c s)
  rw [hfun, deriv_neg, reflected_deriv
    ((contDiff_infty_iff_deriv.mp hh).2.differentiable (by simp)), neg_neg]

def reflectedKernel (n : ℕ) (c : ℝ) : ℝ → ℂ := reflected (complexKernel n) c

theorem reflectedKernel_cinfty (n : ℕ) (c : ℝ) :
    ContDiff ℝ ∞ (reflectedKernel n c) :=
  (complexKernel_cinfty n).comp (contDiff_const.sub contDiff_id)

theorem reflectedKernel_second (n : ℕ) (c t : ℝ) :
    deriv (deriv (reflectedKernel n c)) t =
      deriv (deriv (complexKernel n)) (c - t) :=
  reflected_second (complexKernel_cinfty n) c t

theorem reflectedKernel_tsupport (n : ℕ) (c : ℝ) :
    tsupport (reflectedKernel n c) ⊆
      Icc (c - mollifierRadius n) (c + mollifierRadius n) := by
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  have hk : lineKernel n (c - t) ≠ 0 := by
    intro hk
    exact ht (by simp [reflectedKernel, reflected, complexKernel, hk])
  have hb : c - t ∈ Metric.ball (0 : ℝ) (mollifierRadius n) := by
    exact (lineBump n).support_normed_eq.subset hk
  have habs : |c - t| < mollifierRadius n := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hb
  obtain ⟨hl, hr⟩ := abs_lt.mp habs
  constructor <;> linarith

theorem reflectedKernel_hasCompactSupport (n : ℕ) (c : ℝ) :
    HasCompactSupport (reflectedKernel n c) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (subset_closure.trans (reflectedKernel_tsupport n c))

/-- A genuine member of the old core, with no domain supplier premise. -/
def productTest (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y) :
    SmoothCompactTensor where
  horizontal := reflectedKernel n x
  vertical := reflectedKernel n y
  horizontal_smooth := (reflectedKernel_cinfty n x).of_le (by simp)
  vertical_smooth := (reflectedKernel_cinfty n y).of_le (by simp)
  horizontal_compact := reflectedKernel_hasCompactSupport n x
  vertical_compact := reflectedKernel_hasCompactSupport n y
  vertical_positive := by
    intro t ht
    have hl := (reflectedKernel_tsupport n y ht).1
    change 0 < t
    linarith
  horizontal_cinfty := reflectedKernel_cinfty n x
  vertical_cinfty := reflectedKernel_cinfty n y

def productSeed (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y) : SmoothSeed :=
  ⟨1, fun _ => productTest n x y hy⟩

def productRectangle (n : ℕ) (x y : ℝ) : Set UpperHalfPlane :=
  {z | z.re ∈ Icc (x - mollifierRadius n) (x + mollifierRadius n) ∧
    z.im ∈ Icc (y - mollifierRadius n) (y + mollifierRadius n)}

theorem productSeed_support_rectangle (n : ℕ) (x y : ℝ)
    (hy : mollifierRadius n < y) :
    finiteCompactTensorSupportK Finset.univ (seedTensors (productSeed n x y hy)) ⊆
      productRectangle n x y := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  change z.re ∈ tsupport (reflectedKernel n x) ∧
    z.im ∈ tsupport (reflectedKernel n y) at hi
  exact ⟨reflectedKernel_tsupport n x hi.1, reflectedKernel_tsupport n y hi.2⟩

theorem productSeed_input (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (z : UpperHalfPlane) :
    finiteCoreFunction Finset.univ (seedTensors (productSeed n x y hy)) z =
      reflectedKernel n x z.re * reflectedKernel n y z.im := by
  simp [finiteCoreFunction, seedTensors, productSeed, productTest, tensorFunctionH_eq]

theorem productSeed_output (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (z : UpperHalfPlane) :
    finiteCoreLaplacian Finset.univ (seedTensors (productSeed n x y hy)) z =
      -((z.im : ℂ)^2 *
        (deriv (deriv (complexKernel n)) (x - z.re) * reflectedKernel n y z.im +
          reflectedKernel n x z.re * deriv (deriv (complexKernel n)) (y - z.im))) := by
  simp [finiteCoreLaplacian, seedTensors, productSeed, productTest,
    tensorHyperbolicLaplacianH_eq, reflectedKernel_second]

def massKernel (n : ℕ) (x y : ℝ) (z : UpperHalfPlane) : ℂ :=
  star (reflectedKernel n x z.re * reflectedKernel n y z.im)

def secondKernel (n : ℕ) (x y : ℝ) (z : UpperHalfPlane) : ℂ :=
  star (deriv (deriv (complexKernel n)) (x - z.re) * reflectedKernel n y z.im +
    reflectedKernel n x z.re * deriv (deriv (complexKernel n)) (y - z.im))

theorem massKernel_real (n : ℕ) (x y : ℝ) (z : UpperHalfPlane) :
    massKernel n x y z =
      ((lineKernel n (x - z.re) * lineKernel n (y - z.im) : ℝ) : ℂ) := by
  simp [massKernel, reflectedKernel, reflected, complexKernel]

theorem productSeed_native_integrand (n : ℕ) (x y : ℝ)
    (hy : mollifierRadius n < y) (z : UpperHalfPlane) (w : ℂ) :
    star (finiteCoreLaplacian Finset.univ (seedTensors (productSeed n x y hy)) z +
      finiteCoreFunction Finset.univ (seedTensors (productSeed n x y hy)) z) * w =
      -((z.im : ℂ)^2 * secondKernel n x y z * w) + massKernel n x y z * w := by
  rw [productSeed_output, productSeed_input]
  simp only [secondKernel, massKernel, Complex.star_def, map_add, map_neg, map_mul,
    map_pow, Complex.conj_ofReal]
  ring

/-- This proves legality of the actual translated product test from its
closed support rectangle, before invoking the native adjoint equation. -/
theorem actual_defect_product_test (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (hinterior : productRectangle n x y ⊆ reducedCarrier N) :
    (∫ z : UpperHalfPlane,
      -((z.im : ℂ)^2 * secondKernel n x y z * f (orbitProjection N z)) +
        massKernel n x y z * f (orbitProjection N z)) = 0 := by
  have h := actual_negative_one_defect_interior_weak N f hf (productSeed n x y hy)
    ((productSeed_support_rectangle n x y hy).trans hinterior)
  simpa only [productSeed_native_integrand] using h

/-- Local L2 gives every integrability premise needed to split the true
product-kernel equation. No distributional-derivative integrability is assumed. -/
theorem product_kernel_integrable (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y) :
    Integrable (fun z : UpperHalfPlane =>
      (z.im : ℂ)^2 * secondKernel n x y z * f (orbitProjection N z)) ∧
    Integrable (fun z : UpperHalfPlane =>
      massKernel n x y z * f (orbitProjection N z)) := by
  obtain ⟨ho, hi⟩ := finite_tensor_weak_products_integrable N (productSeed n x y hy) f f
  constructor
  · apply ho.neg.congr
    exact Eventually.of_forall fun z => by
      rw [productSeed_output]
      simp only [secondKernel, Complex.star_def, map_neg, map_mul, map_pow,
        Complex.conj_ofReal]
      ring
  · apply hi.congr
    exact Eventually.of_forall fun z => by rw [productSeed_input]; rfl

def productMassRegularization (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (n : ℕ) (x y : ℝ) : ℂ :=
  ∫ z : UpperHalfPlane, massKernel n x y z * f (orbitProjection N z)

def productSecondRegularization (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (n : ℕ) (x y : ℝ) : ℂ :=
  ∫ z : UpperHalfPlane, (z.im : ℂ)^2 * secondKernel n x y z * f (orbitProjection N z)

def productEuclideanMass (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (n : ℕ) (x y : ℝ) : ℂ :=
  ∫ z : UpperHalfPlane, (z.im : ℂ)^2 * massKernel n x y z * f (orbitProjection N z)

/-- Exact second-kernel distribution equation. The right side is the
canonical y^-2 mass convolution, NOT the unweighted mass convolution. -/
theorem actual_defect_second_kernel_equation (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (hinterior : productRectangle n x y ⊆ reducedCarrier N) :
    productSecondRegularization N f n x y = productMassRegularization N f n x y := by
  have h := actual_defect_product_test N f hf n x y hy hinterior
  obtain ⟨h₂, h₀⟩ := product_kernel_integrable N f n x y hy
  rw [integral_add h₂.neg h₀, integral_neg] at h
  have heq : productMassRegularization N f n x y -
      productSecondRegularization N f n x y = 0 := by
    simpa only [productMassRegularization, productSecondRegularization,
      sub_eq_add_neg, add_comm] using h
  exact (sub_eq_zero.mp heq).symm

theorem coefficient_mass_integrable (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (c : UpperHalfPlane → ℝ) (hc : Continuous c) :
    Integrable (fun z : UpperHalfPlane =>
      (c z : ℂ) * massKernel n x y z * f (orbitProjection N z)) := by
  let s := productSeed n x y hy
  let F := finiteCoreFunction Finset.univ (seedTensors s)
  let K := finiteCompactTensorSupportK Finset.univ (seedTensors s)
  have hF : Continuous F :=
    continuous_finiteCoreFunction Finset.univ (seedTensors s)
  have hsupp : Function.support (fun z => (c z : ℂ) * F z) ⊆ K := by
    intro z hz
    apply finiteCoreFunction_support_subset Finset.univ (seedTensors s)
    intro hzero
    exact hz (by simp [hzero])
  have hp := compact_seed_quotient_product_integrable N (fun z => (c z : ℂ) * F z)
    ((Complex.continuous_ofReal.comp hc).mul hF)
    (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s)) hsupp f
  apply hp.congr
  exact Eventually.of_forall fun z => by
    change star ((c z : ℂ) * finiteCoreFunction Finset.univ
      (seedTensors (productSeed n x y hy)) z) * _ = _
    rw [productSeed_input]
    simp only [massKernel, Complex.star_def, map_mul, Complex.conj_ofReal]
    ring

/-- Exact variable-height commutator. Once the second-kernel integral is
identified with the ordinary smoothed second derivative, this is the
residual of the original variable-coefficient hyperbolic operator.
It is NOT asserted to vanish. -/
theorem actual_defect_height_commutator (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y)
    (hinterior : productRectangle n x y ⊆ reducedCarrier N) :
    -((y : ℂ)^2 * productSecondRegularization N f n x y) +
      productEuclideanMass N f n x y =
      ∫ z : UpperHalfPlane, ((z.im : ℂ)^2 - (y : ℂ)^2) *
        massKernel n x y z * f (orbitProjection N z) := by
  have hE : Integrable (fun z : UpperHalfPlane =>
      (z.im : ℂ)^2 * massKernel n x y z * f (orbitProjection N z)) := by
    simpa only [Complex.ofReal_pow] using
      coefficient_mass_integrable N f n x y hy (fun z => z.im^2)
        (UpperHalfPlane.continuous_im.pow 2)
  have hM := (product_kernel_integrable N f n x y hy).2
  rw [actual_defect_second_kernel_equation N f hf n x y hy hinterior]
  calc
    _ = productEuclideanMass N f n x y -
        (y : ℂ)^2 * productMassRegularization N f n x y := by ring
    _ = ∫ z : UpperHalfPlane,
        ((z.im : ℂ)^2 * massKernel n x y z * f (orbitProjection N z) -
          (y : ℂ)^2 * (massKernel n x y z * f (orbitProjection N z))) := by
      rw [integral_sub hE (hM.const_mul _), integral_const_mul]
      rfl
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring

end
end ImbalancedChen.Part3.Gamma0TranslatedProductWeakPDE20261026a
