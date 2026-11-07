import ImbalancedChen.Part3CompactProductKernelSixJet
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
Actual normalized product mollifier: all six literal coordinate derivatives
commute with convolution and converge UNIFORMLY, with one shared radius,
to those of an actual C-infinity compact plane function. Derivatives may
also be transferred to the actual kernel, yielding precisely the six
integrals consumed by the existing finite-product quadrature theorem.
No approximation, Fourier, Gamma-core or density conclusion is assumed.
-/

noncomputable section
namespace ImbalancedChen.Part3.CompactC2ProductMollifier20261026a

open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
open CompactProductKernelSixJet20261025a

abbrev Plane := ℝ × ℝ
abbrev JetVector := JetIndex → ℂ

def ex : Plane := (1, 0)
def ey : Plane := (0, 1)

def directional (v : Plane) (F : Plane → ℂ) : Plane → ℂ := fun p => fderiv ℝ F p v

def directionalIter (v : Plane) : ℕ → (Plane → ℂ) → Plane → ℂ
  | 0, F => F
  | n + 1, F => directional v (directionalIter v n F)

theorem directional_smooth (v : Plane) {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (directional v F) :=
  (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp (hF.fderiv_right (by simp))

theorem directional_compact (v : Plane) {F : Plane → ℂ} (hF : HasCompactSupport F) :
    HasCompactSupport (directional v F) := hF.fderiv_apply ℝ v

theorem directionalIter_smooth (v : Plane) (n : ℕ) {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (directionalIter v n F) := by
  induction n with
  | zero => exact hF
  | succ n ih => exact directional_smooth v ih

theorem directionalIter_compact (v : Plane) (n : ℕ) {F : Plane → ℂ}
    (hF : HasCompactSupport F) : HasCompactSupport (directionalIter v n F) := by
  induction n with
  | zero => exact hF
  | succ n ih => exact directional_compact v ih

private theorem deriv_coordinate_x {F : Plane → ℂ} (hF : Differentiable ℝ F) (x y : ℝ) :
    deriv (fun s => F (s, y)) x = directional ex F (x, y) := by
  exact ((hF (x, y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const y x))).deriv

private theorem deriv_coordinate_y {F : Plane → ℂ} (hF : Differentiable ℝ F) (x y : ℝ) :
    deriv (fun s => F (x, s)) y = directional ey F (x, y) := by
  exact ((hF (x, y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const x y).prodMk (hasDerivAt_id y))).deriv

private theorem iterated_coordinate_x (n : ℕ) {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) :
    (fun p : Plane => iteratedDeriv n (fun x => F (x, p.2)) p.1) = directionalIter ex n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext p
      rw [iteratedDeriv_succ]
      have hfun : (fun x => iteratedDeriv n (fun s => F (s, p.2)) x) =
          fun x => directionalIter ex n F (x, p.2) :=
        funext fun x => congrFun ih (x, p.2)
      rw [hfun]
      exact deriv_coordinate_x ((directionalIter_smooth ex n hF).differentiable (by simp)) _ _

private theorem iterated_coordinate_y (n : ℕ) {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) :
    (fun p : Plane => iteratedDeriv n (fun y => F (p.1, y)) p.2) = directionalIter ey n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext p
      rw [iteratedDeriv_succ]
      have hfun : (fun y => iteratedDeriv n (fun s => F (p.1, s)) y) =
          fun y => directionalIter ey n F (p.1, y) :=
        funext fun y => congrFun ih (p.1, y)
      rw [hfun]
      exact deriv_coordinate_y ((directionalIter_smooth ey n hF).differentiable (by simp)) _ _

def mixedJet (F : Plane → ℂ) (ij : JetIndex) : Plane → ℂ :=
  directionalIter ex ij.1.1.val (directionalIter ey ij.1.2.val F)

theorem mixedJet_smooth {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) (ij : JetIndex) :
    ContDiff ℝ ∞ (mixedJet F ij) :=
  directionalIter_smooth ex _ (directionalIter_smooth ey _ hF)

theorem mixedJet_compact {F : Plane → ℂ} (hF : HasCompactSupport F) (ij : JetIndex) :
    HasCompactSupport (mixedJet F ij) :=
  directionalIter_compact ex _ (directionalIter_compact ey _ hF)

theorem partialJet_eq_mixedJet {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (ij : JetIndex) (p : Plane) : partialJet ij F p = mixedJet F ij p := by
  unfold partialJet mixedJet
  have hin (x : ℝ) := congrFun (iterated_coordinate_y ij.1.2.val hF) (x, p.2)
  simp_rw [hin]
  exact congrFun (iterated_coordinate_x ij.1.1.val
    (directionalIter_smooth ey ij.1.2.val hF)) p

def jetVector (F : Plane → ℂ) (p : Plane) : JetVector := fun ij => mixedJet F ij p

theorem jetVector_continuous {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (jetVector F) := continuous_pi fun ij => (mixedJet_smooth hF ij).continuous

theorem jetVector_uniformContinuous {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : UniformContinuous (jetVector F) :=
  uniformContinuous_pi.mpr fun ij =>
    (mixedJet_compact hc ij).uniformContinuous_of_continuous (mixedJet_smooth hF ij).continuous

/-- Ordinary complex multiplication, with the real differentiability scalar. -/
def convolutionC (f g : Plane → ℂ) : Plane → ℂ := f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g

theorem convolutionC_comm (f g : Plane → ℂ) : convolutionC f g = convolutionC g f := by
  have hL : (ContinuousLinearMap.mul ℝ ℂ).flip = ContinuousLinearMap.mul ℝ ℂ := by
    ext x y
    exact mul_comm x y
  simpa only [convolutionC, hL] using
    (convolution_flip (L := ContinuousLinearMap.mul ℝ ℂ) (f := g) (g := f))

theorem directional_convolutionC (v : Plane) {f g : Plane → ℂ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    directional v (convolutionC f g) = convolutionC f (directional v g) := by
  funext p
  have hd := hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    hf (hg.of_le (by simp)) p
  change fderiv ℝ (convolutionC f g) p v = convolutionC f (directional v g) p
  rw [hd.fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ) hf
    (hgc.fderiv ℝ) (hg.continuous_fderiv (by simp)) p v

theorem directionalIter_convolutionC (v : Plane) (n : ℕ) {f g : Plane → ℂ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    directionalIter v n (convolutionC f g) = convolutionC f (directionalIter v n g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change directional v (directionalIter v n (convolutionC f g)) = _
      rw [ih]
      exact directional_convolutionC v hf (directionalIter_smooth v n hg)
        (directionalIter_compact v n hgc)

theorem mixedJet_convolutionC {f g : Plane → ℂ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (ij : JetIndex) : mixedJet (convolutionC f g) ij = convolutionC f (mixedJet g ij) := by
  unfold mixedJet
  rw [directionalIter_convolutionC ey _ hf hg hgc]
  exact directionalIter_convolutionC ex _ hf
    (directionalIter_smooth ey _ hg) (directionalIter_compact ey _ hgc)

def realProductKernel (r : ℝ) (hr : 0 < r) (p : Plane) : ℝ :=
  (radiusBump r hr).normed volume p.1 * (radiusBump r hr).normed volume p.2

def complexProductKernel (r : ℝ) (hr : 0 < r) (p : Plane) : ℂ :=
  (normalizedProductKernel r hr).horizontal p.1 * (normalizedProductKernel r hr).vertical p.2

theorem complexProductKernel_eq (r : ℝ) (hr : 0 < r) (p : Plane) :
    complexProductKernel r hr p = (realProductKernel r hr p : ℂ) := by
  simp only [complexProductKernel, normalizedProductKernel, realProductKernel, Complex.ofReal_mul]

theorem realProductKernel_continuous (r : ℝ) (hr : 0 < r) :
    Continuous (realProductKernel r hr) :=
  ((radiusBump r hr).continuous_normed.comp continuous_fst).mul
    ((radiusBump r hr).continuous_normed.comp continuous_snd)

theorem complexProductKernel_smooth (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (complexProductKernel r hr) :=
  ((normalizedProductKernel r hr).horizontal_smooth.comp contDiff_fst).mul
    ((normalizedProductKernel r hr).vertical_smooth.comp contDiff_snd)

theorem realProductKernel_nonneg (r : ℝ) (hr : 0 < r) (p : Plane) :
    0 ≤ realProductKernel r hr p :=
  mul_nonneg ((radiusBump r hr).nonneg_normed _) ((radiusBump r hr).nonneg_normed _)

theorem realProductKernel_integral (r : ℝ) (hr : 0 < r) :
    ∫ p, realProductKernel r hr p = 1 := by
  simpa only [realProductKernel, (radiusBump r hr).integral_normed, one_mul] using
    (integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      ((radiusBump r hr).normed volume) ((radiusBump r hr).normed volume))

theorem realProductKernel_support (r : ℝ) (hr : 0 < r) :
    Function.support (realProductKernel r hr) ⊆ Metric.ball (0 : Plane) r := by
  intro p hp
  have hh : (radiusBump r hr).normed volume p.1 ≠ 0 := fun h => hp (by simp [realProductKernel, h])
  have hv : (radiusBump r hr).normed volume p.2 ≠ 0 := fun h => hp (by simp [realProductKernel, h])
  have hx : p.1 ∈ Function.support ((radiusBump r hr).normed volume) := hh
  have hy : p.2 ∈ Function.support ((radiusBump r hr).normed volume) := hv
  rw [(radiusBump r hr).support_normed_eq] at hx hy
  change p.1 ∈ Metric.ball (0 : ℝ) r at hx
  change p.2 ∈ Metric.ball (0 : ℝ) r at hy
  simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff] using And.intro hx hy

theorem realProductKernel_compact (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (realProductKernel r hr) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) r)
    ((realProductKernel_support r hr).trans Metric.ball_subset_closedBall)

theorem complexProductKernel_compact (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (complexProductKernel r hr) := by
  have h := (realProductKernel_compact r hr).comp_left (show Complex.ofReal 0 = 0 by rfl)
  have heq : complexProductKernel r hr = fun p => (realProductKernel r hr p : ℂ) :=
    funext (complexProductKernel_eq r hr)
  rw [heq]
  exact h

/-- This actual smoothing uses normalized positive product bumps. -/
def productSmoothing (r : ℝ) (hr : 0 < r) (F : Plane → ℂ) : Plane → ℂ :=
  convolutionC (complexProductKernel r hr) F

theorem productSmoothing_smooth (r : ℝ) (hr : 0 < r) {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (productSmoothing r hr F) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (complexProductKernel_smooth r hr).continuous.locallyIntegrable hF

/-- All six derivatives are transferred to the ORIGINAL function. -/
theorem productSmoothing_partialJet (r : ℝ) (hr : 0 < r) {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (ij : JetIndex) (p : Plane) :
    partialJet ij (productSmoothing r hr F) p =
      convolutionC (complexProductKernel r hr) (mixedJet F ij) p := by
  rw [partialJet_eq_mixedJet (productSmoothing_smooth r hr hF hc)]
  exact congrFun (mixedJet_convolutionC
    (complexProductKernel_smooth r hr).continuous.locallyIntegrable hF hc ij) p

/-- The SAME derivatives may be moved to the actual kernel, giving the
literal scalar integrals used by the frozen six-jet quadrature source. -/
theorem productSmoothing_partialJet_integral (r : ℝ) (hr : 0 < r) {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (ij : JetIndex) (p : Plane) :
    partialJet ij (productSmoothing r hr F) p =
      ∫ t, F t *
        iteratedDeriv ij.1.1.val (normalizedProductKernel r hr).horizontal (p.1 - t.1) *
          iteratedDeriv ij.1.2.val (normalizedProductKernel r hr).vertical (p.2 - t.2) := by
  rw [partialJet_eq_mixedJet (productSmoothing_smooth r hr hF hc)]
  change mixedJet (convolutionC (complexProductKernel r hr) F) ij p = _
  rw [convolutionC_comm]
  rw [mixedJet_convolutionC hF.continuous.locallyIntegrable
    (complexProductKernel_smooth r hr) (complexProductKernel_compact r hr)]
  unfold convolutionC
  simp_rw [convolution_def, ContinuousLinearMap.mul_apply',
    ← partialJet_eq_mixedJet (complexProductKernel_smooth r hr),
    complexProductKernel, partialJet_product]
  simp only [mul_assoc]

/-- Restricting the convolution integral uses the ACTUAL support of F. -/
theorem productSmoothing_partialJet_boxIntegral (r : ℝ) (hr : 0 < r)
    {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (A a b : ℝ) (hs : tsupport F ⊆ planeBox A a b) (ij : JetIndex) (p : Plane) :
    partialJet ij (productSmoothing r hr F) p =
      ∫ t in planeBox A a b, F t *
        iteratedDeriv ij.1.1.val (normalizedProductKernel r hr).horizontal (p.1 - t.1) *
          iteratedDeriv ij.1.2.val (normalizedProductKernel r hr).vertical (p.2 - t.2) := by
  rw [productSmoothing_partialJet_integral r hr hF hc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have hFt : F t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hs h))
  simp only [hFt, zero_mul]

/-- A genuine shared-radius, GLOBAL uniform C2 estimate. Compactness and
smoothness produce uniform continuity of the actual six-jet vector. -/
theorem exists_shared_radius_uniform_sixJet {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ δ → ∀ p : Plane, ∀ ij : JetIndex,
      ‖partialJet ij (productSmoothing r hr F) p - partialJet ij F p‖ < ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (jetVector_uniformContinuous hF hc) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrd p ij
  let G := jetVector F
  have hGc : Continuous G := jetVector_continuous hF
  have hdist : dist ((realProductKernel r hr ⋆[lsmul ℝ ℝ, volume] G) p) (G p) ≤ ε / 2 := by
    apply dist_convolution_le (half_pos hε).le (realProductKernel_support r hr)
      (realProductKernel_nonneg r hr) (realProductKernel_integral r hr) hGc.aestronglyMeasurable
    intro q hq
    exact (hmod ((Metric.mem_ball.mp hq).trans_le hrd)).le
  have hint := (realProductKernel_compact r hr).convolutionExists_left (lsmul ℝ ℝ)
    (realProductKernel_continuous r hr) hGc.locallyIntegrable p
  let L : JetVector →L[ℝ] ℂ := ContinuousLinearMap.proj ij
  have heval : ((realProductKernel r hr ⋆[lsmul ℝ ℝ, volume] G) p) ij =
      convolutionC (complexProductKernel r hr) (mixedJet F ij) p := by
    have h := L.integral_comp_comm hint
    simpa only [L, convolutionC, convolution_def, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.lsmul_apply, Pi.smul_apply, ContinuousLinearMap.mul_apply',
      complexProductKernel_eq, Complex.real_smul, G, jetVector] using h.symm
  have hcoord := (norm_le_pi_norm
    (((realProductKernel r hr ⋆[lsmul ℝ ℝ, volume] G) p) - G p) ij).trans
      (show ‖((realProductKernel r hr ⋆[lsmul ℝ ℝ, volume] G) p) - G p‖ ≤ ε / 2 from
        by simpa only [dist_eq_norm] using hdist)
  rw [Pi.sub_apply, heval, ← productSmoothing_partialJet r hr hF hc,
    ← partialJet_eq_mixedJet hF] at hcoord
  exact hcoord.trans_lt (half_lt_self hε)

end ImbalancedChen.Part3.CompactC2ProductMollifier20261026a