import ImbalancedChen.Part3CompactC2ProductMollifier
import Mathlib.MeasureTheory.Function.L2Space

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The distributional first derivative of a genuine L2 function is defined
by integration against every smooth compact scalar test. Testing with
the actual reflected kernel proves that the classical derivative of
the mollification is the mollification of the weak derivative. Both
coordinate identities use the SAME actual normalized product kernel.
All weak-test products are independently integrable from L2 and compact
support. No weak-PDE smoothing, H1 regularity of an adjoint vector, L2
approximate-identity convergence, or finite-tensor density is assumed or
claimed. Those last two density steps remain separate obligations.
-/

namespace ImbalancedChen.Part3.WeakH1ProductMollifierDerivative20261026a
noncomputable section
open Set MeasureTheory ContinuousLinearMap
open scoped Topology Convolution
open CompactC2ProductMollifier20261026a

/-- Bilinear distributional convention. Complex conjugation of all test
functions gives the equivalent usual sesquilinear convention. -/
def HasWeakDirectionalDerivative (f g : Plane → ℂ) (v : Plane) : Prop :=
  ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ t, directional v ψ t * f t) = -(∫ t, ψ t * g t)

theorem weak_test_products_integrable {f g : Plane → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (v : Plane) {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun t => directional v ψ t * f t) volume ∧
      Integrable (fun t => ψ t * g t) volume := by
  constructor
  · simpa only [smul_eq_mul] using
      (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        (directional_smooth v hψ).continuous (directional_compact v hc)
  · simpa only [smul_eq_mul] using
      (hg.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        hψ.continuous hc

def reflected (k : Plane → ℂ) (p : Plane) : Plane → ℂ := fun t => k (p - t)

theorem reflected_smooth {k : Plane → ℂ} (hk : ContDiff ℝ ∞ k) (p : Plane) :
    ContDiff ℝ ∞ (reflected k p) := hk.comp (contDiff_const.sub contDiff_id)

theorem reflected_compact {k : Plane → ℂ} (hk : HasCompactSupport k) (p : Plane) :
    HasCompactSupport (reflected k p) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hk.image (continuous_const.sub continuous_id))
  intro t ht
  refine ⟨p - t, subset_closure ht, ?_⟩
  simp

theorem directional_reflected {k : Plane → ℂ} (hk : ContDiff ℝ ∞ k)
    (v p t : Plane) :
    directional v (reflected k p) t = -directional v k (p - t) := by
  have hd := ((hk.differentiable (by simp)) (p - t)).hasFDerivAt.comp t
    ((hasFDerivAt_const p t).sub (hasFDerivAt_id t))
  change fderiv ℝ (fun q => k (p - q)) t v = -fderiv ℝ k (p - t) v
  rw [hd.fderiv]
  simp

/-- A genuine weak derivative transfers through convolution with any
smooth compact kernel. The proof uses a reflected compact test, not a
formal exchange of distributional and classical differentiation. -/
theorem directional_convolution_of_weakDerivative {f g k : Plane → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (v : Plane) (hweak : HasWeakDirectionalDerivative f g v)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    directional v (convolutionC k f) = convolutionC k g := by
  funext p
  have hψ := reflected_smooth hk p
  have hψc := reflected_compact hkc p
  have hint := weak_test_products_integrable hf hg v hψ hψc
  have hw := hweak (reflected k p) hψ hψc
  simp_rw [directional_reflected hk v p] at hw
  simp only [neg_mul, integral_neg, reflected] at hw
  have heq : (∫ t, directional v k (p - t) * f t) =
      ∫ t, k (p - t) * g t := neg_inj.mp hw
  calc
    directional v (convolutionC k f) p = convolutionC f (directional v k) p := by
      rw [convolutionC_comm k f]
      exact congrFun (directional_convolutionC v
        (hf.locallyIntegrable (by norm_num)) hk hkc) p
    _ = ∫ t, directional v k (p - t) * f t := by
      simp only [convolutionC, convolution_def, ContinuousLinearMap.mul_apply', mul_comm]
    _ = ∫ t, k (p - t) * g t := heq
    _ = convolutionC k g p := by
      rw [convolutionC_comm k g]
      simp only [convolutionC, convolution_def, ContinuousLinearMap.mul_apply', mul_comm]

/-- Honest compact H1 data. Neither weak-gradient existence nor test
approximation is hidden in an opaque target predicate. -/
structure CompactH1Jet where
  value : Plane → ℂ
  dx : Plane → ℂ
  dy : Plane → ℂ
  value_memLp : MemLp value 2 volume
  dx_memLp : MemLp dx 2 volume
  dy_memLp : MemLp dy 2 volume
  value_compact : HasCompactSupport value
  weak_dx : HasWeakDirectionalDerivative value dx ex
  weak_dy : HasWeakDirectionalDerivative value dy ey

/-- True smoothing of an H1 function, without requiring it to have a
classical derivative before convolution. -/
theorem compactH1_productSmoothing_smooth (J : CompactH1Jet)
    (r : ℝ) (hr : 0 < r) : ContDiff ℝ ∞ (productSmoothing r hr J.value) :=
  (complexProductKernel_compact r hr).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ) (complexProductKernel_smooth r hr)
    (J.value_memLp.locallyIntegrable (by norm_num))

/-- Both weak coordinate derivatives commute with the literal actual
normalized product mollifier. No derivative-exchange input is needed. -/
theorem compactH1_productSmoothing_gradient (J : CompactH1Jet)
    (r : ℝ) (hr : 0 < r) :
    directional ex (productSmoothing r hr J.value) = productSmoothing r hr J.dx ∧
    directional ey (productSmoothing r hr J.value) = productSmoothing r hr J.dy := by
  constructor
  · exact directional_convolution_of_weakDerivative J.value_memLp J.dx_memLp
      ex J.weak_dx (complexProductKernel_smooth r hr) (complexProductKernel_compact r hr)
  · exact directional_convolution_of_weakDerivative J.value_memLp J.dy_memLp
      ey J.weak_dy (complexProductKernel_smooth r hr) (complexProductKernel_compact r hr)

end
end ImbalancedChen.Part3.WeakH1ProductMollifierDerivative20261026a
