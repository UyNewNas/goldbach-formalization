import ImbalancedChen.Part3PlanarLocalWeakGradientExtraction
import ImbalancedChen.Part3Gamma0InteriorSmoothedCaccioppoli

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual Gamma adjoint defect local H1 on each fixed legal interior cutoff
region. Strong convergence is derived from the pinned native L2 product
average and its scalar AE bridge. The uniform derivative bound is obtained
from the actual minimalShiftDefect equation through the supplied genuine
Caccioppoli theorem. No weak-limit, H1, smooth-equation, or energy-bound
hypothesis occurs in the actual endpoint. Remaining inputs are explicitly
the compact localization and the geometric legality of shrinking kernels.
This is local regularity; it does not assert the global spectral theorem.
-/

namespace ImbalancedChen.Part3.Gamma0ActualDefectLocalH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0SmoothedCoordinateWeakPDE20261026a Gamma0SmoothedPotentialL2Budget20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0CompactDefectMollifier20261026a Gamma0TranslatedProductWeakPDE20261026a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open NestedRectangleRealCutoff20261026b Gamma0InteriorSmoothedCaccioppoli20261026b
open PlanarLocalWeakGradientExtraction20261026b

/-- Strong ordinary-coordinate L2 convergence for the literal actual
product smoothing, using the already proved scalar/Bochner identification. -/
theorem actualProductSmooth_strong_L2 (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N) :
    Tendsto (fun n => (actualProductSmooth_memLp N hK hB hbound f n).toLp
      (actualProductSmooth N K B f n)) atTop
      (𝓝 ((localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f))) := by
  have hg := localizedPlane_memLp N hK hB f
  have hgc := localizedPlane_hasCompactSupport N hK hbound f
  have h := ProductKernelL2TranslationAverage20261026a.productAverage_tendsto
    (hg.toLp (localizedPlane N K B f))
  have heq (n : ℕ) :
      ProductKernelL2TranslationAverage20261026a.productAverage
        (ProductKernelL2TranslationAverage20261026a.radius n)
        (ProductKernelL2TranslationAverage20261026a.radius_pos n)
        (hg.toLp (localizedPlane N K B f)) =
      (actualProductSmooth_memLp N hK hB hbound f n).toLp
        (actualProductSmooth N K B f n) := by
    rw [CompactProductBochnerAEJoin20261026a.productAverage_eq_scalar_toLp hg hgc]
    apply Lp.ext
    filter_upwards [
      (CompactProductBochnerAEJoin20261026a.smoothing_memLp hg hgc
        (ProductKernelL2TranslationAverage20261026a.radius n)
        (ProductKernelL2TranslationAverage20261026a.radius_pos n)).coeFn_toLp,
      (actualProductSmooth_memLp N hK hB hbound f n).coeFn_toLp] with p hp hq
    rw [hp, hq]
    exact congrFun (productSmooth_eq_nativeSmoothing n (localizedPlane N K B f)).symm p
  simpa only [heq] using h

/-- The actual deficiency vector has a local L2 weak gradient wherever
the fixed smooth cutoff is one. Shrinking-kernel legality is needed only
on a tail; the cutoff and localization are fixed before that tail. -/
theorem actual_defect_local_H1 (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N)
    {θ : Plane → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hrange : ∀ p, 0 ≤ θ p ∧ θ p ≤ 1)
    (Ω : Set Plane) (hone : ∀ p ∈ Ω, θ p = 1)
    (n₀ : ℕ)
    (hheight : ∀ n p, p ∈ tsupport θ → mollifierRadius (n + n₀) < p.2)
    (hlocal : ∀ n p, p ∈ tsupport θ → productRectangle (n + n₀) p.1 p.2 ⊆ K)
    (hcarrier : ∀ n p, p ∈ tsupport θ →
      productRectangle (n + n₀) p.1 p.2 ⊆ reducedCarrier N) :
    HasLocalL2GradientOn Ω (localizedPlane N K B f) := by
  obtain ⟨D, hD0, hD⟩ := exists_cutoff_gradient_budget hθ hc
  let C : ℝ := ((4*D+1) + ((a⁻¹)^2)^2) *
    ‖(localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let U (n : ℕ) := actualProductSmooth N K B f (n + n₀)
  have hU (n : ℕ) : ContDiff ℝ ∞ (U n) := actualProductSmooth_cinfty N hK hB f _
  have hU2 (n : ℕ) : MemLp (U n) 2 volume := actualProductSmooth_memLp N hK hB hbound f _
  have hadd : StrictMono (fun n : ℕ => n + n₀) := fun i j hij => Nat.add_lt_add_right hij n₀
  have hv : Tendsto (fun n => (hU2 n).toLp (U n)) atTop
      (𝓝 ((localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f))) :=
    (actualProductSmooth_strong_L2 N hK hB hbound f).comp hadd.tendsto_atTop
  have he (n : ℕ) :
      ‖weightedGradientL2 hθ hc (hU n) xDirection‖^2 +
        ‖weightedGradientL2 hθ hc (hU n) yDirection‖^2 ≤ C := by
    have h := actual_defect_uniform_interior_energy N hK hB ha hbound hlower f hf
      hθ hc hrange hD0 hD (n + n₀) (hheight n) (hlocal n) (hcarrier n)
    rw [weightedEnergy_eq_L2 hθ hc (hU n)] at h
    exact h
  exact local_gradient_of_smooth_L2_approximation (localizedPlane N K B f)
    (localizedPlane_memLp N hK hB f) U hU hU2 hv hθ hc C hC he Ω hone

/-- Concrete closed interior rectangle instance, with its genuine
explicit separated cutoff; no cutoff, gradient bound or weak limit is
assumed. The three tail premises state only actual kernel geometry. -/
theorem actual_defect_rectangle_local_H1 (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N)
    (L R c d δ : ℝ) (hLR : L ≤ R) (hcd : c ≤ d) (hδ : 0 < δ)
    (n₀ : ℕ)
    (hheight : ∀ n p, p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ) →
      mollifierRadius (n + n₀) < p.2)
    (hlocal : ∀ n p, p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ) →
      productRectangle (n + n₀) p.1 p.2 ⊆ K)
    (hcarrier : ∀ n p, p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ) →
      productRectangle (n + n₀) p.1 p.2 ⊆ reducedCarrier N) :
    HasLocalL2GradientOn (Icc L R ×ˢ Icc c d) (localizedPlane N K B f) :=
  actual_defect_local_H1 N hK hB ha hbound hlower f hf
    (rectangleCutoff_smooth L R c d δ hLR hcd hδ)
    (rectangleCutoff_compact L R c d δ hLR hcd hδ)
    (rectangleCutoff_range L R c d δ hLR hcd hδ) _
    (fun _ hp => rectangleCutoff_one L R c d δ hLR hcd hδ hp)
    n₀ hheight hlocal hcarrier

end
end ImbalancedChen.Part3.Gamma0ActualDefectLocalH120261026b
