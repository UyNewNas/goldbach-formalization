import ImbalancedChen.Part3ActualPullbackLocalH1Transfer

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The analytic local-regularity consequence of the literal whole-H seed
adjoint identity. All localization, cutoff and shrinking-kernel geometry
is constructed, including the mollifier tail. The sole analytic primitive
is the displayed raw adjoint test integral, not H1, a gradient, a smooth
PDE, or an energy estimate. Its actual minimalShiftDefect supplier remains
a separate obligation until the whole-H unfolding supplier is installed.
-/

namespace ImbalancedChen.Part3.WholeSeedTestsRectangleLocalH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0SmoothedCoordinateWeakPDE20261026a Gamma0SmoothedPotentialL2Budget20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0CompactDefectMollifier20261026a
open Gamma0TranslatedProductWeakPDE20261026a Gamma0QuotientCellPushforward20261025a
open Gamma0SmoothCompactTensorCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open MaassWeakOperatorCore20261024zz Gamma0CarrierAESection20261025a
open NestedRectangleRealCutoff20261026b Gamma0InteriorSmoothedCaccioppoli20261026b
open PlanarLocalWeakGradientExtraction20261026b Gamma0ActualDefectLocalH120261026b
open UpperRectangleMollifierGeometry20261026b ActualPullbackLocalH1Transfer20261026b

/-- Raw whole-upper-half-plane adjoint testing, with its actual shifted
operator and actual orbit pullback, without a carrier-support condition. -/
def WholeSeedAdjointTests (N : ℕ) [NeZero N] (f : QuotientL2 N) : Prop :=
  ∀ s : SmoothSeed,
    (∫ z : UpperHalfPlane,
      star (finiteCoreLaplacian Finset.univ (seedTensors s) z +
        finiteCoreFunction Finset.univ (seedTensors s) z) * f (orbitProjection N z)) = 0

theorem smoothed_equation_of_whole_seed_tests (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hraw : WholeSeedAdjointTests N f)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (n : ℕ) (x y : ℝ)
    (hy : mollifierRadius n < y) (hrect : productRectangle n x y ⊆ K) :
    euclideanLaplacian (actualProductSmooth N K B f n) (x, y) =
      potentialSmooth N K B a f n (x, y) := by
  have hw := hraw (productSeed n x y hy)
  simp only [productSeed_native_integrand] at hw
  obtain ⟨h₂, h₀⟩ := product_kernel_integrable N f n x y hy
  rw [integral_add h₂.neg h₀, integral_neg] at hw
  have hkernel : productSecondRegularization N f n x y =
      productMassRegularization N f n x y := by
    have he : productMassRegularization N f n x y -
        productSecondRegularization N f n x y = 0 := by
      simpa only [productMassRegularization, productSecondRegularization,
        sub_eq_add_neg, add_comm] using hw
    exact (sub_eq_zero.mp he).symm
  rw [actualProductSmooth_laplacian N hK hB hbound f n x y hy hrect, hkernel]
  exact (potentialSmooth_eq_nativeMass N ha hbound hlower f n x y hy hrect).symm

/-- Every positive rectangle has a genuine local L2 gradient for the
original automorphic pullback. There is no caller cutoff, localization,
tail, weak-limit, H1, smoothed-PDE or energy-bound hypothesis. -/
theorem rectangle_localH1_of_whole_seed_tests (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hraw : WholeSeedAdjointTests N f)
    (L R c d : ℝ) (hLR : L ≤ R) (hcd : c ≤ d) (hcpos : 0 < c) :
    HasCoordinateLocalH1On (Icc L R ×ˢ Icc c d) (actualPlanePullback N f) := by
  let δ : ℝ := c / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hmargin : 2 * δ < c := by dsimp [δ]; linarith
  let K := upperRectangle (L - 2*δ) (R + 2*δ) (c - 2*δ) (d + 2*δ)
  let a : ℝ := c - 2*δ
  let B : ℝ := d + 2*δ
  have ha : 0 < a := by dsimp [a]; linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hK : IsCompact K := upperRectangle_isCompact _ _ _ _ ha
  have hbound : ∀ z ∈ K, z.im ≤ B := fun z hz => hz.2.2
  have hlower : ∀ z ∈ K, a ≤ z.im := fun z hz => hz.2.1
  let θ := rectangleCutoff L R c d δ hLR hcd hδ
  have hθ : ContDiff ℝ ∞ θ := rectangleCutoff_smooth L R c d δ hLR hcd hδ
  have hθc : HasCompactSupport θ := rectangleCutoff_compact L R c d δ hLR hcd hδ
  have hθrange : ∀ p, 0 ≤ θ p ∧ θ p ≤ 1 :=
    rectangleCutoff_range L R c d δ hLR hcd hδ
  obtain ⟨n₀, htail⟩ := exists_rectangle_mollifier_tail L R c d δ hLR hcd hδ hmargin
  obtain ⟨D, hD0, hD⟩ := exists_cutoff_gradient_budget hθ hθc
  let F := localizedPlane N K B f
  have hF : MemLp F 2 volume := localizedPlane_memLp N hK hB f
  let U (n : ℕ) := actualProductSmooth N K B f (n + n₀)
  have hU (n : ℕ) : ContDiff ℝ ∞ (U n) := actualProductSmooth_cinfty N hK hB f _
  have hU2 (n : ℕ) : MemLp (U n) 2 volume := actualProductSmooth_memLp N hK hB hbound f _
  have hadd : StrictMono (fun n : ℕ => n + n₀) := fun i j hij => Nat.add_lt_add_right hij n₀
  have hv : Tendsto (fun n => (hU2 n).toLp (U n)) atTop (𝓝 (hF.toLp F)) :=
    (actualProductSmooth_strong_L2 N hK hB hbound f).comp hadd.tendsto_atTop
  let C : ℝ := (4*D+1) * ‖hF.toLp F‖^2 + (((a⁻¹)^2) * ‖hF.toLp F‖)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have henergy (n : ℕ) :
      ‖weightedGradientL2 hθ hθc (hU n) xDirection‖^2 +
        ‖weightedGradientL2 hθ hθc (hU n) yDirection‖^2 ≤ C := by
    let V := potentialSmooth N K B a f (n + n₀)
    have hV : ContDiff ℝ ∞ V := productSmooth_cinfty
      ((localizedPotential_memLp N hK hB ha f).locallyIntegrable (by norm_num)) _
    have hV2 : MemLp V 2 volume := potentialSmooth_memLp N hK hB ha hbound f _
    have hPDE : ∀ p ∈ tsupport θ, euclideanLaplacian (U n) p = V p := by
      intro p hp
      exact smoothed_equation_of_whole_seed_tests N f hraw hK hB ha hbound hlower
        (n + n₀) p.1 p.2 ((htail n).1 p hp) ((htail n).2 p hp)
    have he := smooth_interior_L2_budget hθ hθc hθrange hD (hU n) hV.continuous
      (hU2 n) hV2 hPDE
    have hu := mul_self_le_mul_self (norm_nonneg _)
      (actualProductSmooth_uniform_L2_bound N hK hB hbound f (n + n₀))
    have hv' := mul_self_le_mul_self (norm_nonneg _)
      (potentialSmooth_uniform_L2_bound N hK hB ha hbound f (n + n₀))
    simp only [← pow_two] at hu hv'
    have hcoef : 0 ≤ 4*D+1 := by linarith
    rw [weightedEnergy_eq_L2 hθ hθc (hU n)] at he
    exact he.trans (add_le_add (mul_le_mul_of_nonneg_left hu hcoef) hv')
  have hlocal : HasLocalL2GradientOn (Icc L R ×ˢ Icc c d) F :=
    local_gradient_of_smooth_L2_approximation F hF U hU hU2 hv hθ hθc C hC henergy _
      (fun p hp => rectangleCutoff_one L R c d δ hLR hcd hδ hp)
  have hinner : upperRectangle L R c d ⊆ K := by
    intro z hz
    change (L - 2*δ ≤ z.re ∧ z.re ≤ R + 2*δ) ∧
      (c - 2*δ ≤ z.im ∧ z.im ≤ d + 2*δ)
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  exact localH1_of_local_extension (measurableSet_Icc.prod measurableSet_Icc) hlocal
    (localizedPlane_eq_actual_on_rectangle N hcpos hbound f hinner)

end
end ImbalancedChen.Part3.WholeSeedTestsRectangleLocalH120261026b
