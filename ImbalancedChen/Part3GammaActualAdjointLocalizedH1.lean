import ImbalancedChen.Part3GammaActualAdjointFormRegularity
import ImbalancedChen.Part3GammaFiniteSeedAdjointGraphTests
import ImbalancedChen.Part3WholeUpperChartWeakH1Patching

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Local H1 for an arbitrary native adjoint graph pair (f,w). The true
regularized equation is Delta(S_f)=-V_w. Existing smooth Caccioppoli,
mass/potential contractions and strong approximation supply the gradient
bound and extraction. This is not restricted to the eigenvalue -1 and
does not replace arbitrary output w by f. No new Caccioppoli is proved.
-/

namespace ImbalancedChen.Part3.GammaActualAdjointLocalizedH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open GammaFiniteSeedAdjointGraphTests20261026b Gamma0SmoothCompactTensorCore20261025a
open MaassWeakOperatorCore20261024zz Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0TranslatedProductWeakPDE20261026a Gamma0CompactDefectMollifier20261026a
open Gamma0SmoothedCoordinateWeakPDE20261026a Gamma0SmoothedPotentialL2Budget20261026a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open NestedRectangleRealCutoff20261026b Gamma0InteriorSmoothedCaccioppoli20261026b
open PlanarLocalWeakGradientExtraction20261026b Gamma0ActualDefectLocalH120261026b

theorem actual_adjoint_second_kernel_equation (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    (n : ℕ) (x y : ℝ) (hy : mollifierRadius n < y) :
    productSecondRegularization N f n x y = -productMassRegularization N w n x y := by
  have hw := actual_adjoint_finite_seed_tests N hfw (productSeed n x y hy)
  have hlap : (∫ z : UpperHalfPlane,
      star (finiteCoreLaplacian Finset.univ (seedTensors (productSeed n x y hy)) z) *
        f (orbitProjection N z)) = -productSecondRegularization N f n x y := by
    calc
      _ = ∫ z : UpperHalfPlane,
          -((z.im : ℂ)^2 * secondKernel n x y z * f (orbitProjection N z)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          rw [productSeed_output]
          simp only [secondKernel, star_neg, star_mul, star_pow, Complex.star_def,
            Complex.conj_ofReal]
          ring
      _ = _ := integral_neg _
  have hmass : (∫ z : UpperHalfPlane,
      star (finiteCoreFunction Finset.univ (seedTensors (productSeed n x y hy)) z) *
        w (orbitProjection N z)) = productMassRegularization N w n x y := by
    simp only [productSeed_input, productMassRegularization, massKernel]
  rw [hlap, hmass] at hw
  simpa only [neg_neg] using congrArg Neg.neg hw

theorem actual_adjoint_smoothed_equation (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (n : ℕ) (x y : ℝ)
    (hy : mollifierRadius n < y) (hrect : productRectangle n x y ⊆ K) :
    euclideanLaplacian (actualProductSmooth N K B f n) (x,y) =
      -potentialSmooth N K B a w n (x,y) := by
  rw [actualProductSmooth_laplacian N hK hB hbound f n x y hy hrect,
    actual_adjoint_second_kernel_equation N hfw n x y hy,
    potentialSmooth_eq_nativeMass N ha hbound hlower w n x y hy hrect]

/-- Arbitrary actual adjoint input has a local weak L2 gradient on the
cutoff-one region. No form, weak-PDE, H1 or gradient premise is supplied. -/
theorem actual_adjoint_localized_H1 (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im)
    {θ : Plane → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hrange : ∀ p, 0 ≤ θ p ∧ θ p ≤ 1)
    (Ω : Set Plane) (hone : ∀ p ∈ Ω, θ p = 1) (n₀ : ℕ)
    (hheight : ∀ n p, p ∈ tsupport θ → mollifierRadius (n+n₀) < p.2)
    (hlocal : ∀ n p, p ∈ tsupport θ → productRectangle (n+n₀) p.1 p.2 ⊆ K) :
    HasLocalL2GradientOn Ω (localizedPlane N K B f) := by
  obtain ⟨D, hD0, hD⟩ := exists_cutoff_gradient_budget hθ hc
  let F := localizedPlane N K B f
  have hF : MemLp F 2 volume := localizedPlane_memLp N hK hB f
  let W := localizedPlane N K B w
  have hW : MemLp W 2 volume := localizedPlane_memLp N hK hB w
  let U n := actualProductSmooth N K B f (n+n₀)
  have hU (n : ℕ) : ContDiff ℝ ∞ (U n) := actualProductSmooth_cinfty N hK hB f _
  have hU2 (n : ℕ) : MemLp (U n) 2 volume := actualProductSmooth_memLp N hK hB hbound f _
  have hadd : StrictMono (fun n : ℕ => n+n₀) := fun i j hij => Nat.add_lt_add_right hij n₀
  have hvalue : Tendsto (fun n => (hU2 n).toLp (U n)) atTop (𝓝 (hF.toLp F)) :=
    (actualProductSmooth_strong_L2 N hK hB hbound f).comp hadd.tendsto_atTop
  let C : ℝ := (4*D+1)*‖hF.toLp F‖^2 + (((a⁻¹)^2)*‖hW.toLp W‖)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he (n : ℕ) :
      ‖weightedGradientL2 hθ hc (hU n) xDirection‖^2 +
        ‖weightedGradientL2 hθ hc (hU n) yDirection‖^2 ≤ C := by
    let V : Plane → ℂ := -potentialSmooth N K B a w (n+n₀)
    have hV : ContDiff ℝ ∞ V := (productSmooth_cinfty
      ((localizedPotential_memLp N hK hB ha w).locallyIntegrable (by norm_num)) _).neg
    have hV2 : MemLp V 2 volume := (potentialSmooth_memLp N hK hB ha hbound w _).neg
    have hPDE : ∀ p ∈ tsupport θ, euclideanLaplacian (U n) p = V p := by
      intro p hp
      exact actual_adjoint_smoothed_equation N hfw hK hB ha hbound hlower
        (n+n₀) p.1 p.2 (hheight n p hp) (hlocal n p hp)
    have h := smooth_interior_L2_budget hθ hc hrange hD (hU n) hV.continuous
      (hU2 n) hV2 hPDE
    have hu := mul_self_le_mul_self (norm_nonneg _)
      (actualProductSmooth_uniform_L2_bound N hK hB hbound f (n+n₀))
    have hVbound : ‖hV2.toLp V‖ ≤ (a⁻¹)^2*‖hW.toLp W‖ := by
      simpa only [V, MemLp.toLp_neg, norm_neg] using
        potentialSmooth_uniform_L2_bound N hK hB ha hbound w (n+n₀)
    have hv := mul_self_le_mul_self (norm_nonneg _) hVbound
    simp only [← pow_two] at hu hv
    have hcoef : 0 ≤ 4*D+1 := by linarith
    rw [weightedEnergy_eq_L2 hθ hc (hU n)] at h
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hu hcoef) hv)
  exact local_gradient_of_smooth_L2_approximation F hF U hU hU2 hvalue hθ hc C hC he Ω hone

end
end ImbalancedChen.Part3.GammaActualAdjointLocalizedH120261026b
