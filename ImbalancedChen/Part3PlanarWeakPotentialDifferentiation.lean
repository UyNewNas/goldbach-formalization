import ImbalancedChen.Part3PlanarWeakDifferentialMultiindex
import ImbalancedChen.Part3UpperChartLocalSmoothMultiplierH1

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Differentiate a genuine weak equation Delta u=a*u on the positive real
chart. The derivative g is only a local L2 weak derivative. The old
proved local multiplier transposition pays the derivative of a*u; native
test commutation pays the Laplacian. All displayed integrands are L1.
No classical derivative of u or PDE for g is a premise.
-/

namespace ImbalancedChen.Part3.PlanarWeakPotentialDifferentiation20261026b
noncomputable section
open Set MeasureTheory Filter
open CompactC2ProductMollifier20261026a
open CanonicalTensorHyperbolicLaplacianForm20261024z
open Gamma0CompactGreenProductL120261025a LocalWeakH1CutoffProduct20261026b
open UpperChartLocalSmoothMultiplierH120261026b PlanarWeakDifferentialMultiindex20261026b

theorem compact_continuous_multiplier_memLp {K : Set Plane} (hK : IsCompact K)
    {a u : Plane → ℂ} (ha : ContinuousOn a K)
    (hu : MemLp u 2 ((volume : Measure Plane).restrict K)) :
    MemLp (fun p => a p*u p) 2 ((volume : Measure Plane).restrict K) := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image ha.norm
  apply hu.of_le_mul ((ha.aestronglyMeasurable hK.measurableSet).mul hu.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC ⟨p,hp,rfl⟩) (norm_nonneg _)

theorem compact_test_local_L2_integrable (Ω : Set Plane) (u : Plane → ℂ)
    (hu : ∀ K : Set Plane, IsCompact K → K ⊆ Ω →
      MemLp u 2 ((volume : Measure Plane).restrict K))
    {ψ : Plane → ℂ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ω) : Integrable (fun p => ψ p*u p) volume := by
  have hI := MemLp.integrable_mul (p := 2) (q := 2)
    ((hψ.memLp_of_hasCompactSupport hc (p := 2)).restrict (tsupport ψ)) (hu _ hc hs)
  have hsupport : Function.support (fun p => ψ p*u p) ⊆ tsupport ψ := by
    intro p hp
    by_contra hn
    exact hp (by rw [image_eq_zero_of_notMem_tsupport hn,zero_mul])
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hI

theorem local_smooth_product_derivative_memLp (v : Plane) (u g a : Plane → ℂ)
    (hu : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp u 2 ((volume : Measure Plane).restrict K))
    (hg : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp g 2 ((volume : Measure Plane).restrict K))
    (ha : ContDiffOn ℝ ∞ a positiveChart) :
    ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp (productDerivative a u g v) 2 ((volume : Measure Plane).restrict K) := by
  intro K hK hs
  exact (compact_continuous_multiplier_memLp hK
    ((directional_cinfty_on v ha).continuousOn.mono hs) (hu K hK hs)).add
      (compact_continuous_multiplier_memLp hK (ha.continuousOn.mono hs) (hg K hK hs))

/-- Actual first differentiated equation, including both L1 assertions.
`productDerivative a u g v = D_v a*u+a*g` is a literal function. -/
theorem weak_potential_equation_derivative (v : Plane) (u g a : Plane → ℂ)
    (hu : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp u 2 ((volume : Measure Plane).restrict K))
    (hg : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp g 2 ((volume : Measure Plane).restrict K))
    (hweak : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ positiveChart →
      (∫ p, star (ψ p)*g p) = -(∫ p, star (directional v ψ p)*u p))
    (ha : ContDiffOn ℝ ∞ a positiveChart)
    (hΔ : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ positiveChart →
      (∫ p, star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p)*u p) =
        ∫ p, star (ψ p)*(a p*u p))
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) :
    Integrable (fun p => star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p)*g p) volume ∧
      Integrable (fun p => star (ψ p)*productDerivative a u g v p) volume ∧
      (∫ p, star (ProductConvolutionSecondDerivatives20261026a.euclideanLaplacian ψ p)*g p) =
        ∫ p, star (ψ p)*productDerivative a u g v p := by
  have hstar (t : Plane → ℂ) : tsupport (fun p => star (t p)) ⊆ tsupport t :=
    tsupport_comp_subset (g := star) (by simp) t
  refine ⟨compact_test_local_L2_integrable positiveChart g hg
      (laplacian_smooth hψ).continuous.star
      ((laplacian_compact hc).comp_left (g := star) (by simp))
      ((hstar _).trans ((laplacian_support ψ).trans hs)),
    compact_test_local_L2_integrable positiveChart (productDerivative a u g v)
      (local_smooth_product_derivative_memLp v u g a hu hg ha) hψ.continuous.star
      (hc.comp_left (g := star) (by simp)) ((hstar ψ).trans hs),?_⟩
  exact weak_laplacian_derivative positiveChart v u g (fun p => a p*u p)
    (productDerivative a u g v) hweak
    (fun t ht htc hts => raw_local_smooth_multiplier_weak v u g a hu hg hweak ha ht htc hts)
    hΔ ψ hψ hc hs

end
end ImbalancedChen.Part3.PlanarWeakPotentialDifferentiation20261026b
