import ImbalancedChen.Part3ArbitraryCompactFirstGradientIBP
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Local weak derivatives are unique against actual arbitrary smooth tests.
The proof uses the native local fundamental lemma, deriving genuine L1
test products from local integrability and compact support. It then
identifies any such weak derivative with the classical real derivative
of a positive-chart C2 representative; no derivative equality is assumed.
-/

namespace ImbalancedChen.Part3.LocalSmoothWeakDerivativeUniqueness20261026b
noncomputable section
open Set Filter MeasureTheory
open MaassWeakOperatorCore20261024zz Gamma0CompactGreenProductL120261025a
open CompactC2ProductMollifier20261026a ArbitraryCompactFirstGradientIBP20261026b

theorem local_compact_test_product_integrable {U : Set Plane} {f ψ : Plane → ℂ}
    (hf : LocallyIntegrableOn f U volume) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun p => star (ψ p) * f p) volume := by
  have hfi := hf.integrableOn_compact_subset hs hc
  have hp : Integrable (fun p => star (ψ p) * f p)
      ((volume : Measure Plane).restrict (tsupport ψ)) := by
    simpa only [smul_eq_mul] using hfi.smul_of_top_right
      (hψ.star.memLp_top_of_hasCompactSupport (hc.comp_left rfl)
        ((volume : Measure Plane).restrict (tsupport ψ)))
  have hsupport : Function.support (fun p => star (ψ p) * f p) ⊆ tsupport ψ := by
    intro p hp
    by_contra hn
    exact hp (by simp only [image_eq_zero_of_notMem_tsupport hn,star_zero,zero_mul])
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hp

theorem local_ae_eq_of_smooth_test_pairings {U : Set Plane} (hU : IsOpen U)
    {f g : Plane → ℂ} (hf : LocallyIntegrableOn f U volume)
    (hg : LocallyIntegrableOn g U volume)
    (ht : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ p, star (ψ p) * f p) = ∫ p, star (ψ p) * g p) :
    ∀ᵐ p ∂(volume : Measure Plane), p ∈ U → f p = g p := by
  have htest : ∀ η : Plane → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ U →
      (∫ p, η p • (f p - g p)) = 0 := by
    intro η hη hηc hηs
    let ψ : Plane → ℂ := fun p => (η p : ℂ)
    have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hη
    have hψc : HasCompactSupport ψ := hηc.comp_left rfl
    have hψs : tsupport ψ ⊆ U := (tsupport_comp_subset rfl η).trans hηs
    have h1 := local_compact_test_product_integrable hf hψ.continuous hψc hψs
    have h2 := local_compact_test_product_integrable hg hψ.continuous hψc hψs
    have he := ht ψ hψ hψc hψs
    have hsub : (∫ p, star (ψ p) * (f p - g p)) = 0 := by
      simp_rw [mul_sub]
      rw [integral_sub h1 h2,he,sub_self]
    simpa only [ψ,Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using hsub
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg) htest
  filter_upwards [hz] with p hp
  intro hpin
  exact sub_eq_zero.mp (hp hpin)

/-- A local distributional derivative coincides with the literal real
Frechet derivative of an independently supplied classical representative. -/
theorem local_weak_derivative_eq_classical {U : Set Plane} (hU : IsOpen U)
    (hUp : U ⊆ positiveChart) (v : Plane) {F g : Plane → ℂ}
    (hF : ContDiffOn ℝ 2 F positiveChart) (hg : LocallyIntegrableOn g U volume)
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ p, star (ψ p) * g p) = -(∫ p, star (directional v ψ p) * F p)) :
    ∀ᵐ p ∂(volume : Measure Plane), p ∈ U → g p = directional v F p := by
  have hd : LocallyIntegrableOn (directional v F) U volume :=
    ((directional_continuousOn v hF).mono hUp).locallyIntegrableOn hU.measurableSet
  apply local_ae_eq_of_smooth_test_pairings hU hg hd
  intro ψ hψ hc hs
  rw [hw ψ hψ hc hs,plane_arbitrary_compact_first v hψ hc (hs.trans hUp) hF]
  simp only [neg_neg]

end
end ImbalancedChen.Part3.LocalSmoothWeakDerivativeUniqueness20261026b
