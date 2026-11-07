import ImbalancedChen.Part3MobiusSmoothFirstJetWeakTests
import ImbalancedChen.Part3ActualMobiusFirstJetConvergence
import ImbalancedChen.Part3SupportedH1FiniteTensorDensity
import Mathlib.Topology.Sequences

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine compact H1 jet has weak Mobius pullback derivatives equal to
the actual real transpose-Jacobian fields. Actual finite-tensor H1 density
produces smooth first-jet approximants; the true Jacobian L2 estimates
transport all three limits, and native smooth-test identities pass to
those limits. No weak chain rule, gradient equivariance or transported
derivative identity is assumed. All displayed test products are L1.
-/

namespace ImbalancedChen.Part3.CompactH1MobiusWeakTransport20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a MaassWeakOperatorCore20261024zz
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open WeakH1ProductMollifierDerivative20261026a SupportedH1FiniteTensorDensity20261026a
open ActualMobiusPairChartL2Transport20261026b MobiusStrongFirstJetL2Errors20261026b
open MobiusSmoothFirstJetWeakTests20261026b ActualMobiusFirstJetConvergence20261026b

private theorem inner_local_toLp {K : Set Plane} {P Q : Plane → ℂ}
    (hP : MemLp P 2 ((volume : Measure Plane).restrict K))
    (hQ : MemLp Q 2 ((volume : Measure Plane).restrict K)) :
    inner ℂ (hP.toLp P) (hQ.toLp Q) = ∫ p in K, star (P p)*Q p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hP.coeFn_toLp,hQ.coeFn_toLp] with p hp hq
  simp only [RCLike.inner_apply',Complex.star_def,hp,hq]

private theorem local_pair_eq_global {K : Set Plane} {ψ : Plane → ℂ}
    (hs : tsupport ψ ⊆ K) (R : Plane → ℂ) :
    (∫ p in K, star (ψ p)*R p) = ∫ p, star (ψ p)*R p :=
  setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht)),star_zero,zero_mul])

theorem compact_test_product_integrable {K : Set Plane} {ψ R : Plane → ℂ}
    (hR : MemLp R 2 ((volume : Measure Plane).restrict K))
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ K) :
    Integrable (fun p => star (ψ p)*R p) volume := by
  have hp := MemLp.integrable_mul (p := 2) (q := 2)
    ((hψ.continuous.memLp_of_hasCompactSupport hc (p := 2)).restrict K).star hR
  have hsupport : Function.support (fun p => star (ψ p)*R p) ⊆ K := by
    intro p hpr
    by_contra hn
    exact hpr (by rw [image_eq_zero_of_notMem_tsupport (fun ht => hn (hs ht)),star_zero,zero_mul])
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hp

private theorem smoothJetClass_value {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    smoothJetClass hF hc 0 = (hF.continuous.memLp_of_hasCompactSupport hc (p := 2)).toLp F := by
  apply Lp.ext
  filter_upwards [(partial_memLp hF hc (firstIndex 0)).coeFn_toLp,
    (hF.continuous.memLp_of_hasCompactSupport hc (p := 2)).coeFn_toLp] with p hp hq
  rw [hp,hq,partialJet_eq_mixedJet hF]
  rfl

private theorem smoothJetClass_dx {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    smoothJetClass hF hc 1 = ((directional_smooth ex hF).continuous.memLp_of_hasCompactSupport
      (directional_compact ex hc) (p := 2)).toLp (directional ex F) := by
  apply Lp.ext
  filter_upwards [(partial_memLp hF hc (firstIndex 1)).coeFn_toLp,
    ((directional_smooth ex hF).continuous.memLp_of_hasCompactSupport
      (directional_compact ex hc) (p := 2)).coeFn_toLp] with p hp hq
  rw [hp,hq,partialJet_eq_mixedJet hF]
  rfl

private theorem smoothJetClass_dy {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) :
    smoothJetClass hF hc 2 = ((directional_smooth ey hF).continuous.memLp_of_hasCompactSupport
      (directional_compact ey hc) (p := 2)).toLp (directional ey F) := by
  apply Lp.ext
  filter_upwards [(partial_memLp hF hc (firstIndex 2)).coeFn_toLp,
    ((directional_smooth ey hF).continuous.memLp_of_hasCompactSupport
      (directional_compact ey hc) (p := 2)).coeFn_toLp] with p hp hq
  rw [hp,hq,partialJet_eq_mixedJet hF]
  rfl

/-- The approximating smooth functions and their three native L2 limits
are PRODUCED by genuine H1 density, rather than supplied as an H1 premise. -/
private theorem exists_smooth_H1_approximation (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (A a b : ℝ) (ha : 0 < a) (hs : tsupport J.value ⊆ planeBox A a b) :
    ∃ (F : ℕ → Plane → ℂ) (hF : ∀ n, ContDiff ℝ ∞ (F n))
      (hc : ∀ n, HasCompactSupport (F n)),
      Tendsto (fun n => ((hF n).continuous.memLp_of_hasCompactSupport (hc n) (p := 2)).toLp (F n))
        atTop (𝓝 (J.value_memLp.toLp J.value)) ∧
      Tendsto (fun n => ((directional_smooth ex (hF n)).continuous.memLp_of_hasCompactSupport
        (directional_compact ex (hc n)) (p := 2)).toLp (directional ex (F n)))
        atTop (𝓝 (J.dx_memLp.toLp J.dx)) ∧
      Tendsto (fun n => ((directional_smooth ey (hF n)).continuous.memLp_of_hasCompactSupport
        (directional_compact ey (hc n)) (p := 2)).toLp (directional ey (F n)))
        atTop (𝓝 (J.dy_memLp.toLp J.dy)) := by
  obtain ⟨V,hV,hlim⟩ := mem_closure_iff_seq_limit.mp
    (compactH1_mem_finiteTensorJet_closure J hx hy A a b ha hs)
  change ∀ n, ∃ (F : Plane → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F),
    (∃ (ι : Type) (s : Finset ι) (T : ι → Gamma0SmoothCompactTensorCore20261025a.SmoothCompactTensor),
      F = finiteChartFunction s (fun t => (T t).toCompactTensor)) ∧ V n = smoothJetClass hF hc at hV
  choose F hF hc hfinite hclass using hV
  have hl : Tendsto (fun n => smoothJetClass (hF n) (hc n)) atTop (𝓝 (h1JetClass J)) := by
    have heq : V = fun n => smoothJetClass (hF n) (hc n) := funext hclass
    simpa only [heq] using hlim
  refine ⟨F,hF,hc,?_,?_,?_⟩
  · have ht := tendsto_pi_nhds.mp hl 0
    simpa only [smoothJetClass_value,h1JetClass,component,Matrix.cons_val_zero] using ht
  · have ht := tendsto_pi_nhds.mp hl 1
    simpa only [smoothJetClass_dx,h1JetClass,component,Matrix.cons_val_one] using ht
  · have ht := tendsto_pi_nhds.mp hl 2
    simpa only [smoothJetClass_dy,h1JetClass,component,Matrix.cons_val_two] using ht

theorem compactH1_mobius_test_products_integrable (J : CompactH1Jet)
    (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ K) :
    Integrable (fun p => star (ψ p)*pairRawJetX g J.dx J.dy p) volume ∧
    Integrable (fun p => star (ψ p)*pairRawJetY g J.dx J.dy p) volume ∧
    Integrable (fun p => star (directional ex ψ p)*J.value (mobiusChart g p)) volume ∧
    Integrable (fun p => star (directional ey ψ p)*J.value (mobiusChart g p)) volume := by
  have hvalue := pairchart_memLp_comp g hK hKp (J.value_memLp.restrict _)
  obtain ⟨hX,hY⟩ := pairchart_rawJet_memLp g hK hKp (J.dx_memLp.restrict _) (J.dy_memLp.restrict _)
  exact ⟨compact_test_product_integrable hX hψ hc hs,
    compact_test_product_integrable hY hψ hc hs,
    compact_test_product_integrable hvalue (directional_smooth ex hψ)
      (directional_compact ex hc) ((tsupport_fderiv_apply_subset ℝ ex).trans hs),
    compact_test_product_integrable hvalue (directional_smooth ey hψ)
      (directional_compact ey hc) ((tsupport_fderiv_apply_subset ℝ ey).trans hs)⟩

theorem compactH1_mobius_weak_transport (J : CompactH1Jet)
    (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (A a b : ℝ) (ha : 0 < a) (hsJ : tsupport J.value ⊆ planeBox A a b)
    (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) :
    MemLp (fun p => J.value (mobiusChart g p)) 2 ((volume : Measure Plane).restrict K) ∧
    MemLp (pairRawJetX g J.dx J.dy) 2 ((volume : Measure Plane).restrict K) ∧
    MemLp (pairRawJetY g J.dx J.dy) 2 ((volume : Measure Plane).restrict K) ∧
    ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ K →
      ((∫ p, star (ψ p)*pairRawJetX g J.dx J.dy p) =
        -(∫ p, star (directional ex ψ p)*J.value (mobiusChart g p))) ∧
      ((∫ p, star (ψ p)*pairRawJetY g J.dx J.dy p) =
        -(∫ p, star (directional ey ψ p)*J.value (mobiusChart g p))) := by
  obtain ⟨F,hF,hc,h0,hxlim,hylim⟩ := exists_smooth_H1_approximation J hx hy A a b ha hsJ
  let h0F n := (hF n).continuous.memLp_of_hasCompactSupport (hc n) (p := (2 : ℝ≥0∞))
  let hxF n := (directional_smooth ex (hF n)).continuous.memLp_of_hasCompactSupport
    (directional_compact ex (hc n)) (p := (2 : ℝ≥0∞))
  let hyF n := (directional_smooth ey (hF n)).continuous.memLp_of_hasCompactSupport
    (directional_compact ey (hc n)) (p := (2 : ℝ≥0∞))
  have hvalue := compClass_tendsto g hK hKp h0F J.value_memLp h0
  obtain ⟨hX,hY⟩ := jetClass_tendsto g hK hKp hxF hyF J.dx_memLp J.dy_memLp hxlim hylim
  have hvalueLp := pairchart_memLp_comp g hK hKp (J.value_memLp.restrict _)
  obtain ⟨hXLp,hYLp⟩ := pairchart_rawJet_memLp g hK hKp
    (J.dx_memLp.restrict _) (J.dy_memLp.restrict _)
  refine ⟨hvalueLp,hXLp,hYLp,?_⟩
  intro ψ hψ hψc hψK
  have hψpos : tsupport ψ ⊆ positiveChart := fun p hp => hKp p (hψK hp)
  have hdxK : tsupport (directional ex ψ) ⊆ K := (tsupport_fderiv_apply_subset ℝ ex).trans hψK
  have hdyK : tsupport (directional ey ψ) ⊆ K := (tsupport_fderiv_apply_subset ℝ ey).trans hψK
  let P : LocalL2 K := ((hψ.continuous.memLp_of_hasCompactSupport hψc (p := 2)).restrict K).toLp ψ
  let DX : LocalL2 K := (((directional_smooth ex hψ).continuous.memLp_of_hasCompactSupport
    (directional_compact ex hψc) (p := 2)).restrict K).toLp (directional ex ψ)
  let DY : LocalL2 K := (((directional_smooth ey hψ).continuous.memLp_of_hasCompactSupport
    (directional_compact ey hψc) (p := 2)).restrict K).toLp (directional ey ψ)
  have hnX (n : ℕ) : inner ℂ P (jetXClass g hK hKp (hxF n) (hyF n)) =
      -inner ℂ DX (compClass g hK hKp (h0F n)) := by
    dsimp only [P,DX,jetXClass,compClass]
    rw [inner_local_toLp,inner_local_toLp,local_pair_eq_global hψK,local_pair_eq_global hdxK]
    exact (mobius_smooth_weak_tests g (hF n) hψ hψc hψpos).1
  have hnY (n : ℕ) : inner ℂ P (jetYClass g hK hKp (hxF n) (hyF n)) =
      -inner ℂ DY (compClass g hK hKp (h0F n)) := by
    dsimp only [P,DY,jetYClass,compClass]
    rw [inner_local_toLp,inner_local_toLp,local_pair_eq_global hψK,local_pair_eq_global hdyK]
    exact (mobius_smooth_weak_tests g (hF n) hψ hψc hψpos).2
  have hPc : Tendsto (fun _ : ℕ => P) atTop (𝓝 P) := tendsto_const_nhds
  have hDXc : Tendsto (fun _ : ℕ => DX) atTop (𝓝 DX) := tendsto_const_nhds
  have hDYc : Tendsto (fun _ : ℕ => DY) atTop (𝓝 DY) := tendsto_const_nhds
  have htX := hPc.inner hX
  have htY := hPc.inner hY
  have hrX := (hDXc.inner hvalue).neg
  have hrY := (hDYc.inner hvalue).neg
  have heX : (fun n => inner ℂ P (jetXClass g hK hKp (hxF n) (hyF n))) =
      (fun n => -inner ℂ DX (compClass g hK hKp (h0F n))) := funext hnX
  have heY : (fun n => inner ℂ P (jetYClass g hK hKp (hxF n) (hyF n))) =
      (fun n => -inner ℂ DY (compClass g hK hKp (h0F n))) := funext hnY
  rw [← heX] at hrX
  rw [← heY] at hrY
  have hfinalX := tendsto_nhds_unique htX hrX
  have hfinalY := tendsto_nhds_unique htY hrY
  dsimp only [P,DX,jetXClass,compClass] at hfinalX
  dsimp only [P,DY,jetYClass,compClass] at hfinalY
  rw [inner_local_toLp,inner_local_toLp,local_pair_eq_global hψK,local_pair_eq_global hdxK] at hfinalX
  rw [inner_local_toLp,inner_local_toLp,local_pair_eq_global hψK,local_pair_eq_global hdyK] at hfinalY
  exact ⟨hfinalX,hfinalY⟩

end
end ImbalancedChen.Part3.CompactH1MobiusWeakTransport20261026b
