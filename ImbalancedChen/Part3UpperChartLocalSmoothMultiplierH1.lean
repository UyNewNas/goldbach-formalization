import ImbalancedChen.Part3CoherentUpperChartH1CompactProduct
import ImbalancedChen.Part3ArbitraryCompactFirstGradientIBP

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A multiplier smooth ONLY on the positive chart preserves raw whole-chart
H1_loc. It need not have compact support on H. Compact positive tests
remove the boundary seam: chi*test is proved globally smooth, compact and
positive-supported before the raw weak equation is invoked. The literal
Leibniz derivatives and every local L2/test L1 assertion are proved.
-/

namespace ImbalancedChen.Part3.UpperChartLocalSmoothMultiplierH120261026b
noncomputable section
open Set Filter MeasureTheory
open CompactC2ProductMollifier20261026a LocalWeakH1CutoffProduct20261026b
open Gamma0CompactGreenProductL120261025a MaassWeakOperatorCore20261024zz
open ArbitraryCompactFirstGradientIBP20261026b CanonicalTensorHyperbolicLaplacianForm20261024z

theorem compact_positive_multiplier_test_smooth {χ ψ : Plane → ℂ}
    (hχ : ContDiffOn ℝ ∞ χ positiveChart) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ positiveChart) : ContDiff ℝ ∞ (fun p => χ p*ψ p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ tsupport ψ
  · exact ((hχ p (hs hp)).contDiffAt (positiveChart_isOpen.mem_nhds (hs hp))).mul hψ.contDiffAt
  · have he := notMem_tsupport_iff_eventuallyEq.mp hp
    have hz : (fun q => χ q*ψ q) =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [he] with q hq
      simp only [hq,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem local_multiplier_test_directional (v : Plane) {χ ψ : Plane → ℂ}
    (hχ : ContDiffOn ℝ ∞ χ positiveChart) (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ positiveChart) :
    directional v (fun p => χ p*ψ p) = fun p => directional v χ p*ψ p+χ p*directional v ψ p := by
  funext p
  by_cases hp : p ∈ positiveChart
  · have hdχ := ((hχ.differentiableOn (by simp)) p hp).differentiableAt (positiveChart_isOpen.mem_nhds hp)
    simp only [directional,fderiv_fun_mul hdχ (hψ.differentiable (by simp) p),
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  · have hn : p ∉ tsupport ψ := fun ht => hp (hs ht)
    have hψ0 : ψ p = 0 := image_eq_zero_of_notMem_tsupport hn
    have hdψ : directional v ψ p = 0 := by
      simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
    have hprod : p ∉ tsupport (fun p => χ p*ψ p) :=
      fun ht => hn (tsupport_mul_subset_right ht)
    have hdprod : directional v (fun p => χ p*ψ p) p = 0 := by
      simp only [directional,fderiv_of_notMem_tsupport ℝ hprod,ContinuousLinearMap.zero_apply]
    rw [hdprod,hψ0,hdψ]
    simp only [mul_zero,zero_add]

theorem directional_cinfty_on (v : Plane) {χ : Plane → ℂ}
    (hχ : ContDiffOn ℝ ∞ χ positiveChart) : ContDiffOn ℝ ∞ (directional v χ) positiveChart :=
  (hχ.fderiv_of_isOpen positiveChart_isOpen (by simp)).clm_apply contDiffOn_const

private theorem compact_local_multiplier_memLp {K : Set Plane} (hK : IsCompact K)
    {χ F : Plane → ℂ} (hχ : ContinuousOn χ K) (hF : MemLp F 2 ((volume : Measure Plane).restrict K)) :
    MemLp (fun p => χ p*F p) 2 ((volume : Measure Plane).restrict K) := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image hχ.norm
  apply hF.of_le_mul ((hχ.aestronglyMeasurable hK.measurableSet).mul hF.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC ⟨p,hp,rfl⟩) (norm_nonneg _)

private theorem compact_coefficient_integrable (R : Plane → ℂ)
    (hR : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp R 2 ((volume : Measure Plane).restrict K))
    {a : Plane → ℂ} (ha : Continuous a) (hc : HasCompactSupport a) (hs : tsupport a ⊆ positiveChart) :
    Integrable (fun p => a p*R p) volume := by
  have hl := MemLp.integrable_mul (p := 2) (q := 2)
    ((ha.memLp_of_hasCompactSupport hc (p := 2)).restrict (tsupport a)) (hR _ hc hs)
  have hsupport : Function.support (fun p => a p*R p) ⊆ tsupport a := by
    intro p hp
    by_contra hn
    exact hp (by rw [image_eq_zero_of_notMem_tsupport hn,zero_mul])
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hl

theorem raw_local_smooth_multiplier_weak (v : Plane) (F G χ : Plane → ℂ)
    (hF : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp F 2 ((volume : Measure Plane).restrict K))
    (hG : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp G 2 ((volume : Measure Plane).restrict K))
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ positiveChart →
      (∫ p, star (ψ p)*G p) = -(∫ p, star (directional v ψ p)*F p))
    (hχ : ContDiffOn ℝ ∞ χ positiveChart)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) :
    (∫ p, star (ψ p)*productDerivative χ F G v p) =
      -(∫ p, star (directional v ψ p)*(χ p*F p)) := by
  have hstarS : tsupport (fun p => star (ψ p)) ⊆ positiveChart :=
    (tsupport_comp_subset (g := star) (by simp) ψ).trans hs
  have hstarC : HasCompactSupport (fun p => star (ψ p)) := hc.comp_left (g := star) (by simp)
  let P : Plane → ℂ := fun p => χ p*star (ψ p)
  have hP : ContDiff ℝ ∞ P := compact_positive_multiplier_test_smooth hχ hψ.star hstarS
  have hPc : HasCompactSupport P := hstarC.mul_left
  have hPs : tsupport P ⊆ positiveChart := tsupport_mul_subset_right.trans hstarS
  have hDP : directional v P = fun p => directional v χ p*star (ψ p)+χ p*star (directional v ψ p) := by
    rw [show P = (fun p => χ p*star (ψ p)) from rfl,
      local_multiplier_test_directional v hχ hψ.star hstarS]
    funext p
    simp [directional,fderiv_star]
  have hDstar : directional v (fun p => star (P p)) = fun p => star (directional v P p) := by
    funext p
    simp [directional,fderiv_star]
  have hweak := hw (fun p => star (P p)) hP.star (hPc.comp_left (g := star) (by simp))
    ((tsupport_comp_subset (g := star) (by simp) P).trans hPs)
  simp only [hDstar,star_star] at hweak
  let A : ℂ := ∫ p, χ p*star (directional v ψ p)*F p
  let B : ℂ := ∫ p, directional v χ p*star (ψ p)*F p
  let C : ℂ := ∫ p, χ p*star (ψ p)*G p
  have hDψs : tsupport (fun p => star (directional v ψ p)) ⊆ positiveChart :=
    (tsupport_comp_subset (g := star) (by simp) (directional v ψ)).trans
      ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  have hA : Integrable (fun p => χ p*star (directional v ψ p)*F p) volume :=
    compact_coefficient_integrable F hF
      (compact_positive_multiplier_test_smooth hχ (directional_smooth v hψ).star hDψs).continuous
      (((directional_compact v hc).comp_left (g := star) (by simp)).mul_left)
      (tsupport_mul_subset_right.trans hDψs)
  have hB : Integrable (fun p => directional v χ p*star (ψ p)*F p) volume :=
    compact_coefficient_integrable F hF
      (compact_positive_multiplier_test_smooth (directional_cinfty_on v hχ) hψ.star hstarS).continuous
      hstarC.mul_left (tsupport_mul_subset_right.trans hstarS)
  have hC : Integrable (fun p => χ p*star (ψ p)*G p) volume :=
    compact_coefficient_integrable G hG hP.continuous hPc hPs
  have hsplit : (∫ p, directional v P p*F p) = B+A := by
    rw [hDP]
    calc
      _ = ∫ p, directional v χ p*star (ψ p)*F p+χ p*star (directional v ψ p)*F p := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by ring)
      _ = _ := integral_add hB hA
  have hrel : C = -(B+A) := by
    change C = -(∫ p, directional v P p*F p) at hweak
    rw [hsplit] at hweak
    exact hweak
  have hleft : (∫ p, star (ψ p)*productDerivative χ F G v p) = B+C := by
    calc
      _ = ∫ p, directional v χ p*star (ψ p)*F p+χ p*star (ψ p)*G p := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun p => by simp only [productDerivative]; ring)
      _ = _ := integral_add hB hC
  have hright : (∫ p, star (directional v ψ p)*(χ p*F p)) = A := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by ring)
  rw [hleft,hright]
  linear_combination hrel

theorem upperChart_H1_local_smooth_multiplier (F Gx Gy χ : Plane → ℂ)
    (hb : ∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp F 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gx 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gy 2 ((volume : Measure Plane).restrict K))
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ positiveChart →
      ((∫ p, star (ψ p)*Gx p) = -(∫ p, star (directional ex ψ p)*F p)) ∧
      ((∫ p, star (ψ p)*Gy p) = -(∫ p, star (directional ey ψ p)*F p)))
    (hχ : ContDiffOn ℝ ∞ χ positiveChart) :
    (∀ K : Set Plane, IsCompact K → K ⊆ positiveChart →
      MemLp (fun p => χ p*F p) 2 ((volume : Measure Plane).restrict K) ∧
      MemLp (productDerivative χ F Gx ex) 2 ((volume : Measure Plane).restrict K) ∧
      MemLp (productDerivative χ F Gy ey) 2 ((volume : Measure Plane).restrict K)) ∧
    (∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ positiveChart →
      ((∫ p, star (ψ p)*productDerivative χ F Gx ex p) =
        -(∫ p, star (directional ex ψ p)*(χ p*F p))) ∧
      ((∫ p, star (ψ p)*productDerivative χ F Gy ey p) =
        -(∫ p, star (directional ey ψ p)*(χ p*F p)))) := by
  constructor
  · intro K hK hs
    obtain ⟨hF,hGx,hGy⟩ := hb K hK hs
    exact ⟨compact_local_multiplier_memLp hK (hχ.continuousOn.mono hs) hF,
      (compact_local_multiplier_memLp hK ((directional_cinfty_on ex hχ).continuousOn.mono hs) hF).add
        (compact_local_multiplier_memLp hK (hχ.continuousOn.mono hs) hGx),
      (compact_local_multiplier_memLp hK ((directional_cinfty_on ey hχ).continuousOn.mono hs) hF).add
        (compact_local_multiplier_memLp hK (hχ.continuousOn.mono hs) hGy)⟩
  · intro ψ hψ hc hs
    exact ⟨raw_local_smooth_multiplier_weak ex F Gx χ (fun K hK hs => (hb K hK hs).1)
        (fun K hK hs => (hb K hK hs).2.1) (fun ψ hψ hc hs => (hw ψ hψ hc hs).1) hχ hψ hc hs,
      raw_local_smooth_multiplier_weak ey F Gy χ (fun K hK hs => (hb K hK hs).1)
        (fun K hK hs => (hb K hK hs).2.2) (fun ψ hψ hc hs => (hw ψ hψ hc hs).2) hχ hψ hc hs⟩

end
end ImbalancedChen.Part3.UpperChartLocalSmoothMultiplierH120261026b
