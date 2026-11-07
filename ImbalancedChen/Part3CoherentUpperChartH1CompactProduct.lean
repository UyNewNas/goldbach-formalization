import ImbalancedChen.Part3WholeUpperChartWeakH1Patching
import ImbalancedChen.Part3LocalWeakH1CutoffProduct

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A coherent WHOLE-chart weak gradient is only locally L2. Compact smooth
multiplication produces a genuine CompactH1Jet with the LITERAL original
gradient fields Dchi*F+chi*Gx/Gy. Indicators are used only to obtain legal
global L2 extensions; their arbitrary Lp representatives are removed by
proved AE equalities. No global ordinary L2 of the raw automorphic field,
local-to-global H1 seam, or gradient covariance is assumed.
-/

namespace ImbalancedChen.Part3.CoherentUpperChartH1CompactProduct20261026b
noncomputable section
open Set Filter MeasureTheory
open CompactC2ProductMollifier20261026a WeakH1ProductMollifierDerivative20261026a
open PlanarLocalWeakGradientExtraction20261026b LocalWeakH1CutoffProduct20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z

theorem exists_coherent_compact_H1_product (F Gx Gy : Plane → ℂ)
    (hb : ∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp F 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gx 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gy 2 ((volume : Measure Plane).restrict K))
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p)*Gx p) = -(∫ p, star (directional ex ψ p)*F p)) ∧
      ((∫ p, star (ψ p)*Gy p) = -(∫ p, star (directional ey ψ p)*F p)))
    {χ : Plane → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ upperChart) :
    ∃ J : CompactH1Jet, J.value = (fun p => χ p*F p) ∧
      J.dx = productDerivative χ F Gx ex ∧ J.dy = productDerivative χ F Gy ey ∧
      tsupport J.value ⊆ tsupport χ ∧ tsupport J.dx ⊆ tsupport χ ∧ tsupport J.dy ⊆ tsupport χ := by
  let S := tsupport χ
  have hS : MeasurableSet S := isClosed_tsupport.measurableSet
  obtain ⟨hF,hX,hY⟩ := hb S hc hs
  have hF0 : MemLp (S.indicator F) 2 volume := (memLp_indicator_iff_restrict hS).2 hF
  have hX0 : MemLp (S.indicator Gx) 2 volume := (memLp_indicator_iff_restrict hS).2 hX
  have hY0 : MemLp (S.indicator Gy) 2 volume := (memLp_indicator_iff_restrict hS).2 hY
  let X := hX0.toLp (S.indicator Gx)
  let Y := hY0.toLp (S.indicator Gy)
  have hgrad : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      ((∫ p, star (ψ p)*X p) = -(∫ p, star (directional ex ψ p)*S.indicator F p)) ∧
      ((∫ p, star (ψ p)*Y p) = -(∫ p, star (directional ey ψ p)*S.indicator F p)) := by
    intro ψ hψ hψc hψS
    have hpx : (∫ p, star (ψ p)*X p) = ∫ p, star (ψ p)*Gx p := by
      apply integral_congr_ae
      filter_upwards [hX0.coeFn_toLp] with p hp
      change X p = S.indicator Gx p at hp
      rw [hp]
      by_cases hpS : p ∈ S
      · rw [Set.indicator_of_mem hpS]
      · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hpS (hψS ht)),star_zero,zero_mul]
    have hpy : (∫ p, star (ψ p)*Y p) = ∫ p, star (ψ p)*Gy p := by
      apply integral_congr_ae
      filter_upwards [hY0.coeFn_toLp] with p hp
      change Y p = S.indicator Gy p at hp
      rw [hp]
      by_cases hpS : p ∈ S
      · rw [Set.indicator_of_mem hpS]
      · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hpS (hψS ht)),star_zero,zero_mul]
    have hm (v : Plane) : (∫ p, star (directional v ψ p)*S.indicator F p) =
        ∫ p, star (directional v ψ p)*F p := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        by_cases hpS : p ∈ S
        · rw [Set.indicator_of_mem hpS]
        · have hn : p ∉ tsupport ψ := fun ht => hpS (hψS ht)
          have hd : directional v ψ p = 0 := by
            simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
          simp only [hd,star_zero,zero_mul])
    obtain ⟨hx,hy⟩ := hw ψ hψ hψc (hψS.trans hs)
    exact ⟨by rw [hpx,hm ex]; exact hx,by rw [hpy,hm ey]; exact hy⟩
  let J0 := cutoffJet hF0 X Y hχ hc (Subset.refl S) hgrad
  have he0 : J0.value =ᵐ[(volume : Measure Plane)] (fun p => χ p*F p) :=
    Eventually.of_forall (fun p => by
      by_cases hp : p ∈ S
      · simp only [J0,cutoffJet,Set.indicator_of_mem hp]
      · have hz : χ p = 0 := image_eq_zero_of_notMem_tsupport hp
        simp only [J0,cutoffJet,hz,zero_mul])
  have hdχ (v p : Plane) (hp : p ∉ S) : directional v χ p = 0 := by
    simp only [directional,fderiv_of_notMem_tsupport ℝ hp,ContinuousLinearMap.zero_apply]
  have heX : J0.dx =ᵐ[(volume : Measure Plane)] productDerivative χ F Gx ex := by
    filter_upwards [hX0.coeFn_toLp] with p hp
    change X p = S.indicator Gx p at hp
    by_cases hpS : p ∈ S
    · simp only [J0,cutoffJet,productDerivative,hp,Set.indicator_of_mem hpS]
    · have hz : χ p = 0 := image_eq_zero_of_notMem_tsupport hpS
      simp only [J0,cutoffJet,productDerivative,hz,hdχ ex p hpS,zero_mul,add_zero]
  have heY : J0.dy =ᵐ[(volume : Measure Plane)] productDerivative χ F Gy ey := by
    filter_upwards [hY0.coeFn_toLp] with p hp
    change Y p = S.indicator Gy p at hp
    by_cases hpS : p ∈ S
    · simp only [J0,cutoffJet,productDerivative,hp,Set.indicator_of_mem hpS]
    · have hz : χ p = 0 := image_eq_zero_of_notMem_tsupport hpS
      simp only [J0,cutoffJet,productDerivative,hz,hdχ ey p hpS,zero_mul,add_zero]
  let J : CompactH1Jet := {
    value := fun p => χ p*F p
    dx := productDerivative χ F Gx ex
    dy := productDerivative χ F Gy ey
    value_memLp := J0.value_memLp.ae_eq he0
    dx_memLp := J0.dx_memLp.ae_eq heX
    dy_memLp := J0.dy_memLp.ae_eq heY
    value_compact := hc.mul_right
    weak_dx := by
      intro ψ hψ hψc
      have hl : (∫ p, directional ex ψ p*(χ p*F p)) =
          ∫ p, directional ex ψ p*J0.value p := by
        apply integral_congr_ae
        filter_upwards [he0] with p hp
        rw [hp]
      have hr : (∫ p, ψ p*productDerivative χ F Gx ex p) = ∫ p, ψ p*J0.dx p := by
        apply integral_congr_ae
        filter_upwards [heX] with p hp
        rw [hp]
      rw [hl,hr]
      exact J0.weak_dx ψ hψ hψc
    weak_dy := by
      intro ψ hψ hψc
      have hl : (∫ p, directional ey ψ p*(χ p*F p)) =
          ∫ p, directional ey ψ p*J0.value p := by
        apply integral_congr_ae
        filter_upwards [he0] with p hp
        rw [hp]
      have hr : (∫ p, ψ p*productDerivative χ F Gy ey p) = ∫ p, ψ p*J0.dy p := by
        apply integral_congr_ae
        filter_upwards [heY] with p hp
        rw [hp]
      rw [hl,hr]
      exact J0.weak_dy ψ hψ hψc }
  exact ⟨J,rfl,rfl,rfl,tsupport_mul_subset_left,productDerivative_tsupport ex,productDerivative_tsupport ey⟩

end
end ImbalancedChen.Part3.CoherentUpperChartH1CompactProduct20261026b
