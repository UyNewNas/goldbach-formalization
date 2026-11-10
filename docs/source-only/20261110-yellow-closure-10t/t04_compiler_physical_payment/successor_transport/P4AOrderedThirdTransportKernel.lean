import ImbalancedChen.P4AOrderedThirdCompactComparison
import ImbalancedChen.ActualExtendedThirdFiniteTailIntegral

namespace ImbalancedChen.P4AOrderedThirdTransportKernel
noncomputable section
open Set Filter Topology MeasureTheory VariableEnvelope HistoricalThirdCoarse
open P4AOriginalOrderedThirdTable (Point retained capValue atPoint atPoint_on_cell)
open P4AOrderedThirdFifthOwnersAndTail (levelAt residual tail)
open scoped Classical BigOperators ENNReal

def K (e w : ℝ) (m : ℕ) (t : Point) :=
  actualExtendedThirdCapKernel e (levelAt e w m t) (t 0) (t 1) (t 2)

theorem measurable_level (e w : ℝ) (m : ℕ) : Measurable (levelAt e w m) := by
  have heq : atPoint e m=fun t => initial e+
      ∑ j∈retained e m,if t∈logPrimeMeshCell 0 (19/96) m j then capValue e m j-initial e else 0 := by
    funext t
    by_cases h : ∃ j∈retained e m,t∈logPrimeMeshCell 0 (19/96) m j
    · obtain ⟨j,hj,ht⟩ := h
      rw [atPoint_on_cell hj ht,Finset.sum_eq_single_of_mem j hj]
      · rw [if_pos ht]; ring
      · intro k hk hn; exact if_neg (fun hh => hn (logPrimeMeshCell_unique (by norm_num) hh ht))
    · rw [atPoint,dif_neg h,Finset.sum_eq_zero (fun j hj => if_neg (fun ht => h ⟨j,hj,ht⟩)),add_zero]
  have hm : Measurable (atPoint e m) := by
    rw [heq]; apply measurable_const.add; apply Finset.measurable_sum
    intro j _; exact measurable_const.piecewise (measurableSet_logPrimeMeshCell _ _ _ _) measurable_const
  exact hm.piecewise (isClosed_le continuous_const (continuous_apply 2)).measurableSet measurable_const

theorem measurable_kernel (e w : ℝ) (m : ℕ) : Measurable (K e w m) := by
  have hx : Measurable (fun t : Point => t 0) := (continuous_apply 0).measurable
  have hy : Measurable (fun t : Point => t 1) := (continuous_apply 1).measurable
  have hz : Measurable (fun t : Point => t 2) := (continuous_apply 2).measurable
  have hF := continuous_actualExtendedThirdLowerFactor.measurable
  have ha := hF.comp ((((measurable_const.sub hx).sub hy).sub hz).div hz :
    Measurable (fun t : Point => (thirdPrefixTheta-2*e-t 0-t 1-t 2)/t 2))
  have hb := hF.comp (((((measurable_level e w m).sub hx).sub hy).sub hz).div hz)
  exact (measurable_const.mul (ha.sub hb)).div ((hx.mul hy).mul (hz.pow_const 2))

private theorem finite_insert_last_fin3 (q x y : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
      (q, (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm (x, y)) = ![x, y, q] := by
  ext i
  fin_cases i <;>
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth, Fin.succAboveCases, MeasurableEquiv.piFinTwo]

/-- Actual Tonelli bridge; measurability is paid by the explicit capped kernel,
not supplied as a premise on the original functional. -/
theorem nested (h : ℝ) (K : (Fin 3 → ℝ) → ℝ) (hK : Measurable K) :
    (∫⁻ t in actualExtendedThirdOrderedTailRegion h, ENNReal.ofReal (K t)) =
      ∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z thirdPrefixRho, ∫⁻ y in Ioc z x,
        ENNReal.ofReal (K ![x, y, z]) := by
  let F : (Fin 3 → ℝ) → ℝ≥0∞ := (actualExtendedThirdOrderedTailRegion h).indicator
    (fun t => ENNReal.ofReal (K t))
  have hF : Measurable F := hK.ennreal_ofReal.indicator
    (measurableSet_actualExtendedThirdOrderedTailRegion h)
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  let E₂ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinSuccAbove _ 2
  have hE₂ : MeasurePreserving E₂ := volume_preserving_piFinTwo _
  have hvec (x y z : ℝ) : F ![x, y, z] =
      (Ioc 0 h).indicator (fun z => (Ioc z thirdPrefixRho).indicator
        (fun x => (Ioc z x).indicator
          (fun y => ENNReal.ofReal (K ![x, y, z])) y) x) z := by
    have hmem : ![x, y, z] ∈ actualExtendedThirdOrderedTailRegion h ↔
        z ∈ Ioc 0 h ∧ x ∈ Ioc z thirdPrefixRho ∧ y ∈ Ioc z x := by
      change (0 < z ∧ z ≤ h ∧ z < x ∧ x ≤ thirdPrefixRho ∧ z < y ∧ y ≤ x) ↔
        (0 < z ∧ z ≤ h) ∧ (z < x ∧ x ≤ thirdPrefixRho) ∧ (z < y ∧ y ≤ x)
      constructor
      · rintro ⟨hz, hzh, hzx, hx, hzy, hy⟩
        exact ⟨⟨hz, hzh⟩, ⟨hzx, hx⟩, ⟨hzy, hy⟩⟩
      · rintro ⟨⟨hz, hzh⟩, ⟨hzx, hx⟩, ⟨hzy, hy⟩⟩
        exact ⟨hz, hzh, hzx, hx, hzy, hy⟩
    by_cases hz : z ∈ Ioc 0 h <;>
      by_cases hx : x ∈ Ioc z thirdPrefixRho <;>
      by_cases hy : y ∈ Ioc z x <;>
      simp_all [F, Set.indicator_apply]
  calc
    (∫⁻ t in actualExtendedThirdOrderedTailRegion h, ENNReal.ofReal (K t)) = ∫⁻ t, F t :=
      (lintegral_indicator (measurableSet_actualExtendedThirdOrderedTailRegion h) _).symm
    _ = ∫⁻ p : ℝ × (Fin 2 → ℝ), F (E.symm p) := (hE.symm.lintegral_comp hF).symm
    _ = ∫⁻ z : ℝ, ∫⁻ v : Fin 2 → ℝ, F (E.symm (z, v)) :=
      lintegral_prod _ (hF.comp E.symm.measurable).aemeasurable
    _ = ∫⁻ z : ℝ, ∫⁻ x : ℝ, ∫⁻ y : ℝ, F ![x, y, z] := by
      apply lintegral_congr
      intro z
      have hs : Measurable (fun v : Fin 2 → ℝ => F (E.symm (z, v))) :=
        hF.comp (E.symm.measurable.comp (measurable_const.prodMk measurable_id))
      calc
        _ = ∫⁻ p : ℝ × ℝ, F (E.symm (z, E₂.symm p)) :=
          (hE₂.symm.lintegral_comp hs).symm
        _ = ∫⁻ x : ℝ, ∫⁻ y : ℝ, F (E.symm (z, E₂.symm (x, y))) :=
          lintegral_prod _ (hs.comp E₂.symm.measurable).aemeasurable
        _ = _ := by simp only [E, E₂, finite_insert_last_fin3]
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Ioc 0 h
      · rw [indicator_of_mem hz]
        calc
          _ = ∫⁻ x : ℝ, (Ioc z thirdPrefixRho).indicator
              (fun x => ∫⁻ y in Ioc z x,
                ENNReal.ofReal (K ![x, y, z])) x := by
            apply lintegral_congr
            intro x
            by_cases hx : x ∈ Ioc z thirdPrefixRho
            · rw [indicator_of_mem hx]
              simp_rw [hvec, indicator_of_mem hz, indicator_of_mem hx]
              exact lintegral_indicator measurableSet_Ioc _
            · rw [indicator_of_notMem hx]
              simp_rw [hvec, indicator_of_mem hz, indicator_of_notMem hx]
              exact lintegral_zero
          _ = _ := lintegral_indicator measurableSet_Ioc _
      · rw [indicator_of_notMem hz]
        simp_rw [hvec, indicator_of_notMem hz]
        simp only [lintegral_zero]


theorem physical_tail {e h : ℝ} (he0 : 0≤e) (he : e≤1/384)
    (hs : h≤thirdPrefixTailMargin/4) (w : ℝ) (m : ℕ) :
    (∫⁻ t in actualExtendedThirdOrderedTailRegion h,ENNReal.ofReal (K e w m t))=tail e w m h := by
  rw [nested h _ (measurable_kernel e w m)]
  unfold tail thirdPrefixTailMass
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro z hz
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro x hx
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro y hy
  let lam := levelAt e w m ![x,y,z]
  have hh := residual he0 he w m (t:=![x,y,z]) ⟨hz.1.le,hy.1.le,hy.2⟩ hx.2
  change thirdPrefixTailMargin≤lam-x-y ∧ lam≤thirdPrefixTheta-2*e at hh
  have hc := thirdPrefixTail_ownCube_lt hs hz.1 hz.2 hh.1
  have hl := thirdPrefixTail_argument_ge_three (by norm_num [thirdPrefixTailMargin]) hs hz.1 hz.2 hh.1
  have hl' := div_le_div_of_nonneg_right (by linarith only [hh.2] : lam-x-y-z≤thirdPrefixTheta-2*e-x-y-z) hz.1.le
  change ENNReal.ofReal (actualExtendedThirdCapKernel e lam x y z)=
    ENNReal.ofReal (if x+y+3*z<thirdPrefixTheta-2*e then thirdPrefixCorrectionKernel (thirdPrefixTheta-2*e) lam x y z else 0)
  rw [if_pos (hc.trans_le hh.2)]
  unfold actualExtendedThirdCapKernel thirdPrefixCorrectionKernel
  rw [actualExtendedThirdLowerFactor_of_two_le ((by norm_num : (2:ℝ)≤3).trans (hl.trans hl')),
    actualExtendedThirdLowerFactor_of_two_le ((by norm_num : (2:ℝ)≤3).trans hl)]

end
end ImbalancedChen.P4AOrderedThirdTransportKernel

