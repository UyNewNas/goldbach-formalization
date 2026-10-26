import ImbalancedChen.P2EnhancedSeedD5PlusGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual D5+ integral: integrability, genuine two-coordinate Fubini,
the real inner logarithm, and the three rational affine outer pieces.
The closed support wall is removed only inside a Lebesgue v-integral by
singleton nullity. No arithmetic boundary is declared empty. No numerical
certificate or final seed/feedback estimate is a premise.
-/

namespace ImbalancedChen.P2EnhancedSeedD5PlusLogFubini

noncomputable section

open Set MeasureTheory Filter Classical
open scoped Interval
open P2EnhancedSeedSingletonPrimitive (a0)
open P2EnhancedSeedPairD6Primitive (pairKernel pair_inner_log_integral)
open P2EnhancedSeedD5PlusGeometry
open P5OriginalActionMassBound (Point)

def logSlice (u l r : ℝ) : ℝ := Real.log (r*(1-u-l)/(l*(1-u-r)))/(u*(1-u))
def outerSlice (u : ℝ) : ℝ := logSlice u (lower u) (upper u)

theorem continuousOn_pairKernel : ContinuousOn pairKernel closedRectangle := by
  apply continuousOn_const.div
  · fun_prop
  · intro x hx
    have h := closed_geometry hx
    exact (mul_pos (mul_pos h.1 h.2.1) h.2.2).ne'

theorem integrableOn_pairKernel : IntegrableOn pairKernel supportedD5 :=
  (continuousOn_pairKernel.integrableOn_compact isCompact_Icc).mono_set
    (fun x hx => D5plus_subset_closed hx.1)

/-- Seed support is applied to the original D5+ integrand before Fubini. -/
theorem integral_feedback_support (J : ℝ) :
    (∫ x in D5plus,feedback J x)=J*(∫ x in supportedD5,pairKernel x) := by
  have hset : D5plus ∩ supportedD5=supportedD5 := by
    ext x
    exact ⟨fun h => h.2,fun h => ⟨h.1,h⟩⟩
  calc
    _ = ∫ x in D5plus,supportedD5.indicator (fun x => J*pairKernel x) x := by
      apply setIntegral_congr_fun measurableSet_D5plus
      intro x hx
      exact feedback_support J hx
    _ = ∫ x in D5plus ∩ supportedD5,J*pairKernel x :=
      setIntegral_indicator measurableSet_supportedD5
    _ = _ := by rw [hset,integral_const_mul]

/-- The exact affine support boundary costs a singleton in each real
vertical slice. This is not a claim about arithmetic endpoint counts. -/
theorem inner_indicator_slice (u : ℝ) :
    (∫ v : ℝ,supportedD5.indicator pairKernel (![u,v] : Point))=
      (Ioo a0 top).indicator
        (fun u => ∫ v in Ioo (lower u) (upper u),pairKernel (![u,v] : Point)) u := by
  by_cases hu : u ∈ Ioo a0 top
  · rw [indicator_of_mem hu]
    have hne : ∀ᵐ v : ℝ ∂volume,v≠supportSum-u := by rw [ae_iff]; simp
    have heq : (fun v : ℝ => supportedD5.indicator pairKernel (![u,v] : Point))=ᵐ[volume]
        (Ioo (lower u) (upper u)).indicator (fun v => pairKernel (![u,v] : Point)) := by
      filter_upwards [hne] with v hv
      simp only [Set.indicator_apply,slice_dictionary hu hv]
    rw [integral_congr_ae heq,integral_indicator measurableSet_Ioo]
  · rw [indicator_of_notMem hu]
    have hz (v : ℝ) : supportedD5.indicator pairKernel (![u,v] : Point)=0 := by
      apply indicator_of_notMem
      intro hx
      have hh := supportedD5_u hx
      exact hu (by simpa only [Matrix.cons_val_zero] using hh)
    simp_rw [hz]
    exact integral_zero

/-- Actual finite-dimensional Lebesgue Fubini, justified by compact
integrability of the true kernel on the supported original domain. -/
theorem integral_supported_nested :
    (∫ x in supportedD5,pairKernel x)=
      ∫ u in Ioo a0 top,∫ v in Ioo (lower u) (upper u),pairKernel (![u,v] : Point) := by
  let F := supportedD5.indicator pairKernel
  have hF : Integrable F := integrableOn_pairKernel.integrable_indicator measurableSet_supportedD5
  have htwo : (∫ x : Point,F x)=∫ u : ℝ,∫ v : ℝ,F ![u,v] := by
    calc
      _ = ∫ u : ℝ,∫ v : ℝ,∫ z : Fin 0 → ℝ,F (Fin.cons u (Fin.cons v z)) := integral_fin_pair F hF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with u
        apply integral_congr_ae
        filter_upwards [] with v
        rw [integral_fin_zero]
        rfl
  calc
    _ = ∫ x : Point,F x := (integral_indicator measurableSet_supportedD5).symm
    _ = ∫ u : ℝ,∫ v : ℝ,F ![u,v] := htwo
    _ = ∫ u : ℝ,(Ioo a0 top).indicator
        (fun u => ∫ v in Ioo (lower u) (upper u),pairKernel (![u,v] : Point)) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact inner_indicator_slice u
    _ = _ := integral_indicator measurableSet_Ioo

theorem inner_log {u : ℝ} (hu : u ∈ Icc a0 top) :
    (∫ v in Ioo (lower u) (upper u),pairKernel (![u,v] : Point))=outerSlice u := by
  have hg := slice_geometry hu
  have hh := pair_inner_log_integral hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  simpa only [pairKernel,Matrix.cons_val_zero,Matrix.cons_val_one,outerSlice,logSlice,
    one_div,div_eq_mul_inv,mul_comm] using hh

theorem continuousOn_outerSlice : ContinuousOn outerSlice (Icc a0 top) := by
  have hn : ContinuousOn (fun u : ℝ => upper u*(1-u-lower u)) (Icc a0 top) := by
    unfold upper lower
    fun_prop
  have hd : ContinuousOn (fun u : ℝ => lower u*(1-u-upper u)) (Icc a0 top) := by
    unfold upper lower
    fun_prop
  have hden (u : ℝ) (hu : u ∈ Icc a0 top) : 0<lower u*(1-u-upper u) := by
    have hg := slice_geometry hu
    exact mul_pos hg.2.1 (by linarith only [hg.2.2.2])
  have hnum (u : ℝ) (hu : u ∈ Icc a0 top) : 0<upper u*(1-u-lower u) := by
    have hg := slice_geometry hu
    exact mul_pos (hg.2.1.trans_le hg.2.2.1) (by linarith only [hg.2.2.1,hg.2.2.2])
  have hratio := hn.div hd (fun u hu => (hden u hu).ne')
  have hlog := hratio.log (fun u hu => (div_pos (hnum u hu) (hden u hu)).ne')
  have hout := hlog.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    (fun u hu => by
      have hg := slice_geometry hu
      exact (mul_pos hg.1 (by have ht:=hu.2; dsimp [top] at ht; linarith only [ht] : 0<1-u)).ne')
  exact hout

theorem intervalIntegrable_outerSlice {l r : ℝ}
    (hl : a0≤l) (hlr : l≤r) (hr : r≤top) : IntervalIntegrable outerSlice volume l r :=
  (continuousOn_outerSlice.mono
    (fun u hu => ⟨hl.trans hu.1,hu.2.trans hr⟩)).intervalIntegrable_of_Icc hlr

theorem feedback_outer_log (J : ℝ) :
    (∫ x in D5plus,feedback J x)=J*(∫ u in Ioo a0 top,outerSlice u) := by
  rw [integral_feedback_support,integral_supported_nested]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact inner_log ⟨hu.1.le,hu.2.le⟩

/-- The exact three D5+ pieces in the original seven-piece lambda/50
calculation. The endpoints and affine boundaries are rational and literal.
No numerical value, enhanced H/h bound, or coefficient inequality enters. -/
theorem feedback_three_affine_logs (J : ℝ) :
    (∫ x in D5plus,feedback J x)=J*(
      (∫ u in a0..cutOne,logSlice u (supportSum-u) cap)+
      (∫ u in cutOne..cutTwo,logSlice u u cap)+
      (∫ u in cutTwo..top,logSlice u u (1-2*u))) := by
  have ho := three_cut_order
  have h01 := intervalIntegrable_outerSlice (le_refl a0) ho.1.le
    (ho.2.1.le.trans ho.2.2.le)
  have h12 := intervalIntegrable_outerSlice ho.1.le ho.2.1.le ho.2.2.le
  have h02 := intervalIntegrable_outerSlice (le_refl a0) (ho.1.le.trans ho.2.1.le) ho.2.2.le
  have h23 := intervalIntegrable_outerSlice (ho.1.le.trans ho.2.1.le) ho.2.2.le (le_refl top)
  have hfirst : (∫ u in a0..cutOne,outerSlice u)=
      ∫ u in a0..cutOne,logSlice u (supportSum-u) cap := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ho.1.le] at hu
    have hh := first_affine hu
    rw [outerSlice,hh.1,hh.2]
  have hsecond : (∫ u in cutOne..cutTwo,outerSlice u)=
      ∫ u in cutOne..cutTwo,logSlice u u cap := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ho.2.1.le] at hu
    have hh := second_affine hu
    rw [outerSlice,hh.1,hh.2]
  have hthird : (∫ u in cutTwo..top,outerSlice u)=
      ∫ u in cutTwo..top,logSlice u u (1-2*u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ho.2.2.le] at hu
    have hh := third_affine hu
    rw [outerSlice,hh.1,hh.2]
  rw [feedback_outer_log,integral_Ioo_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (ho.1.le.trans (ho.2.1.le.trans ho.2.2.le)),
    ← intervalIntegral.integral_add_adjacent_intervals h02 h23,
    ← intervalIntegral.integral_add_adjacent_intervals h01 h12,hfirst,hsecond,hthird]

end
end ImbalancedChen.P2EnhancedSeedD5PlusLogFubini
