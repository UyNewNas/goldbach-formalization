import ImbalancedChen.P4AOriginalHistoricalThirdOccurrence
import ImbalancedChen.P5HistoricalRectangularGammaTransport
import ImbalancedChen.ActualPrimePolyhedralTestFunctions

/-! The ideal cap has a continuous extension on a positive compact box.
The two strict ordering forms retain the actual three-prime ordering.
The restricted integral is bounded by the entire signed third correction
because the ideal correction is nonnegative throughout its original domain. -/
namespace ImbalancedChen.P4AOriginalHistoricalThirdMajorant
noncomputable section
open Set Filter MeasureTheory
open scoped Classical BigOperators Topology
open VariableEnvelope
open HistoricalThirdCoarse
open HistoricalThirdCoarse.P1ActualTuple (gateForms gateBounds gateForms_ne_zero mem_gateRegion)
open P5HistoricalRectangularGammaTransport
abbrev Point := Fin 3 → ℝ
abbrev boxRegion (a : ℝ) := logPrimeBox (fun _ : Fin 3 => a) (fun _ => thirdPrefixRho)
abbrev ordered := primeAffineGateRegion gateForms (gateBounds 2 2)

def envelope (t : Point) : ℝ := min (six (t 0) (t 1) (t 2)) (C (max (t 0) mu))
def safeFactor (a : ℝ) (f : Point → ℝ) (t : Point) : ℝ :=
  4*actualExtendedThirdLowerFactor ((f t-t 0-t 1-t 2)/max a (t 2))/max a (t 2)
def profile (a : ℝ) (t : Point) : ℝ :=
  safeFactor a (fun _ => thirdPrefixTheta) t-safeFactor a envelope t
def testSum (a : ℝ) (N : ℕ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 3 => a) (fun _ => thirdPrefixRho) (ordered.indicator (profile a))
def testIntegral (a : ℝ) : ℝ := ∫ t in boxRegion a ∩ ordered,profile a t*(∏ i,1/t i)

theorem envelope_eq {t : Point} (hz : 0≤t 2) (hzy : t 2≤t 1) (hyx : t 1≤t 0) :
    envelope t=actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  have hc : cap ≤ thirdPrefixTheta := by norm_num [cap,thirdPrefixTheta]
  rw [envelope,actualExtendedThirdIdealCap_eq]
  by_cases h : t 0≤mu
  · rw [if_pos h,original_eq_six ⟨hz,hzy,hyx,h⟩,max_eq_right h]
    have hcm : C mu=cap := by norm_num [C,mu,cap]
    rw [hcm,min_eq_left (six_le_cap _ _ hz),min_eq_right ((six_le_cap _ _ hz).trans hc)]
  · have h' := le_of_not_ge h
    rw [if_neg h,max_eq_left h',← v_eq_C h',min_eq_right (v_le_six _ _ _),
      min_eq_right ((v_le_cap _).trans hc)]

theorem envelope_le (t : Point) : envelope t≤thirdPrefixTheta := by
  have hm := le_max_right (t 0) mu
  have h : C (max (t 0) mu)≤thirdPrefixTheta := by
    dsimp [C,mu,thirdPrefixTheta] at hm ⊢; linarith
  exact (min_le_right _ _).trans h

theorem continuous_profile (a : ℝ) (ha : 0<a) : Continuous (profile a) := by
  have hc : Continuous envelope := by
    unfold envelope six v A C B
    fun_prop
  have hh : Continuous (fun t : Point => max a (t 2)) := by fun_prop
  have hn (t : Point) := (ha.trans_le (le_max_left a (t 2))).ne'
  have hs (f : Point → ℝ) (hf : Continuous f) : Continuous (safeFactor a f) :=
    (continuous_const.mul (continuous_actualExtendedThirdLowerFactor.comp
      ((((hf.sub (continuous_apply 0)).sub (continuous_apply 1)).sub (continuous_apply 2)).div hh hn))).div hh hn
  exact (hs _ continuous_const).sub (hs _ hc)

theorem profile_eq {a : ℝ} (ha : 0<a) {t : Point} (hz : a≤t 2) :
    profile a t=primeTupleMinusProfile thirdPrefixTheta t-primeTupleMinusProfile (envelope t) t := by
  simp only [profile,safeFactor,max_eq_right hz,primeTupleMinusProfile_eq_extendedThirdFactor _ _ (ha.trans_le hz)]

theorem profile_nonneg {a : ℝ} (ha : 0<a) {t : Point} (hz : a≤t 2) : 0≤profile a t := by
  rw [profile_eq ha hz]
  apply sub_nonneg.mpr
  rw [primeTupleMinusProfile_eq_extendedThirdFactor _ _ (ha.trans_le hz),
    primeTupleMinusProfile_eq_extendedThirdFactor _ _ (ha.trans_le hz)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (monotone_actualExtendedThirdLowerFactor
    (div_le_div_of_nonneg_right (by linarith only [envelope_le t]) (ha.trans_le hz).le)) (by norm_num)) (ha.trans_le hz).le

theorem kernel_identity {a : ℝ} (ha : 0<a) {t : Point} (ht : t∈boxRegion a ∩ ordered) :
    profile a t*(∏ i,1/t i)=actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2) := by
  have hb := mem_logPrimeBox.mp ht.1
  have hp (i : Fin 3) := ha.trans_le (hb i).1
  have hh := ((mem_gateRegion 2 2 t).mp ht.2).1
  rw [profile_eq ha (hb 2).1,envelope_eq (hp 2).le (hh.antitone (by decide : (1:Fin 3)≤2))
    (hh.antitone (by decide : (0:Fin 3)≤1)),actualExtendedThirdGatedKernel_zero_buffer_eq_capKernel (hp 2),
    primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hp 2),primeTupleMinusProfile_eq_extendedThirdFactor _ _ (hp 2)]
  simp only [actualExtendedThirdCapKernel,mul_zero,sub_zero,Fin.prod_univ_three]
  field_simp [(hp 0).ne',(hp 1).ne',(hp 2).ne'] <;> ring

theorem test_integral_le {a : ℝ} (ha : 0<a) : testIntegral a≤actualExtendedThirdIdealFunctional := by
  let K := fun t : Point => actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)
  let D := actualExtendedThirdClosedOrderRegion thirdPrefixRho
  have hD := measurableSet_actualExtendedThirdClosedOrderRegion thirdPrefixRho
  have hs : boxRegion a ∩ ordered ⊆ D := by
    intro t ht
    have hb := mem_logPrimeBox.mp ht.1
    have hh := ((mem_gateRegion 2 2 t).mp ht.2).1.antitone
    exact ⟨ha.trans_le (hb 2).1,(hb 2).2.le,hh (by decide),hh (by decide),(hb 0).2.le⟩
  have hnon : 0 ≤ᵐ[volume.restrict D] K := by
    filter_upwards [ae_restrict_mem hD] with t ht
    have h0 := ht.1
    have hx := h0.trans_le (ht.2.2.1.trans ht.2.2.2.1)
    have hy := h0.trans_le ht.2.2.1
    have hcap := min_le_left thirdPrefixTheta
      (if t 0≤mu then original (t 0) (t 1) (t 2) else v (t 0))
    rw [← actualExtendedThirdIdealCap_eq] at hcap
    dsimp only [K]
    rw [actualExtendedThirdGatedKernel_zero_buffer_eq_capKernel h0]
    simp only [actualExtendedThirdCapKernel,mul_zero,sub_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (monotone_actualExtendedThirdLowerFactor
      (div_le_div_of_nonneg_right (by linarith only [hcap]) h0.le)))) (by positivity)
  rw [actualExtendedThirdIdealFunctional_eq_gated]
  calc
    _ = ∫ t in boxRegion a ∩ ordered,K t := by
      apply setIntegral_congr_fun ((measurableSet_logPrimeBox _ _).inter (measurableSet_primeAffineGateRegion _ _))
      exact fun t ht => kernel_identity ha ht
    _ ≤ _ := setIntegral_mono_set (integrableOn_actualExtendedThirdGatedKernel_full
      (by norm_num : (0:ℝ)≤0) (by norm_num)) hnon (Eventually.of_forall hs)

theorem prime_limit {a : ℝ} (ha : 0<a) (har : a<thirdPrefixRho) :
    Tendsto (testSum a) atTop (𝓝 (testIntegral a)) :=
  tendsto_actualPrimeBoxTestSum_cube_affineGates ha har gateForms (gateBounds 2 2)
    gateForms_ne_zero (profile a) (continuous_profile a ha).continuousOn

/-- All three dispatch regions of the source Gamma bound. In the
transition x≤mu the missing envelope can exceed v(x) only by
cap−A(x), controlled by the actual upper endpoint of the box. -/
theorem cell_error {m : ℕ} {j : Cell m} {e chi : ℝ} (he : 0≤e) (hc : 0≤chi)
    (hf : e+7*chi≤3/256) (hj : j∈cells e chi m) {t : Point}
    (ht : t∈logPrimeMeshCell 0 (19/96) m j) :
    |levelExponent e (box m j)-envelope t|≤4*e+6*chi := by
  let b := box m j
  obtain ⟨hw,hz0,hzy,hyx,hstop,hwidth⟩ := (mem_cells e chi m j).mp hj
  have hh := inBox_of_cell ht
  have hz : 0≤t 2 := (show (0:ℝ)≤(b.lz:ℝ) by exact_mod_cast hz0).trans hh.2.2.2.2.1
  have h21 : t 2≤t 1 := hh.2.2.2.2.2.trans ((show (b.uz:ℝ)≤b.ly by exact_mod_cast hzy).trans hh.2.2.1)
  have h10 : t 1≤t 0 := hh.2.2.2.1.trans ((show (b.uy:ℝ)≤b.lx by exact_mod_cast hyx).trans hh.1)
  have htarget := envelope_eq hz h21 h10
  have hbase := qVLo_le_v hh.1 hh.2.1
  have hdiff := rationalInterval_v_error hh.1 hh.2.1
  have hw' := (coordinate_widths b chi hwidth).1
  have hcap := six_le_cap (t 0) (t 1) hz
  have htheta : cap≤thirdPrefixTheta := by norm_num [cap,thirdPrefixTheta]
  dsimp only [levelExponent,gamma]
  rw [htarget,actualExtendedThirdIdealCap_eq]
  by_cases hfull : (b.ux:ℝ) ≤ mu-4*e
  · have hx : t 0≤mu := by linarith only [hfull,hh.2.1,he]
    have ho : Ordered (t 0) (t 1) (t 2) := ⟨hz,h21,h10,hx⟩
    rw [if_pos hfull,if_pos hx,original_eq_six ho,min_eq_right (hcap.trans htheta)]
    obtain ⟨h₁,h₂⟩ := fullGamma_error e chi b hc hwidth hh ho hf
    apply abs_le.mpr
    constructor <;> linarith
  · rw [if_neg hfull]
    by_cases hx : t 0≤mu
    · rw [if_pos hx,original_eq_six ⟨hz,h21,h10,hx⟩,min_eq_right (hcap.trans htheta)]
      have hv := v_le_six (t 0) (t 1) (t 2)
      have hcap' : cap-A (t 0)≤2*e+chi/2 := by
        dsimp [cap,A,mu] at *; linarith only [not_le.mp hfull,hw',hh.1]
      rw [v_eq_A hx] at hbase hdiff hv
      apply abs_le.mpr
      constructor <;> linarith only [hbase,hdiff,hv,hcap',hcap,hw',he,hc]
    · rw [if_neg hx,min_eq_right ((v_le_cap _).trans htheta)]
      apply abs_le.mpr
      constructor <;> linarith only [hbase,hdiff,hw',he,hc]

end
end ImbalancedChen.P4AOriginalHistoricalThirdMajorant
