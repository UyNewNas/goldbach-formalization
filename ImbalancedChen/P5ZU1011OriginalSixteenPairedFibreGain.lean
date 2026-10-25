import ImbalancedChen.P5ZU1011OriginalSixteenPointwiseFibre
import ImbalancedChen.P5U6RetainedAdoptedIntegral

/-!
# Actual original16 / corrected Runbo U6 same-outer-mask signed gain

U6 coordinates are (u,t)=(y,x), opposite the decreasing original16 outer
coordinates (x,y)=(p4,p3). The adopted U6 correction keeps R=1/2-u-t in
its WHOLE denominator. Both original signs occur exactly once: +U6-U11.
Only a fixed measurable last-pair mask is used; no four-tuple selection,
optimal replacement mask, arithmetic mean or moving-mask limit is asserted.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPairedFibreGain

noncomputable section
open Set MeasureTheory Filter
open Classical
open U11Integral U11Canonical U1011OriginalSixteenOuterFibre
open Part5OriginalUpsilon5CausalDictionary
open P5U6AdoptedH248BindingSourceOnly P5U6RetainedAdoptedIntegralSourceOnly

abbrev U6Point := Fin 2 → ℝ

def pairRectangle : Set Outer :=
  {q | (19/125 : ℝ)≤q.1 ∧ q.1<(59/250 : ℝ) ∧
    (417/5000 : ℝ)≤q.2 ∧ q.2<(19/125 : ℝ)}

def transpose (q : Outer) : U6Point := ![q.2,q.1]

def transposeEquiv : Outer ≃ᵐ U6Point :=
  MeasurableEquiv.prodComm.trans MeasurableEquiv.finTwoArrow.symm

theorem transposeEquiv_apply (q : Outer) : transposeEquiv q=transpose q := by
  ext i
  fin_cases i <;> rfl

theorem transpose_measurePreserving : MeasurePreserving transposeEquiv :=
  (volume_preserving_finTwoArrow ℝ).symm.comp measurePreserving_swap

theorem measurableSet_pairRectangle : MeasurableSet pairRectangle :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)))

theorem mem_u6_rectangle_transpose (q : Outer) :
    transpose q ∈ currentChenUpsilon6LogRectangle ↔ q ∈ pairRectangle := by
  rw [mem_currentChenUpsilon6LogRectangle]
  simp only [transpose,Matrix.cons_val_zero,Matrix.cons_val_one,pairRectangle,mem_setOf_eq]
  tauto

theorem mem_u6_domain_transpose (q : Outer) :
    transpose q ∈ currentChenUpsilon6LogDomain 0 ↔
      q ∈ pairRectangle ∧ q.1+q.2≤(833/2500 : ℝ) := by
  simp only [currentChenUpsilon6LogDomain,mem_inter_iff,mem_setOf_eq,sub_zero,
    mem_u6_rectangle_transpose,transpose,Matrix.cons_val_zero,Matrix.cons_val_one,add_comm]

/-- True original residual after the coordinate transpose. -/
def runboResidual (q : Outer) : ℝ := (1/2:ℝ)-q.2-q.1

def runboProfile (q : Outer) : ℝ := runboResidual q/(417/5000 : ℝ)

def runboKernel (q : Outer) : ℝ :=
  4*(Real.log (runboProfile q-1)+adoptedH248Floor (runboProfile q))/
    (runboResidual q*q.2*q.1)

/-- This is the adopted corrected kernel, not an auxiliary a-denominator
model. The complete R*u*t denominator is preserved pointwise. -/
theorem adoptedKernel_transpose_eq_runbo (q : Outer) : adoptedKernel (transpose q)=runboKernel q := by
  rw [adoptedKernel_eq_original_log]
  rfl

/-- The TRUE U6 density includes its original corrected product gate. -/
def u6Density (q : Outer) : ℝ :=
  (currentChenUpsilon6LogDomain 0).indicator adoptedKernel (transpose q)

theorem u6Density_eq_product_indicator {q : Outer} (hq : q ∈ pairRectangle) :
    u6Density q=if q.1+q.2≤(833/2500 : ℝ) then runboKernel q else 0 := by
  by_cases hg : q.1+q.2≤(833/2500 : ℝ)
  · have hd := (mem_u6_domain_transpose q).2 ⟨hq,hg⟩
    simp only [u6Density,indicator_of_mem hd,if_pos hg]
    exact adoptedKernel_transpose_eq_runbo q
  · have hd : transpose q ∉ currentChenUpsilon6LogDomain 0 :=
      fun h => hg ((mem_u6_domain_transpose q).1 h).2
    simp only [u6Density,indicator_of_notMem hd,if_neg hg]

theorem u6Density_eq_zero_off_rectangle {q : Outer} (hq : q ∉ pairRectangle) : u6Density q=0 := by
  have hd : transpose q ∉ currentChenUpsilon6LogDomain 0 :=
    fun h => hq ((mem_u6_domain_transpose q).1 h).1
  exact indicator_of_notMem hd _

theorem integrable_u6Density : Integrable u6Density := by
  have hi : Integrable ((currentChenUpsilon6LogDomain 0).indicator adoptedKernel) :=
    (integrableOn_adoptedEnhancedKernel (eta := 0) (by norm_num)).integrable_indicator
      (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain 0)
  have h := transpose_measurePreserving.integrable_comp_of_integrable hi
  simpa only [Function.comp_def,transposeEquiv_apply,u6Density] using h

/-- Real endpoint payment only. The arithmetic lower-band prime endpoint
is NOT declared empty or removed by this null-set statement. -/
theorem lowerBand_volume_zero : volume {q : Outer | q.2=(417/5000 : ℝ)}=0 := by
  have heq : {q : Outer | q.2=(417/5000 : ℝ)}=Set.univ ×ˢ {(417/5000 : ℝ)} := by
    ext q
    simp
  rw [heq]
  change ((volume : Measure ℝ).prod volume) (Set.univ ×ˢ {(417/5000 : ℝ)})=0
  rw [Measure.prod_prod]
  simp

theorem ae_second_ne_lowerBand : ∀ᵐ q : Outer, q.2≠(417/5000 : ℝ) := by
  rw [ae_iff]
  simpa only [not_not] using lowerBand_volume_zero

/-- The common rectangle has weak y>=a; original U11 has y>a. Their
retained versions agree a.e. for the SAME outer mask, with no crop change. -/
theorem retained_domain_ae_eq (M : Set Outer) :
    pairRectangle \ M =ᵐ[volume] outerDomain M := by
  filter_upwards [ae_second_ne_lowerBand] with q hne
  apply propext
  constructor
  · rintro ⟨⟨hx,hxd,hy,hyh⟩,hm⟩
    exact ⟨hx,hxd,(lt_or_eq_of_le hy).resolve_right hne.symm,hyh,hm⟩
  · rintro ⟨hx,hxd,hy,hyh,hm⟩
    exact ⟨⟨hx,hxd,hy.le,hyh⟩,hm⟩

theorem lowerBand_integral_zero (f : Outer → ℝ) :
    (∫ q in pairRectangle ∩ {q | q.2=(417/5000 : ℝ)},f q)=0 := by
  have hz : volume (pairRectangle ∩ {q : Outer | q.2=(417/5000 : ℝ)})=0 :=
    measure_mono_null inter_subset_right lowerBand_volume_zero
  rw [Measure.restrict_eq_zero.mpr hz,integral_zero_measure]

theorem integral_retained_domain_eq (M : Set Outer) (f : Outer → ℝ) :
    (∫ q in pairRectangle \ M,f q)=∫ q in outerDomain M,f q :=
  setIntegral_congr_set (retained_domain_ae_eq M)

theorem integrableOn_u11Density_rectangle : IntegrableOn outerCost pairRectangle := by
  have h := integrableOn_outerCost ∅ measurableSet_empty
  apply h.congr_set_ae
  simpa only [diff_empty] using retained_domain_ae_eq ∅

/-- Actual signed gain from deleting ONE common outer-pair mask. -/
def signedPairGainDensity (q : Outer) : ℝ := outerCost q-u6Density q

theorem signedPairGainDensity_eq_original_formula {q : Outer} (hq : q ∈ pairRectangle) :
    signedPairGainDensity q=fibreCost q/(q.1*q.2)-
      (if q.1+q.2≤(833/2500 : ℝ) then
        4*(Real.log (runboProfile q-1)+adoptedH248Floor (runboProfile q))/
          (runboResidual q*q.2*q.1) else 0) := by
  rw [signedPairGainDensity,outerCost,u6Density_eq_product_indicator hq]
  rfl

theorem integrableOn_signedPairGainDensity : IntegrableOn signedPairGainDensity pairRectangle :=
  integrableOn_u11Density_rectangle.sub integrable_u6Density.integrableOn

def retainedU6 (M : Set Outer) : ℝ := ∫ q in pairRectangle \ M,u6Density q

def retainedU11 (M : Set Outer) : ℝ := ∫ q in pairRectangle \ M,outerCost q

def pairedRetained (M : Set Outer) : ℝ := retainedU6 M-retainedU11 M

/-- Same original signs exactly once. This is an equality of actual
estimator integrals, not a selected-count or mean hypothesis. -/
theorem pairedRetained_change_eq_deleted_gain (M : Set Outer) (hM : MeasurableSet M) :
    pairedRetained M-pairedRetained ∅=
      ∫ q in pairRectangle ∩ M,signedPairGainDensity q := by
  have hi6 : IntegrableOn u6Density pairRectangle := integrable_u6Density.integrableOn
  have h6 := integral_inter_add_sdiff hM hi6
  have h11 := integral_inter_add_sdiff hM integrableOn_u11Density_rectangle
  have hgain : (∫ q in pairRectangle ∩ M,signedPairGainDensity q)=
      (∫ q in pairRectangle ∩ M,outerCost q)-(∫ q in pairRectangle ∩ M,u6Density q) :=
    integral_sub (integrableOn_u11Density_rectangle.mono_set inter_subset_left)
      (hi6.mono_set inter_subset_left)
  unfold pairedRetained retainedU6 retainedU11
  simp only [diff_empty]
  linarith

/-- The negative original full16 integral is genuinely the same retained
outer cost on the common rectangle, after the proved real endpoint payment. -/
theorem retainedU11_eq_original_integral (M : Set Outer) (hM : MeasurableSet M) :
    retainedU11 M=(∫ v in originalDomain M,actualMinimum v*harmonicDensity v) := by
  unfold retainedU11
  rw [integral_retained_domain_eq M outerCost]
  exact (integral_original_eq_outer_fibre M hM).symm

/-- Positive original U6 uses E on native ascending coordinates (u,t),
so its SAME outer mask is ascendingMask E and reads E(y,x). -/
theorem retainedU6_eq_original_adopted (E : Set Outer) (hE : MeasurableSet E) :
    retainedU6 (ascendingMask E)=
      retainedEstimatorIntegral (fun p : U6Point => (p 0,p 1) ∈ E) 0 := by
  let D := currentChenUpsilon6LogDomain 0 ∩ {p : U6Point | (p 0,p 1) ∉ E}
  have hpoint : MeasurableSet {p : U6Point | (p 0,p 1) ∈ E} :=
    hE.preimage ((measurable_pi_apply 0).prod_mk (measurable_pi_apply 1))
  have hD : MeasurableSet D :=
    (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain 0).inter hpoint.compl
  have heq (q : Outer) : D.indicator adoptedKernel (transpose q)=
      (pairRectangle \ ascendingMask E).indicator u6Density q := by
    by_cases hq : q ∈ pairRectangle \ ascendingMask E
    · have hn : (transpose q 0,transpose q 1) ∉ E := by
        simpa only [transpose,Matrix.cons_val_zero,Matrix.cons_val_one,ascendingMask,mem_preimage,
          Prod.swap_prod_mk] using hq.2
      by_cases hd : transpose q ∈ currentChenUpsilon6LogDomain 0 <;>
        simp [D,u6Density,hq,hd,hn]
    · have hn : transpose q ∉ D := by
        intro hp
        have hr := ((mem_u6_domain_transpose q).1 hp.1).1
        have hm : q ∉ ascendingMask E := by
          simpa only [transpose,Matrix.cons_val_zero,Matrix.cons_val_one,ascendingMask,mem_preimage,
            Prod.swap_prod_mk] using hp.2
        exact hq ⟨hr,hm⟩
      simp only [indicator_of_notMem hn,indicator_of_notMem hq]
  symm
  calc
    _ = ∫ p : U6Point,D.indicator adoptedKernel p := (integral_indicator hD).symm
    _ = ∫ q : Outer,D.indicator adoptedKernel (transpose q) := by
      have h := (transpose_measurePreserving.integral_comp' (D.indicator adoptedKernel)).symm
      simpa only [transposeEquiv_apply] using h
    _ = ∫ q : Outer,(pairRectangle \ ascendingMask E).indicator u6Density q := by
      apply integral_congr_ae
      exact Eventually.of_forall heq
    _ = _ := integral_indicator (measurableSet_pairRectangle.diff (measurableSet_ascendingMask E hE))

/-- Native ascending original E appears once in BOTH signs. No term is
removed as an arithmetic endpoint and no independently chosen E is allowed. -/
theorem original_adopted_pair_change_eq_deleted_gain (E : Set Outer) (hE : MeasurableSet E) :
    (retainedEstimatorIntegral (fun p : U6Point => (p 0,p 1) ∈ E) 0 -
      (∫ v in originalDomain (ascendingMask E),actualMinimum v*harmonicDensity v)) -
    (retainedEstimatorIntegral (fun _ : U6Point => False) 0 -
      (∫ v in originalDomain ∅,actualMinimum v*harmonicDensity v)) =
      ∫ q in pairRectangle ∩ ascendingMask E,signedPairGainDensity q := by
  have h := pairedRetained_change_eq_deleted_gain (ascendingMask E) (measurableSet_ascendingMask E hE)
  unfold pairedRetained at h
  rw [retainedU6_eq_original_adopted E hE,
    retainedU11_eq_original_integral (ascendingMask E) (measurableSet_ascendingMask E hE),
    retainedU11_eq_original_integral ∅ measurableSet_empty] at h
  have hempty : ascendingMask (∅ : Set Outer)=∅ := by ext q; simp [ascendingMask]
  have h6 := retainedU6_eq_original_adopted (∅ : Set Outer) measurableSet_empty
  rw [hempty] at h6
  rw [h6] at h
  simpa only [mem_empty_iff_false] using h

end
end ImbalancedChen.P5Z.U1011OriginalSixteenPairedFibreGain
