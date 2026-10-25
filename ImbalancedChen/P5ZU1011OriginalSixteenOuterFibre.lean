import ImbalancedChen.P5ZU1011OriginalSixteenReassembly
import ImbalancedChen.FinitePiIntegral

/-!
# The genuine original16 outer-last-pair / inner-first-pair integral

Coordinates are DECREASING: (x,y,z,w)=(p4,p3,p2,p1) in logarithms.
The natural last-pair source (p3,p4) therefore has the swapped real mask
(y,x). Every strict/weak original wall and the full nonlinear16 kernel
remain literal. The fibre cost has NO mask argument: selection is allowed
only after the complete inner pair has been integrated. No moving-mask
limit or arbitrary four-tuple selection is inferred by this Fubini layer.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenOuterFibre

noncomputable section
open Set MeasureTheory Filter
open Classical
open U11Integral U11Canonical

abbrev Outer := ℝ × ℝ
abbrev Inner := Fin 2 → ℝ
abbrev actualMinimum := U1011OriginalSixteenReassembly.actualMinimum

/-- q=(x,y) is the LAST prime pair, reversed from the natural (p3,p4).
r=(z,w) is the FIRST prime pair, also in decreasing order. -/
def join (q : Outer) (r : Inner) : LogFour := Fin.cons q.1 (Fin.cons q.2 r)

def innerDomain (y : ℝ) : Set Inner :=
  {r | (417/5000 : ℝ)≤r 1 ∧ r 1<r 0 ∧ r 0<y}

def outerDomain (mask : Set Outer) : Set Outer :=
  {q | (19/125 : ℝ)≤q.1 ∧ q.1<(59/250 : ℝ) ∧
    (417/5000 : ℝ)<q.2 ∧ q.2<(19/125 : ℝ) ∧ q∉mask}

/-- Original natural last-pair E(p3,p4) becomes E(y,x), not E(x,y). -/
def ascendingMask (E : Set Outer) : Set Outer := Prod.swap ⁻¹' E

theorem mem_ascendingMask (E : Set Outer) (q : Outer) :
    q ∈ ascendingMask E ↔ (q.2,q.1) ∈ E := Iff.rfl

theorem measurableSet_ascendingMask (E : Set Outer) (hE : MeasurableSet E) :
    MeasurableSet (ascendingMask E) := hE.preimage measurable_swap

theorem measurableSet_innerDomain (y : ℝ) : MeasurableSet (innerDomain y) :=
  (measurableSet_le measurable_const (measurable_pi_apply 1)).inter
    ((measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 0)).inter
      (measurableSet_lt (measurable_pi_apply 0) measurable_const))

theorem measurableSet_outerDomain (mask : Set Outer) (hm : MeasurableSet mask) :
    MeasurableSet (outerDomain mask) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_lt measurable_snd measurable_const).inter hm.compl)))

theorem outerDomain_eq_base_diff (mask : Set Outer) :
    outerDomain mask=outerDomain ∅ \ mask := by
  ext q
  simp only [outerDomain,mem_setOf_eq,mem_diff,not_mem_empty,true_and,and_true,and_assoc]

theorem mem_originalDomain_join_iff (mask : Set Outer) (q : Outer) (r : Inner) :
    join q r ∈ originalDomain mask ↔ q ∈ outerDomain mask ∧ r ∈ innerDomain q.2 := by
  change ((417/5000 : ℝ)≤r 1 ∧ r 1<r 0 ∧ r 0<q.2 ∧ q.2<(19/125 : ℝ) ∧
    (19/125 : ℝ)≤q.1 ∧ q.1<(59/250 : ℝ) ∧ q∉mask) ↔
    (((19/125 : ℝ)≤q.1 ∧ q.1<(59/250 : ℝ) ∧ (417/5000 : ℝ)<q.2 ∧
      q.2<(19/125 : ℝ) ∧ q∉mask) ∧
      ((417/5000 : ℝ)≤r 1 ∧ r 1<r 0 ∧ r 0<q.2))
  constructor
  · rintro ⟨ha,hwz,hzy,hy,hx,hxd,hm⟩
    exact ⟨⟨hx,hxd,ha.trans_lt (hwz.trans hzy),hy,hm⟩,ha,hwz,hzy⟩
  · rintro ⟨⟨hx,hxd,hay,hy,hm⟩,ha,hwz,hzy⟩
    exact ⟨ha,hwz,hzy,hy,hx,hxd,hm⟩

theorem outer_coordinates_pos {mask : Set Outer} {q : Outer} (hq : q ∈ outerDomain mask) :
    0<q.1 ∧ 0<q.2 := by
  have hx := hq.1
  have hy := hq.2.2.1
  constructor <;> linarith

def innerIntegrand (q : Outer) (r : Inner) : ℝ := actualMinimum (join q r)/(r 0*r 1)

/-- The TRUE full16 cost integrated over the complete original first pair.
There is no E or four-tuple-dependent keep predicate in this function. -/
def fibreCost (q : Outer) : ℝ := ∫ r in innerDomain q.2, innerIntegrand q r

def outerCost (q : Outer) : ℝ := fibreCost q/(q.1*q.2)

def zeroExtended (mask : Set Outer) (v : LogFour) : ℝ :=
  (originalDomain mask).indicator (fun v => actualMinimum v*harmonicDensity v) v

def jointZeroExtended (mask : Set Outer) (z : Outer × Inner) : ℝ :=
  zeroExtended mask (join z.1 z.2)

theorem harmonicDensity_join (q : Outer) (r : Inner) :
    harmonicDensity (join q r)=(1/(q.1*q.2))*(1/(r 0*r 1)) := by
  simp only [harmonicDensity,join,Fin.cons_zero,Fin.cons_succ,one_div,mul_inv_rev]
  ring

/-- The original mask factors OUTSIDE the complete inner fibre. -/
theorem zeroExtended_join (mask : Set Outer) (q : Outer) (r : Inner) :
    zeroExtended mask (join q r)=
      (outerDomain mask).indicator
        (fun q => (1/(q.1*q.2))*(innerDomain q.2).indicator (innerIntegrand q) r) q := by
  by_cases hq : q ∈ outerDomain mask
  · by_cases hr : r ∈ innerDomain q.2
    · have hv := (mem_originalDomain_join_iff mask q r).2 ⟨hq,hr⟩
      simp only [zeroExtended,indicator_of_mem hv,indicator_of_mem hq,indicator_of_mem hr]
      rw [harmonicDensity_join]
      unfold innerIntegrand
      ring
    · have hv : join q r ∉ originalDomain mask :=
        fun h => hr ((mem_originalDomain_join_iff mask q r).1 h).2
      simp only [zeroExtended,indicator_of_notMem hv,indicator_of_mem hq,indicator_of_notMem hr,mul_zero]
  · have hv : join q r ∉ originalDomain mask :=
      fun h => hq ((mem_originalDomain_join_iff mask q r).1 h).1
    simp only [zeroExtended,indicator_of_notMem hv,indicator_of_notMem hq]

/-- The only integrability input is already PROVED for the actual full16
bank. No hIntegrable, hFubini or mean estimate is requested from a caller. -/
theorem integrable_zeroExtended (mask : Set Outer) (hm : MeasurableSet mask) :
    Integrable (zeroExtended mask) :=
  (integrable_indicator_iff (measurableSet_originalDomain mask hm)).2
    (U1011OriginalSixteenReassembly.integrableOn_weighted_actualMinimum mask hm)

/-- Exact measure-preserving regrouping, without a coordinate permutation.
Its inverse is explicitly join((x,y),(z,w))=(x,y,z,w). -/
def splitFirst : LogFour ≃ᵐ (ℝ × (Fin 3 → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0

def splitSecond : (Fin 3 → ℝ) ≃ᵐ (ℝ × Inner) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0

def split : LogFour ≃ᵐ (Outer × Inner) :=
  (splitFirst.trans ((MeasurableEquiv.refl ℝ).prodCongr splitSecond)).trans
    MeasurableEquiv.prodAssoc.symm

theorem split_symm_apply (z : Outer × Inner) : split.symm z=join z.1 z.2 := by
  simp [split,splitFirst,splitSecond,join,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

theorem split_measurePreserving : MeasurePreserving split := by
  have hfirst : MeasurePreserving splitFirst := volume_preserving_piFinSuccAbove _ 0
  have hsecond : MeasurePreserving splitSecond := volume_preserving_piFinSuccAbove _ 0
  have hprod : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr splitSecond) :=
    (MeasurePreserving.id volume).prod hsecond
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : Outer × Inner ≃ᵐ (ℝ × (ℝ × Inner))) :=
    volume_preserving_prodAssoc
  exact hassoc.symm.comp (hprod.comp hfirst)

theorem integrable_jointZeroExtended (mask : Set Outer) (hm : MeasurableSet mask) :
    Integrable (jointZeroExtended mask) := by
  have h := split_measurePreserving.symm.integrable_comp_of_integrable (integrable_zeroExtended mask hm)
  simpa only [Function.comp_def,split_symm_apply,jointZeroExtended] using h

/-- Pointwise fibre integration. Constant extraction and indicator Fubini
are exact even at an exterior pair where the source fibre is empty. -/
theorem integral_joint_section (mask : Set Outer) (q : Outer) :
    (∫ r : Inner, jointZeroExtended mask (q,r))=(outerDomain mask).indicator outerCost q := by
  simp only [jointZeroExtended,zeroExtended_join]
  by_cases hq : q ∈ outerDomain mask
  · simp only [indicator_of_mem hq]
    rw [integral_const_mul,integral_indicator (measurableSet_innerDomain q.2)]
    unfold outerCost fibreCost
    ring
  · simp only [indicator_of_notMem hq,integral_zero]

/-- Actual weighted inner integrability holds for almost every retained
last pair, derived from the full16 majorant and genuine product Fubini. -/
theorem integrableOn_inner_fibre_ae (mask : Set Outer) (hm : MeasurableSet mask) :
    ∀ᵐ q : Outer, q ∈ outerDomain mask → IntegrableOn (innerIntegrand q) (innerDomain q.2) := by
  filter_upwards [(integrable_jointZeroExtended mask hm).prod_right_ae] with q hi
  intro hq
  have hpos := outer_coordinates_pos hq
  have hne : q.1*q.2≠0 := (mul_pos hpos.1 hpos.2).ne'
  have hscaled := hi.const_mul (q.1*q.2)
  change Integrable (fun r : Inner => (q.1*q.2)*zeroExtended mask (join q r)) at hscaled
  have heq : (fun r : Inner => (q.1*q.2)*zeroExtended mask (join q r))=
      (innerDomain q.2).indicator (innerIntegrand q) := by
    funext r
    rw [zeroExtended_join,indicator_of_mem hq]
    field_simp [hpos.1.ne',hpos.2.ne']
  rw [heq] at hscaled
  exact (integrable_indicator_iff (measurableSet_innerDomain q.2)).1 hscaled

/-- The complete outer weighted fibre cost is integrable on every fixed
measurable retained last-pair domain, with no premise on slice estimates. -/
theorem integrableOn_outerCost (mask : Set Outer) (hm : MeasurableSet mask) :
    IntegrableOn outerCost (outerDomain mask) := by
  have hi := (integrable_jointZeroExtended mask hm).integral_prod_left
  have heq : (fun q : Outer => ∫ r : Inner, jointZeroExtended mask (q,r))=
      (outerDomain mask).indicator outerCost := by
    funext q
    exact integral_joint_section mask q
  rw [heq] at hi
  exact (integrable_indicator_iff (measurableSet_outerDomain mask hm)).1 hi

/-- TRUE original16 weighted Fubini, with all original half-open prime
walls and every full/selected-square policy test inside the same kernel. -/
theorem integral_original_eq_outer_fibre (mask : Set Outer) (hm : MeasurableSet mask) :
    (∫ v in originalDomain mask, actualMinimum v*harmonicDensity v)=
      ∫ q in outerDomain mask, fibreCost q/(q.1*q.2) := by
  calc
    _ = ∫ v, zeroExtended mask v := (integral_indicator (measurableSet_originalDomain mask hm)).symm
    _ = ∫ z : Outer × Inner, jointZeroExtended mask z := by
      have h := (split_measurePreserving.symm.integral_comp' (zeroExtended mask)).symm
      simpa only [Function.comp_def,split_symm_apply,jointZeroExtended] using h
    _ = ∫ q : Outer, ∫ r : Inner, jointZeroExtended mask (q,r) :=
      integral_prod _ (integrable_jointZeroExtended mask hm)
    _ = ∫ q : Outer, (outerDomain mask).indicator outerCost q := by
      apply integral_congr_ae
      exact Eventually.of_forall (integral_joint_section mask)
    _ = _ := integral_indicator (measurableSet_outerDomain mask hm)

/-- Fixed ascending E is applied to the original last pair (y,x). This
identity makes no assertion about a varying E(N) or a four-tuple selector. -/
theorem integral_original_ascending_mask_eq_outer_fibre
    (E : Set Outer) (hE : MeasurableSet E) :
    (∫ v in originalDomain (ascendingMask E), actualMinimum v*harmonicDensity v)=
      ∫ q in outerDomain (ascendingMask E), fibreCost q/(q.1*q.2) :=
  integral_original_eq_outer_fibre (ascendingMask E) (measurableSet_ascendingMask E hE)

theorem fibreCost_nonneg {q : Outer} (hq : q ∈ outerDomain ∅) : 0≤fibreCost q := by
  apply setIntegral_nonneg (measurableSet_innerDomain q.2)
  intro r hr
  have hv := (mem_originalDomain_join_iff ∅ q r).2 ⟨hq,hr⟩
  have hm := (U1011OriginalSixteenReassembly.actualMinimum_bounds ∅ (join q r) hv).1
  have hw : 0<r 1 := by have h := hr.1; linarith
  have hz : 0<r 0 := hw.trans hr.2.1
  exact div_nonneg hm (mul_pos hz hw).le

theorem outerCost_nonneg {q : Outer} (hq : q ∈ outerDomain ∅) : 0≤outerCost q :=
  div_nonneg (fibreCost_nonneg hq) (mul_pos (outer_coordinates_pos hq).1 (outer_coordinates_pos hq).2).le

/-- No first-pair source is present at or below the original lower wall. -/
theorem fibreCost_eq_zero_of_second_le {q : Outer} (hy : q.2≤(417/5000 : ℝ)) : fibreCost q=0 := by
  have hempty : innerDomain q.2=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have ha := hr.1
    have hwz := hr.2.1
    have hzy := hr.2.2
    linarith
  simp [fibreCost,hempty]

end
end ImbalancedChen.P5Z.U1011OriginalSixteenOuterFibre
