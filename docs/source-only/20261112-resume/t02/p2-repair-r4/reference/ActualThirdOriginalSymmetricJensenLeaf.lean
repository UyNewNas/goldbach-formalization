import ImbalancedChen.ActualThirdOriginalBoxMoments
import Mathlib.Tactic.FinCases

/- SOURCEONLY / HOLD_ELABORATION / OPEN30. V3: import shared BoxMoments; unique V2 proof body unchanged. -/


/-!
SOURCEONLY / UNCOMPILED / OPEN30.
The original order is y<=x. We integrate the actual closed reciprocal triangle
by Fubini, rather than assuming x and y independent on that triangle.
-/
namespace ImbalancedChen.OriginalThirdTriangleMomentsSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly

abbrev XY := ℝ × ℝ

def xySquare (a b : ℝ) : Set XY := Icc a b ×ˢ Icc a b
def xyTriangle (a b : ℝ) : Set XY := xySquare a b ∩ {p | p.2≤p.1}
def xyWeight (p : XY) : ℝ := (1/p.1)*(1/p.2)
def triangleMass (a b : ℝ) : ℝ := (Real.log (b/a))^2/2
def triangleProbability (a b : ℝ) : Measure XY :=
  (volume.restrict (xyTriangle a b)).withDensity
    (fun p => ENNReal.ofReal (xyWeight p/triangleMass a b))
def maxMean (a b : ℝ) : ℝ :=
  2*(b*Real.log (b/a)-(b-a))/(Real.log (b/a))^2

theorem measurableSet_xyTriangle (a b : ℝ) : MeasurableSet (xyTriangle a b) :=
  (measurableSet_Icc.prod measurableSet_Icc).inter
    (isClosed_le continuous_snd continuous_fst).measurableSet

private theorem continuousOn_xyWeight (a b : ℝ) (ha : 0<a) :
    ContinuousOn xyWeight (xySquare a b) := by
  exact (continuousOn_const.div continuous_fst.continuousOn
    (fun p hp => (ha.trans_le hp.1.1).ne')).mul
    (continuousOn_const.div continuous_snd.continuousOn
      (fun p hp => (ha.trans_le hp.2.1).ne'))

private theorem xyWeight_nonneg (a b : ℝ) (ha : 0<a) {p : XY}
    (hp : p∈xyTriangle a b) : 0≤xyWeight p := by
  exact mul_nonneg (one_div_pos.mpr (ha.trans_le hp.1.1.1)).le
    (one_div_pos.mpr (ha.trans_le hp.1.2.1)).le

private theorem measurable_xyWeight : Measurable xyWeight :=
  (measurable_const.div measurable_fst).mul (measurable_const.div measurable_snd)

/-- Closed-triangle Fubini. The inner upper endpoint is x, not b. -/
theorem integral_xyTriangle_nested (a b : ℝ) {g : XY → ℝ}
    (hg : ContinuousOn g (xySquare a b)) :
    (∫ p in xyTriangle a b, g p) =
      ∫ x in Icc a b, ∫ y in Icc a x, g (x,y) := by
  let O : Set XY := {p | p.2≤p.1}
  have hO : MeasurableSet O := (isClosed_le continuous_snd continuous_fst).measurableSet
  have hi : IntegrableOn g (xySquare a b) :=
    hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc
    _ = ∫ p in xySquare a b, O.indicator g p := (setIntegral_indicator hO).symm
    _ = ∫ x in Icc a b, ∫ y in Icc a b, O.indicator g (x,y) := by
      rw [xySquare, Measure.volume_eq_prod]
      exact setIntegral_prod _ (by
        simpa only [xySquare, Measure.volume_eq_prod] using hi.indicator hO)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have heq : (fun y => O.indicator g (x,y)) =
          (Iic x).indicator (fun y => g (x,y)) := by
        funext y
        by_cases h : y≤x <;> simp [O, h]
      change (∫ y in Icc a b, O.indicator g (x,y)) =
        ∫ y in Icc a x, g (x,y)
      rw [heq, setIntegral_indicator measurableSet_Iic]
      have hset : Icc a b ∩ Iic x = Icc a x := by
        ext y
        constructor
        · intro hy
          exact ⟨hy.1.1,hy.2⟩
        · intro hy
          exact ⟨⟨hy.1,hy.2.trans hx.2⟩,hy.2⟩
      rw [hset]

private theorem reciprocal_Icc {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, 1/x)=Real.log (b/a) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact integral_one_div_of_pos ha (ha.trans_le hab)

private theorem log_ratio_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, Real.log (x/a))=b*Real.log (b/a)-(b-a) := by
  have hn (x : ℝ) (hx : x∈Icc a b) : x≠0 := (ha.trans_le hx.1).ne'
  have heq : (∫ x in Icc a b, Real.log (x/a)) =
      ∫ x in Icc a b, Real.log x-Real.log a := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact Real.log_div (hn x hx) ha.ne'
  have hi : IntervalIntegrable (fun x : ℝ => Real.log x) volume a b :=
    (continuousOn_id.log hn).intervalIntegrable_of_Icc hab
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_sub hi intervalIntegrable_const, integral_log]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [Real.log_div (ha.trans_le hab).ne' ha.ne']
  ring

private theorem log_ratio_over_x_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, Real.log (x/a)/x)=(Real.log (b/a))^2/2 := by
  have hn (x : ℝ) (hx : x∈Icc a b) : x≠0 := (ha.trans_le hx.1).ne'
  have heq : (∫ x in Icc a b, Real.log (x/a)/x) =
      ∫ x in Icc a b, (Real.log x-Real.log a)/x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change Real.log (x/a)/x = (Real.log x-Real.log a)/x
    rw [Real.log_div (hn x hx) ha.ne']
  have hi : IntervalIntegrable (fun x : ℝ => (Real.log x-Real.log a)/x) volume a b :=
    (((continuousOn_id.log hn).sub continuousOn_const).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hd : ∀ x∈uIcc a b, HasDerivAt
      (fun x : ℝ => (Real.log x-Real.log a)^2/2)
      ((Real.log x-Real.log a)/x) x := by
    intro x hx
    have hx' : x∈Icc a b := by simpa only [uIcc_of_le hab] using hx
    have hlog : HasDerivAt (fun y : ℝ => Real.log y-Real.log a) x⁻¹ x :=
      (Real.hasDerivAt_log (hn x hx')).sub_const (Real.log a)
    have hsquare : HasDerivAt
        (fun y : ℝ => (Real.log y-Real.log a)*(Real.log y-Real.log a))
        (x⁻¹*(Real.log x-Real.log a)+(Real.log x-Real.log a)*x⁻¹) x :=
      hlog.fun_mul hlog
    have hhalf : HasDerivAt
        (fun y : ℝ => ((Real.log y-Real.log a)*(Real.log y-Real.log a))/2)
        ((x⁻¹*(Real.log x-Real.log a)+(Real.log x-Real.log a)*x⁻¹)/2) x :=
      hsquare.div_const (2 : ℝ)
    have hvalue : (x⁻¹*(Real.log x-Real.log a)+(Real.log x-Real.log a)*x⁻¹)/2 =
        (Real.log x-Real.log a)/x := by ring
    rw [hvalue] at hhalf
    simpa only [pow_two] using hhalf
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  rw [Real.log_div (ha.trans_le hab).ne' ha.ne']
  ring

/-- Exact reciprocal mass of the closed ordered half. The diagonal is not
silently discarded: both endpoints are included throughout the set integrals. -/
theorem integral_xyTriangle_weight {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b, xyWeight p)=triangleMass a b := by
  rw [integral_xyTriangle_nested a b (continuousOn_xyWeight a b ha)]
  calc
    _ = ∫ x in Icc a b, Real.log (x/a)/x := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change (∫ y in Icc a x, (1/x)*(1/y))=Real.log (x/a)/x
      rw [integral_const_mul, reciprocal_Icc ha hx.1]
      ring
    _ = _ := log_ratio_over_x_integral ha hab

theorem integral_xySquare_weight {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xySquare a b, xyWeight p)=(Real.log (b/a))^2 := by
  rw [xySquare, Measure.volume_eq_prod]
  change (∫ p in Icc a b ×ˢ Icc a b, (1/p.1)*(1/p.2) ∂volume.prod volume)=_
  rw [setIntegral_prod_mul, reciprocal_Icc ha hab]
  ring

theorem triangle_mass_is_half_square {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b, xyWeight p)=
      (∫ p in xySquare a b, xyWeight p)/2 := by
  rw [integral_xyTriangle_weight ha hab, integral_xySquare_weight ha hab]
  rfl

/-- Numerator of the maximum-coordinate expectation. On the true ordered
triangle max(x,y)=x, so no independent-coordinate assumption appears. -/
theorem integral_xyTriangle_max_weight {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b, xyWeight p*max p.1 p.2)=
      b*Real.log (b/a)-(b-a) := by
  have heq : (∫ p in xyTriangle a b, xyWeight p*max p.1 p.2)=
      ∫ p in xyTriangle a b, 1/p.2 := by
    apply setIntegral_congr_fun (measurableSet_xyTriangle a b)
    intro p hp
    change xyWeight p*max p.1 p.2=1/p.2
    rw [max_eq_left (show p.2≤p.1 from hp.2)]
    change (1/p.1)*(1/p.2)*p.1=1/p.2
    calc
      _ = ((1/p.1)*p.1)*(1/p.2) := by ring
      _ = _ := by rw [one_div_mul_cancel (ha.trans_le hp.1.1.1).ne', one_mul]
  have hc : ContinuousOn (fun p : XY => 1/p.2) (xySquare a b) :=
    continuousOn_const.div continuous_snd.continuousOn
      (fun p hp => (ha.trans_le hp.2.1).ne')
  rw [heq, integral_xyTriangle_nested a b hc]
  calc
    _ = ∫ x in Icc a b, Real.log (x/a) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact reciprocal_Icc ha hx.1
    _ = _ := log_ratio_integral ha hab

theorem triangleMass_pos {a b : ℝ} (ha : 0<a) (hab : a<b) :
    0<triangleMass a b := by
  have hl := Real.log_pos ((one_lt_div ha).2 hab)
  exact div_pos (sq_pos_of_pos hl) (by norm_num)

/-- This probability measure is the actual normalized reciprocal triangle. -/
theorem triangleProbability_isProbability {a b : ℝ} (ha : 0<a) (hab : a<b) :
    IsProbabilityMeasure (triangleProbability a b) := by
  have hm := triangleMass_pos ha hab
  have hi : IntegrableOn (fun p : XY => xyWeight p/triangleMass a b)
      (xyTriangle a b) volume :=
    (((continuousOn_xyWeight a b ha).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set inter_subset_left).div_const (triangleMass a b)
  have hn : ∀ᵐ p ∂volume.restrict (xyTriangle a b), 0≤xyWeight p/triangleMass a b := by
    filter_upwards [ae_restrict_mem (measurableSet_xyTriangle a b)] with p hp
    exact div_nonneg (xyWeight_nonneg a b ha hp) hm.le
  constructor
  rw [triangleProbability, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div,
    integral_xyTriangle_weight ha hab.le, div_self hm.ne']
  simp

theorem integral_triangleProbability {a b : ℝ} (ha : 0<a) (hab : a<b) (g : XY → ℝ) :
    (∫ p, g p ∂triangleProbability a b)=
      (∫ p in xyTriangle a b, xyWeight p*g p)/triangleMass a b := by
  rw [triangleProbability, integral_withDensity_eq_integral_toReal_smul
    ((measurable_xyWeight.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ p in xyTriangle a b, (xyWeight p*g p)/triangleMass a b := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_xyTriangle a b)] with p hp
      rw [ENNReal.toReal_ofReal (div_nonneg (xyWeight_nonneg a b ha hp)
        (triangleMass_pos ha hab).le), smul_eq_mul]
      ring
    _ = _ := integral_div _ _

/-- Exact original em formula, now under the true ordered probability. -/
theorem triangleProbability_max_mean {a b : ℝ} (ha : 0<a) (hab : a<b) :
    (∫ p, max p.1 p.2 ∂triangleProbability a b)=maxMean a b := by
  rw [integral_triangleProbability ha hab, integral_xyTriangle_max_weight ha hab.le]
  have hl := (Real.log_pos ((one_lt_div ha).2 hab)).ne'
  unfold triangleMass maxMean
  field_simp [hl]

theorem triangleProbability_x_mean {a b : ℝ} (ha : 0<a) (hab : a<b) :
    (∫ p, p.1 ∂triangleProbability a b)=maxMean a b := by
  have hm : ∀ᵐ p ∂triangleProbability a b, p∈xyTriangle a b :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (measurableSet_xyTriangle a b))
  calc
    _ = ∫ p, max p.1 p.2 ∂triangleProbability a b := by
      apply integral_congr_ae
      filter_upwards [hm] with p hp
      exact (max_eq_left hp.2).symm
    _ = _ := triangleProbability_max_mean ha hab

abbrev PrismPoint := XY × ℝ

def prismRegion (a b c d : ℝ) : Set PrismPoint := xyTriangle a b ×ˢ Icc c d
def prismSquare (a b c d : ℝ) : Set PrismPoint := xySquare a b ×ˢ Icc c d
def prismWeight (p : PrismPoint) : ℝ := 4*xyWeight p.1*(1/p.2^2)
def prismMass (a b c d : ℝ) : ℝ := 4*triangleMass a b*zMass c d
def prismProbability (a b c d : ℝ) : Measure PrismPoint :=
  (volume.restrict (prismRegion a b c d)).withDensity
    (fun p => ENNReal.ofReal (prismWeight p/prismMass a b c d))

private theorem z_mass_integral {c d : ℝ} (hc : 0<c) (hcd : c≤d) :
    (∫ z in Icc c d, 1/z^2)=zMass c d := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  have heq : (fun z : ℝ => 1/z^2)=(fun z => z^(-2:ℤ)) := by
    funext z
    simp [zpow_neg,one_div]
  rw [heq, integral_zpow (Or.inr ⟨by norm_num,
    notMem_uIcc_of_lt hc (hc.trans_le hcd)⟩)]
  unfold zMass
  norm_num [zpow_neg,zpow_natCast]
  field_simp [hc.ne',(hc.trans_le hcd).ne']
  ; ring

theorem integral_prismWeight {a b c d : ℝ}
    (ha : 0<a) (hab : a≤b) (hc : 0<c) (hcd : c≤d) :
    (∫ p in prismRegion a b c d, prismWeight p)=prismMass a b c d := by
  rw [prismRegion, Measure.volume_eq_prod]
  change (∫ p in xyTriangle a b ×ˢ Icc c d,
    (4*xyWeight p.1)*(1/p.2^2) ∂volume.prod volume)=_
  rw [setIntegral_prod_mul (μ := (volume : Measure XY)) (ν := (volume : Measure ℝ)) (fun q : XY => 4*xyWeight q) (fun z : ℝ => 1/z^2) (xyTriangle a b) (Icc c d), integral_const_mul, integral_xyTriangle_weight ha hab,
    z_mass_integral hc hcd]
  rfl

/-- Actual three-dimensional reciprocal mass is exactly half the full square
prism mass, including factor4 and the z^-2 coordinate. -/
theorem original_symmetric_prism_half_mass {a b c d : ℝ}
    (ha : 0<a) (hab : a≤b) (hc : 0<c) (hcd : c≤d) :
    (∫ p in prismRegion a b c d, prismWeight p)=
      (∫ p in prismSquare a b c d, prismWeight p)/2 := by
  rw [integral_prismWeight ha hab hc hcd, prismSquare, Measure.volume_eq_prod]
  change prismMass a b c d=
    (∫ p in xySquare a b ×ˢ Icc c d,
      (4*xyWeight p.1)*(1/p.2^2) ∂volume.prod volume)/2
  rw [setIntegral_prod_mul (μ := (volume : Measure XY)) (ν := (volume : Measure ℝ)) (fun q : XY => 4*xyWeight q) (fun z : ℝ => 1/z^2) (xySquare a b) (Icc c d), integral_const_mul, integral_xySquare_weight ha hab,
    z_mass_integral hc hcd]
  unfold prismMass triangleMass
  ring

theorem integral_prism_max_weight {a b c d : ℝ}
    (ha : 0<a) (hab : a≤b) (hc : 0<c) (hcd : c≤d) :
    (∫ p in prismRegion a b c d, prismWeight p*max p.1.1 p.1.2)=
      4*(b*Real.log (b/a)-(b-a))*zMass c d := by
  have heq : (fun p : PrismPoint => prismWeight p*max p.1.1 p.1.2)=
      (fun p => (4*(xyWeight p.1*max p.1.1 p.1.2))*(1/p.2^2)) := by
    funext p
    unfold prismWeight
    ring
  rw [heq, prismRegion, Measure.volume_eq_prod, setIntegral_prod_mul (μ := (volume : Measure XY)) (ν := (volume : Measure ℝ)) (fun q : XY => 4*(xyWeight q*max q.1 q.2)) (fun z : ℝ => 1/z^2) (xyTriangle a b) (Icc c d),
    integral_const_mul, integral_xyTriangle_max_weight ha hab, z_mass_integral hc hcd]

private theorem prismMass_pos {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hcd : c<d) : 0<prismMass a b c d := by
  exact mul_pos (mul_pos (by norm_num) (triangleMass_pos ha hab))
    (div_pos (sub_pos.mpr hcd) (mul_pos hc (hc.trans hcd)))

private theorem measurable_prismRegion (a b c d : ℝ) :
    MeasurableSet (prismRegion a b c d) :=
  (measurableSet_xyTriangle a b).prod measurableSet_Icc

private theorem measurable_prismWeight : Measurable prismWeight :=
  ((measurable_xyWeight.comp measurable_fst).const_mul 4).mul
    (measurable_const.div (measurable_snd.pow_const 2))

private theorem prismWeight_nonneg {a b c d : ℝ} (ha : 0<a)
    {p : PrismPoint} (hp : p∈prismRegion a b c d) : 0≤prismWeight p := by
  exact mul_nonneg (mul_nonneg (by norm_num) (xyWeight_nonneg a b ha hp.1))
    (one_div_nonneg.mpr (sq_nonneg p.2))

private theorem integrableOn_prismWeight {a b c d : ℝ} (ha : 0<a) (hc : 0<c) :
    IntegrableOn prismWeight (prismRegion a b c d) := by
  have hxy : ContinuousOn (fun p : PrismPoint => xyWeight p.1) (prismSquare a b c d) :=
    (continuousOn_xyWeight a b ha).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hz : ContinuousOn (fun p : PrismPoint => 1/p.2^2) (prismSquare a b c d) :=
    continuousOn_const.div (continuous_snd.continuousOn.pow 2)
      (fun p hp => pow_ne_zero 2 (hc.trans_le hp.2.1).ne')
  have hcompact : IsCompact (prismSquare a b c d) := by
    unfold prismSquare xySquare
    exact (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hi := ((hxy.const_mul 4).mul hz).integrableOn_compact
    (μ := (volume : Measure PrismPoint)) hcompact
  exact hi.mono_set (fun p hp => ⟨hp.1.1,hp.2⟩)

/-- Probability normalization for the TRUE ordered3D prism, not a square
measure mislabeled as the triangle law. -/
theorem prismProbability_isProbability {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hcd : c<d) :
    IsProbabilityMeasure (prismProbability a b c d) := by
  have hm := prismMass_pos ha hab hc hcd
  have hi : IntegrableOn (fun p : PrismPoint => prismWeight p/prismMass a b c d)
      (prismRegion a b c d) (volume : Measure PrismPoint) :=
    (integrableOn_prismWeight (a:=a) (b:=b) (c:=c) (d:=d) ha hc).div_const
      (prismMass a b c d)
  have hn : ∀ᵐ p ∂volume.restrict (prismRegion a b c d),
      0≤prismWeight p/prismMass a b c d := by
    filter_upwards [ae_restrict_mem (measurable_prismRegion a b c d)] with p hp
    exact div_nonneg (prismWeight_nonneg ha hp) hm.le
  constructor
  rw [prismProbability, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div,
    integral_prismWeight ha hab.le hc hcd.le, div_self hm.ne']
  simp

theorem integral_prismProbability {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hcd : c<d) (g : PrismPoint → ℝ) :
    (∫ p, g p ∂prismProbability a b c d)=
      (∫ p in prismRegion a b c d, prismWeight p*g p)/prismMass a b c d := by
  rw [prismProbability, integral_withDensity_eq_integral_toReal_smul
    ((measurable_prismWeight.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ p in prismRegion a b c d, (prismWeight p*g p)/prismMass a b c d := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurable_prismRegion a b c d)] with p hp
      rw [ENNReal.toReal_ofReal (div_nonneg (prismWeight_nonneg ha hp)
        (prismMass_pos ha hab hc hcd).le), smul_eq_mul]
      ring
    _ = _ := integral_div _ _

/-- The actual normalized3D ordered-prism expectation equals the exact em
formula used by mean_upper. No independence of ordered x and y is assumed. -/
theorem prismProbability_max_mean {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hcd : c<d) :
    (∫ p, max p.1.1 p.1.2 ∂prismProbability a b c d)=maxMean a b := by
  rw [integral_prismProbability ha hab hc hcd,
    integral_prism_max_weight ha hab.le hc hcd.le]
  have hl := (Real.log_pos ((one_lt_div ha).2 hab)).ne'
  have hz := (div_pos (sub_pos.mpr hcd) (mul_pos hc (hc.trans hcd))).ne'
  change zMass c d≠0 at hz
  unfold prismMass triangleMass maxMean
  field_simp [hl,hz]

/-- Literal coordinate order for attaching the product-space prism to Fin3. -/
def prismPoint (p : PrismPoint) : Fin 3 → ℝ := ![p.1.1,p.1.2,p.2]

theorem symmetric_prism_subset_actual_compact {a b c d : ℝ}
    (hc : 0<c) (hcut : (1:ℝ)/100≤c) (hza : d≤a)
    (hb : b≤thirdPrefixRho) (hfull : 2*b+3*d≤thirdPrefixTheta)
    {p : PrismPoint} (hp : p∈prismRegion a b c d) :
    prismPoint p∈OriginalThirdCompactPartitionSourceOnly.compactRegion := by
  have hz : 0<p.2 := hc.trans_le hp.2.1
  have hzy : p.2≤p.1.2 := hp.2.2.trans (hza.trans hp.1.1.2.1)
  have hyx : p.1.2≤p.1.1 := hp.1.2
  have hx : p.1.1≤thirdPrefixRho := hp.1.1.1.2.trans hb
  have hcube : p.1.1+p.1.2+3*p.2≤thirdPrefixTheta := by
    linarith [hp.1.1.1.2,hp.1.1.2.2,hp.2.2]
  change ((0<p.2 ∧ p.2≤thirdPrefixRho ∧ p.2≤p.1.2 ∧ p.1.2≤p.1.1 ∧
    p.1.1≤thirdPrefixRho) ∧ p.1.1+p.1.2+3*p.2≤thirdPrefixTheta-2*0) ∧
      (1:ℝ)/100≤p.2
  exact ⟨⟨⟨hz,hzy.trans (hyx.trans hx),hzy,hyx,hx⟩,
    by simpa only [mul_zero,sub_zero] using hcube⟩,hcut.trans hp.2.1⟩

end
end ImbalancedChen.OriginalThirdTriangleMomentsSourceOnly

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
The literal compactKernel is not symmetric off the ordered region. This file
records the exact obstruction; it does NOT assert the requested false
pointwise symmetry or halve the literal kernel integral on a full box.
-/
namespace ImbalancedChen.OriginalThirdSwapAuditSourceOnly
noncomputable section
open Set MeasureTheory
open VariableEnvelope
open OriginalThirdCompactPartitionSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly

/-- Genuine Fin3 coordinate permutation, independently volume preserving. -/
def xySwap : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1)

theorem xySwap_volume_preserving : MeasurePreserving xySwap volume volume := by
  exact volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) (Equiv.swap 0 1)

/-- The equality face x=y is a proper affine null wall. This alone does not
make an arbitrary kernel's two triangular integrals equal. -/
theorem xy_diagonal_volume_zero :
    volume {t : Fin 3 → ℝ | t 0=t 1}=0 := by
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (0 : Fin 3) -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (1 : Fin 3)
  have hL : L≠0 := by
    intro hz
    have hh := congrArg (fun J : (Fin 3 → ℝ) →L[ℝ] ℝ => J ![1,0,0]) hz
    norm_num [L, Matrix.cons_val_two] at hh
  simpa [L, sub_eq_zero] using affinePrimeWall_volume_zero L hL 0

/-- Both coordinates are above mu; the literal dispatch selects v(x). -/
theorem witness_caps :
    actualExtendedThirdBufferedCap 0 (19/96) (63/320) (1/15)=(19/32 : ℝ) ∧
    actualExtendedThirdBufferedCap 0 (63/320) (19/96) (1/15)=(381/640 : ℝ) := by
  norm_num [actualExtendedThirdBufferedCap, thirdPrefixBufferedCap,
    actualExtendedThirdEnvelope, mu, v, VariableEnvelope.A, VariableEnvelope.C, thirdPrefixTheta]

/-- Exact witness: the ordered old argument is 127/64 <= 2, whereas its
swapped old argument is 257/128 > 2. The actual Suzuki lower factor separates
these arguments strictly, so this is a kernel counterexample, not just a
cap counterexample. -/
theorem literal_kernel_swap_strict :
    actualExtendedThirdOrderedKernel 0 (63/320) (19/96) (1/15) <
      actualExtendedThirdOrderedKernel 0 (19/96) (63/320) (1/15) := by
  have hz : actualExtendedThirdLowerFactor (127/64)=0 :=
    actualExtendedThirdLowerFactor_of_le_two (by norm_num)
  have hp : 0<actualExtendedThirdLowerFactor (257/128) := by
    rw [← lower_eq_actual (by norm_num : (2:ℝ)≤257/128),
      lower_eq_log (by norm_num) (by norm_num)]
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hd : actualExtendedThirdOrderedKernel 0 (19/96) (63/320) (1/15)-
      actualExtendedThirdOrderedKernel 0 (63/320) (19/96) (1/15)=
      (3072000/133)*actualExtendedThirdLowerFactor (257/128) := by
    unfold actualExtendedThirdOrderedKernel
    rw [witness_caps.1, witness_caps.2]
    norm_num [thirdPrefixTheta, hz]
    ; ring
  apply sub_pos.mp
  rw [hd]
  exact mul_pos (by norm_num) hp

/-- The first point is in the true ordered compact domain, and its swap is
outside it. Hence the original compact region is itself not swap invariant. -/
theorem witness_region_asymmetry :
    (![19/96,63/320,1/15] : Fin 3 → ℝ)∈compactRegion ∧
    (![63/320,19/96,1/15] : Fin 3 → ℝ)∉compactRegion := by
  norm_num [compactRegion, actualExtendedThirdManuscriptTailRegion,
    actualExtendedThirdClosedOrderRegion, thirdPrefixRho, thirdPrefixTheta,
    Matrix.cons_val_two]

/-- The correct full-box extension of the ordered kernel. This is a separate
function, not an asserted alternative definition of compactKernel off-domain. -/
def sortedKernel (t : Fin 3 → ℝ) : ℝ :=
  actualExtendedThirdOrderedKernel 0 (max (t 0) (t 1)) (min (t 0) (t 1)) (t 2)

theorem sorted_kernel_symmetric (x y z : ℝ) :
    actualExtendedThirdOrderedKernel 0 (max x y) (min x y) z=
      actualExtendedThirdOrderedKernel 0 (max y x) (min y x) z := by
  rw [max_comm x y, min_comm x y]

theorem sortedKernel_eq_actual_on_ordered {t : Fin 3 → ℝ} (ht : t 1≤t 0) :
    sortedKernel t=compactKernel t := by
  simp only [sortedKernel, compactKernel, max_eq_left ht, min_eq_right ht]

/-- Integrability on the original compact domain is supplied by the actual
proved kernel theorem; it is not a new numerical assumption. -/
theorem sortedKernel_integrable_on_compact : IntegrableOn sortedKernel compactRegion := by
  apply integrableOn_compactKernel.congr_fun ?_ measurableSet_compactRegion
  intro t ht
  exact (sortedKernel_eq_actual_on_ordered ht.1.1.2.2.2.1).symm

end
end ImbalancedChen.OriginalThirdSwapAuditSourceOnly

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Correct symmetric-extension half-integral bridge. Whole-box integrability is
DERIVED from actual ordered compact integrability and the Fin3 swap, not
assumed. The common diagonal is explicitly proved null before summing halves.
-/
namespace ImbalancedChen.OriginalThirdSortedHalfIntegralSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdSwapAuditSourceOnly

/-- Original symmetric full-cell geometry in physical coordinates. The last
field retains the generator's original no-crossing-mu gate. -/
structure SymmetricFullBox (a b c d : ℝ) : Prop where
  width_xy : a<b
  width_z : c<d
  cutoff : (1:ℝ)/100≤c
  z_below_xy : d≤a
  upper_rho : b≤thirdPrefixRho
  raw_full : 2*b+3*d≤thirdPrefixTheta
  no_crossing_mu : b≤VariableEnvelope.mu ∨ VariableEnvelope.mu≤a

def symmetricBox (a b c d : ℝ) : Set (Fin 3 → ℝ) :=
  {t | t 0∈Icc a b ∧ t 1∈Icc a b ∧ t 2∈Icc c d}
def orderedHalf (a b c d : ℝ) : Set (Fin 3 → ℝ) :=
  symmetricBox a b c d ∩ {t | t 1≤t 0}
def reflectedHalf (a b c d : ℝ) : Set (Fin 3 → ℝ) :=
  symmetricBox a b c d ∩ {t | t 0≤t 1}

/-- The same box in the existing Fin3 closed-rectangle notation. -/
theorem symmetricBox_eq_Icc (a b c d : ℝ) :
    symmetricBox a b c d=Icc (![a,a,c] : Fin 3 → ℝ) ![b,b,d] := by
  ext t
  constructor
  · rintro ⟨hx,hy,hz⟩
    constructor
    · intro i
      fin_cases i
      · exact hx.1
      · exact hy.1
      · exact hz.1
    · intro i
      fin_cases i
      · exact hx.2
      · exact hy.2
      · exact hz.2
  · intro ht
    exact ⟨⟨ht.1 0,ht.2 0⟩,⟨ht.1 1,ht.2 1⟩,⟨ht.1 2,ht.2 2⟩⟩
private theorem swap_zero (t : Fin 3 → ℝ) : xySwap t 0=t 1 := by
  change MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ)
    (Equiv.swap 0 1) t 0=t 1
  simpa only [Equiv.swap_apply_right] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 3 => ℝ)
      (Equiv.swap (0 : Fin 3) 1) t (1 : Fin 3)

private theorem swap_one (t : Fin 3 → ℝ) : xySwap t 1=t 0 := by
  change MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ)
    (Equiv.swap 0 1) t 1=t 0
  simpa only [Equiv.swap_apply_left] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 3 => ℝ)
      (Equiv.swap (0 : Fin 3) 1) t (0 : Fin 3)

private theorem swap_two (t : Fin 3 → ℝ) : xySwap t 2=t 2 := by
  change MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ)
    (Equiv.swap 0 1) t 2=t 2
  simpa [Equiv.swap_apply_def] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 3 => ℝ)
      (Equiv.swap (0 : Fin 3) 1) t (2 : Fin 3)

theorem sortedKernel_xySwap (t : Fin 3 → ℝ) :
    sortedKernel (xySwap t)=sortedKernel t := by
  simp only [sortedKernel, swap_zero, swap_one, swap_two]
  exact sorted_kernel_symmetric (t 1) (t 0) (t 2)

private theorem measurable_symmetricBox (a b c d : ℝ) :
    MeasurableSet (symmetricBox a b c d) := by
  exact (measurableSet_Icc.preimage (continuous_apply (0 : Fin 3)).measurable).inter
    ((measurableSet_Icc.preimage (continuous_apply (1 : Fin 3)).measurable).inter
      (measurableSet_Icc.preimage (continuous_apply (2 : Fin 3)).measurable))

private theorem measurable_orderedHalf (a b c d : ℝ) :
    MeasurableSet (orderedHalf a b c d) := by
  exact (measurable_symmetricBox a b c d).inter
    (isClosed_le (continuous_apply 1) (continuous_apply 0)).measurableSet

private theorem measurable_reflectedHalf (a b c d : ℝ) :
    MeasurableSet (reflectedHalf a b c d) := by
  exact (measurable_symmetricBox a b c d).inter
    (isClosed_le (continuous_apply 0) (continuous_apply 1)).measurableSet

theorem swap_preimage_orderedHalf (a b c d : ℝ) :
    xySwap ⁻¹' orderedHalf a b c d=reflectedHalf a b c d := by
  ext t
  simp only [mem_preimage, orderedHalf, reflectedHalf, symmetricBox,
    mem_inter_iff, mem_ofPred_eq, swap_zero, swap_one, swap_two]
  constructor
  · rintro ⟨⟨hy,hx,hz⟩,hxy⟩
    exact ⟨⟨hx,hy,hz⟩,hxy⟩
  · rintro ⟨⟨hx,hy,hz⟩,hxy⟩
    exact ⟨⟨hy,hx,hz⟩,hxy⟩

private theorem halves_union (a b c d : ℝ) :
    orderedHalf a b c d ∪ reflectedHalf a b c d=symmetricBox a b c d := by
  ext t
  constructor
  · rintro (ht|ht)
    · exact ht.1
    · exact ht.1
  · intro ht
    rcases le_total (t 1) (t 0) with h|h
    · exact Or.inl ⟨ht,h⟩
    · exact Or.inr ⟨ht,h⟩

private theorem halves_ae_disjoint (a b c d : ℝ) :
    AEDisjoint volume (orderedHalf a b c d) (reflectedHalf a b c d) := by
  change volume (orderedHalf a b c d ∩ reflectedHalf a b c d)=0
  apply measure_mono_null _ xy_diagonal_volume_zero
  intro t ht
  exact le_antisymm ht.2.2 ht.1.2

/-- Every point of the true ordered half lies in the original compact domain. -/
theorem orderedHalf_subset_compact (a b c d : ℝ) (hg : SymmetricFullBox a b c d) :
    orderedHalf a b c d⊆compactRegion := by
  intro t ht
  rcases ht with ⟨⟨hx,hy,hz⟩,hyx⟩
  have hzpos : 0<t 2 := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) hg.cutoff) hz.1
  have hzy : t 2≤t 1 := hz.2.trans (hg.z_below_xy.trans hy.1)
  have hxr : t 0≤thirdPrefixRho := hx.2.trans hg.upper_rho
  have hraw : t 0+t 1+3*t 2≤thirdPrefixTheta := by
    linarith [hx.2,hy.2,hz.2,hg.raw_full]
  exact ⟨⟨⟨hzpos,hzy.trans (hyx.trans hxr),hzy,hyx,hxr⟩,
    by
      change t 0+t 1+3*t 2≤thirdPrefixTheta-2*0
      simpa only [mul_zero,sub_zero] using hraw⟩,hg.cutoff.trans hz.1⟩

/-- Actual ordered-kernel integrability is inherited from the original domain. -/
theorem actualKernel_integrable_orderedHalf (a b c d : ℝ)
    (hg : SymmetricFullBox a b c d) :
    IntegrableOn compactKernel (orderedHalf a b c d) := by
  exact integrableOn_compactKernel.mono_set (orderedHalf_subset_compact a b c d hg)

/-- Intersecting the original compact domain with a symmetric full box gives
exactly its ordered half, with both diagonal endpoints retained. -/
theorem compact_inter_symmetricBox (a b c d : ℝ) (hg : SymmetricFullBox a b c d) :
    compactRegion ∩ symmetricBox a b c d=orderedHalf a b c d := by
  ext t
  constructor
  · rintro ⟨ht,hb⟩
    exact ⟨hb,ht.1.1.2.2.2.1⟩
  · intro ht
    exact ⟨orderedHalf_subset_compact a b c d hg ht,ht.1⟩
/-- Pull actual compact integrability to the reflected half; then join the
halves. No whole-box integrability or leaf-integral bound is a premise. -/
theorem sortedKernel_integrable_symmetricBox (a b c d : ℝ)
    (hg : SymmetricFullBox a b c d) :
    IntegrableOn sortedKernel (symmetricBox a b c d) := by
  have ho : IntegrableOn sortedKernel (orderedHalf a b c d) :=
    sortedKernel_integrable_on_compact.mono_set (orderedHalf_subset_compact a b c d hg)
  have hr : IntegrableOn (sortedKernel ∘ xySwap) (xySwap ⁻¹' orderedHalf a b c d) :=
    (xySwap_volume_preserving.integrableOn_comp_preimage xySwap.measurableEmbedding).2 ho
  have hcomp : sortedKernel ∘ xySwap=sortedKernel := by
    funext t
    exact sortedKernel_xySwap t
  rw [swap_preimage_orderedHalf, hcomp] at hr
  rw [← halves_union a b c d]
  exact ho.union hr

/-- Equality of the two sorted-kernel half integrals follows from the actual
volume-preserving permutation, not from equality of their masses. -/
theorem reflected_sorted_integral_eq_ordered (a b c d : ℝ) :
    (∫ t in reflectedHalf a b c d, sortedKernel t)=
      ∫ t in orderedHalf a b c d, sortedKernel t := by
  have h := xySwap_volume_preserving.setIntegral_preimage_emb
    xySwap.measurableEmbedding sortedKernel (orderedHalf a b c d)
  rw [swap_preimage_orderedHalf] at h
  simpa only [sortedKernel_xySwap] using h

/-- The original actual ordered kernel is exactly the sorted extension on
its ordered half, with all original cap gates and constants intact. -/
theorem ordered_sorted_integral_eq_actual (a b c d : ℝ) :
    (∫ t in orderedHalf a b c d, sortedKernel t)=
      ∫ t in orderedHalf a b c d, compactKernel t := by
  apply setIntegral_congr_fun (measurable_orderedHalf a b c d)
  intro t ht
  exact sortedKernel_eq_actual_on_ordered ht.2

/-- Original symmetric full-cell half-integral rule for the CORRECT extension.
The shared diagonal is null and both half integrals are genuinely integrable. -/
theorem symmetric_box_sorted_integral_eq_twice_actual (a b c d : ℝ)
    (hg : SymmetricFullBox a b c d) :
    (∫ t in symmetricBox a b c d, sortedKernel t)=
      2*(∫ t in orderedHalf a b c d, compactKernel t) := by
  have hi := sortedKernel_integrable_symmetricBox a b c d hg
  have ho : IntegrableOn sortedKernel (orderedHalf a b c d) :=
    hi.mono_set inter_subset_left
  have hr : IntegrableOn sortedKernel (reflectedHalf a b c d) :=
    hi.mono_set inter_subset_left
  calc
    _ = (∫ t in orderedHalf a b c d, sortedKernel t)+
        ∫ t in reflectedHalf a b c d, sortedKernel t := by
      rw [← halves_union a b c d]
      exact setIntegral_union₀ (halves_ae_disjoint a b c d)
        (measurable_reflectedHalf a b c d).nullMeasurableSet ho hr
    _ = _ := by
      rw [reflected_sorted_integral_eq_ordered, ordered_sorted_integral_eq_actual]
      ring

/-- Direct one-half form on the actual compact-domain portion of the box. -/
theorem actual_symmetric_half_integral (a b c d : ℝ)
    (hg : SymmetricFullBox a b c d) :
    (∫ t in compactRegion ∩ symmetricBox a b c d, compactKernel t)=
      (∫ t in symmetricBox a b c d, sortedKernel t)/2 := by
  rw [compact_inter_symmetricBox a b c d hg,
    symmetric_box_sorted_integral_eq_twice_actual a b c d hg]
  ring

end
end ImbalancedChen.OriginalThirdSortedHalfIntegralSourceOnly

/-! SOURCEONLY / UNCOMPILED / OPEN30. Genuine ordered-prism moments for
symmetric mean_upper; ordered x and y are never treated as independent. -/
namespace ImbalancedChen.OriginalThirdSymmetricJensenSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly

def sumMean (a b : ℝ) : ℝ := 2*(b-a)/Real.log (b/a)
def minMean (a b : ℝ) : ℝ := sumMean a b-maxMean a b
def invZMean (c d : ℝ) : ℝ := (c+d)/(2*c*d)
def prismAffine (A B C E : ℝ) (p : PrismPoint) : ℝ :=
  (A+B*p.1.1+C*p.1.2)/p.2+E

def oldLow (b d : ℝ) : ℝ := (57/64-(7/2)*b)/d-1
def oldHigh (a c : ℝ) : ℝ := (57/64-(7/2)*a)/c-1

def oldMean (a b c d : ℝ) : ℝ :=
  (57/64-sumMean a b-(3/2)*maxMean a b)*invZMean c d-1
def newMean (a b c d : ℝ) : ℝ :=
  (thirdPrefixTheta-sumMean a b)*invZMean c d-1

private theorem reciprocal_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ x in Icc a b, 1/x)=Real.log (b/a) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact integral_one_div_of_pos ha (ha.trans_le hab)

/-- True MIN numerator on y<=x: the inner integral has length x-a. -/
theorem triangle_y_numerator {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b, xyWeight p*p.2)=(b-a)-a*Real.log (b/a) := by
  have heq : (∫ p in xyTriangle a b, xyWeight p*p.2)=
      ∫ p in xyTriangle a b, 1/p.1 := by
    apply setIntegral_congr_fun (measurableSet_xyTriangle a b)
    intro p hp
    unfold xyWeight
    field_simp [(ha.trans_le hp.1.1.1).ne',(ha.trans_le hp.1.2.1).ne']

  have hc : ContinuousOn (fun p : XY => 1/p.1) (xySquare a b) :=
    continuousOn_const.div continuous_fst.continuousOn
      (fun p hp => (ha.trans_le hp.1.1).ne')
  rw [heq, integral_xyTriangle_nested a b hc]
  have hi : IntegrableOn (fun x : ℝ => 1/x) (Icc a b) :=
    (continuousOn_const.div continuousOn_id
      (fun x hx => (ha.trans_le hx.1).ne')).integrableOn_compact isCompact_Icc
  have hconst : (∫ x in Icc a b, (1:ℝ))=b-a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    simp
  calc
    _ = ∫ x in Icc a b, 1-a*(1/x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change (∫ y : ℝ in Icc a x, 1/x)=1-a*(1/x)
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [(ha.trans_le hx.1).ne']

    _ = _ := by
      rw [integral_sub (integrable_const 1) (hi.const_mul a), integral_const_mul,
        hconst, reciprocal_integral ha hab]

private theorem triangle_x_numerator {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ p in xyTriangle a b, xyWeight p*p.1)=b*Real.log (b/a)-(b-a) := by
  rw [← integral_xyTriangle_max_weight ha hab]
  apply setIntegral_congr_fun (measurableSet_xyTriangle a b)
  intro p hp
  change xyWeight p*p.1=xyWeight p*max p.1 p.2
  have horder : p.2≤p.1 := hp.2
  rw [max_eq_left horder]

private theorem z_second_integral {c d : ℝ} (hc : 0<c) (hcd : c≤d) :
    (∫ z in Icc c d, 1/z^2)=zMass c d := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  have heq : (fun z : ℝ => 1/z^2)=(fun z => z^(-2:ℤ)) := by
    funext z; simp [zpow_neg,one_div]
  rw [heq,integral_zpow (Or.inr ⟨by norm_num,
    notMem_uIcc_of_lt hc (hc.trans_le hcd)⟩)]
  unfold zMass
  norm_num [zpow_neg,zpow_natCast]
  field_simp [hc.ne',(hc.trans_le hcd).ne']
  ; ring

private theorem z_third_integral {c d : ℝ} (hc : 0<c) (hcd : c≤d) :
    (∫ z in Icc c d, (1/z)/z^2)=zMass c d*invZMean c d := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  have heq : (fun z : ℝ => (1/z)/z^2)=(fun z => z^(-3:ℤ)) := by
    funext z
    by_cases hz : z=0
    · simp [hz]
    · simp only [zpow_neg]
      field_simp [hz]

  rw [heq,integral_zpow (Or.inr ⟨by norm_num,
    notMem_uIcc_of_lt hc (hc.trans_le hcd)⟩)]
  unfold zMass invZMean
  norm_num [zpow_neg,zpow_natCast]
  field_simp [hc.ne',(hc.trans_le hcd).ne']
  ring

/-- Only the XY triangle and the z interval factor; x and y do not. -/
theorem prism_tensor_mean {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hcd : c<d)
    (f : XY → ℝ) (g : ℝ → ℝ) :
    (∫ p, f p.1*g p.2 ∂prismProbability a b c d)=
      ((∫ q in xyTriangle a b, xyWeight q*f q)/triangleMass a b)*
      ((∫ z in Icc c d, g z/z^2)/zMass c d) := by
  rw [integral_prismProbability ha hab hc hcd]
  have heq : (fun p : PrismPoint => prismWeight p*(f p.1*g p.2))=
      (fun p => (4*(xyWeight p.1*f p.1))*(g p.2/p.2^2)) := by
    funext p
    unfold prismWeight
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  change (∫ p : PrismPoint in xyTriangle a b ×ˢ Icc c d,
      (4*(xyWeight p.1*f p.1))*(g p.2/p.2^2)
      ∂(volume : Measure XY).prod (volume : Measure ℝ))/prismMass a b c d = _
  rw [setIntegral_prod_mul (μ := (volume : Measure XY)) (ν := (volume : Measure ℝ))
    (fun q : XY => 4*(xyWeight q*f q)) (fun z : ℝ => g z/z^2)
    (xyTriangle a b) (Icc c d), integral_const_mul]
  have ht := (triangleMass_pos ha hab).ne'
  have hz : zMass c d≠0 := (div_pos (sub_pos.mpr hcd) (mul_pos hc (hc.trans hcd))).ne'
  unfold prismMass
  field_simp [ht,hz]


/-- Exact mixed moments needed by both NEW and OLD arguments. -/
theorem prism_mixed_moments {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hcd : c<d) :
    (∫ p, 1/p.2 ∂prismProbability a b c d)=invZMean c d ∧
    (∫ p, p.1.1/p.2 ∂prismProbability a b c d)=maxMean a b*invZMean c d ∧
    (∫ p, p.1.2/p.2 ∂prismProbability a b c d)=minMean a b*invZMean c d := by
  have h0 := prism_tensor_mean ha hab hc hcd (fun _=>1) (fun z=>1/z)
  have hx := prism_tensor_mean ha hab hc hcd (fun p=>p.1) (fun z=>1/z)
  have hy := prism_tensor_mean ha hab hc hcd (fun p=>p.2) (fun z=>1/z)
  simp only [mul_one,mul_one_div] at h0 hx hy
  rw [integral_xyTriangle_weight ha hab.le,z_third_integral hc hcd.le] at h0
  rw [triangle_x_numerator ha hab.le,z_third_integral hc hcd.le] at hx
  rw [triangle_y_numerator ha hab.le,z_third_integral hc hcd.le] at hy
  have hl := (Real.log_pos ((one_lt_div ha).2 hab)).ne'
  have ht := (triangleMass_pos ha hab).ne'
  have hz : zMass c d≠0 := (div_pos (sub_pos.mpr hcd) (mul_pos hc (hc.trans hcd))).ne'
  refine ⟨?_,?_,?_⟩
  · rw [h0]
    field_simp [ht,hz]
  · rw [hx]
    unfold triangleMass maxMean
    field_simp [hl,hz]

  · rw [hy]
    unfold triangleMass minMean sumMean maxMean
    field_simp [hl,hz]
    ring

/-- MIN and SUM marginal means on the true ordered prism. -/
theorem prism_min_sum_moments {a b c d : ℝ}
    (ha : 0<a) (hab : a<b) (hc : 0<c) (hcd : c<d) :
    (∫ p, p.1.2 ∂prismProbability a b c d)=minMean a b ∧
    (∫ p, p.1.1+p.1.2 ∂prismProbability a b c d)=sumMean a b := by
  have hy := prism_tensor_mean ha hab hc hcd (fun p=>p.2) (fun _=>1)
  have hs := prism_tensor_mean ha hab hc hcd (fun p=>p.1+p.2) (fun _=>1)
  simp only [mul_one] at hy hs
  rw [triangle_y_numerator ha hab.le,z_second_integral hc hcd.le] at hy
  have hxy : (∫ p in xyTriangle a b, xyWeight p*(p.1+p.2))=
      (b-a)*Real.log (b/a) := by
    have hxcont : ContinuousOn (fun p : XY => xyWeight p*p.1) (xySquare a b) := by
      have hw : ContinuousOn xyWeight (xySquare a b) :=
        (continuousOn_const.div continuous_fst.continuousOn
          (fun p hp=>(ha.trans_le hp.1.1).ne')).mul
        (continuousOn_const.div continuous_snd.continuousOn
          (fun p hp=>(ha.trans_le hp.2.1).ne'))
      exact hw.mul continuous_fst.continuousOn
    have hycont : ContinuousOn (fun p : XY => xyWeight p*p.2) (xySquare a b) := by
      have hw : ContinuousOn xyWeight (xySquare a b) :=
        (continuousOn_const.div continuous_fst.continuousOn
          (fun p hp=>(ha.trans_le hp.1.1).ne')).mul
        (continuousOn_const.div continuous_snd.continuousOn
          (fun p hp=>(ha.trans_le hp.2.1).ne'))
      exact hw.mul continuous_snd.continuousOn
    have hi : IntegrableOn (fun p : XY => xyWeight p*p.1) (xyTriangle a b)
        (volume : Measure XY) :=
      (hxcont.integrableOn_compact (μ := (volume : Measure XY))
        (isCompact_Icc.prod isCompact_Icc)).mono_set
        (show xyTriangle a b⊆xySquare a b from inter_subset_left)
    have hj : IntegrableOn (fun p : XY => xyWeight p*p.2) (xyTriangle a b)
        (volume : Measure XY) :=
      (hycont.integrableOn_compact (μ := (volume : Measure XY))
        (isCompact_Icc.prod isCompact_Icc)).mono_set
        (show xyTriangle a b⊆xySquare a b from inter_subset_left)
    simp_rw [mul_add]
    rw [integral_add hi hj,triangle_x_numerator ha hab.le,triangle_y_numerator ha hab.le]
    ring
  rw [hxy,z_second_integral hc hcd.le] at hs
  have hl := (Real.log_pos ((one_lt_div ha).2 hab)).ne'
  have hz : zMass c d≠0 := (div_pos (sub_pos.mpr hcd) (mul_pos hc (hc.trans hcd))).ne'
  refine ⟨?_,?_⟩
  · rw [hy,div_self hz,mul_one]
    unfold triangleMass minMean sumMean maxMean
    field_simp [hl,hz]
    ring
  · rw [hs,div_self hz,mul_one]
    unfold triangleMass sumMean
    field_simp [hl,hz]


end
end ImbalancedChen.OriginalThirdSymmetricJensenSourceOnly

/-! SOURCEONLY / UNCOMPILED / OPEN30. Above-mu actual ordered-prism
NEW Jensen minus OLD lower-endpoint chord; no integral bound is assumed. -/
namespace ImbalancedChen.OriginalThirdSymmetricJensenSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly

def actualPrismOld (p : PrismPoint) : ℝ :=
  (actualExtendedThirdBufferedCap 0 p.1.1 p.1.2 p.2-p.1.1-p.1.2-p.2)/p.2

def symmetricChordMean (a b c d flo fhi : ℝ) : ℝ :=
  flo+(oldMean a b c d-oldLow b d)/(oldHigh a c-oldLow b d)*(fhi-flo)

private theorem positive_a_c {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    0<a ∧ 0<c := by
  have hc : 0<c := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) hg.cutoff
  exact ⟨hc.trans_le (hg.width_z.le.trans hg.z_below_xy),hc⟩

private theorem mass_pos {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    0<prismMass a b c d := by
  have hp := positive_a_c hg
  exact mul_pos (mul_pos (by norm_num) (triangleMass_pos hp.1 hg.width_xy))
    (div_pos (sub_pos.mpr hg.width_z) (mul_pos hp.2 (hp.2.trans hg.width_z)))

private theorem measurable_prism (a b c d : ℝ) : MeasurableSet (prismRegion a b c d) :=
  (measurableSet_xyTriangle a b).prod measurableSet_Icc

private theorem prism_ae_mem (a b c d : ℝ) :
    ∀ᵐ p ∂prismProbability a b c d, p∈prismRegion a b c d := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (measurable_prism a b c d))

private theorem continuous_prism_weight (a b c d : ℝ)
    (ha : 0<a) (hc : 0<c) : ContinuousOn prismWeight (prismSquare a b c d) := by
  have hx : ContinuousOn (fun p : PrismPoint => p.1.1) (prismSquare a b c d) :=
    (continuous_fst.fst : Continuous (fun p : PrismPoint => p.1.1)).continuousOn
  have hy : ContinuousOn (fun p : PrismPoint => p.1.2) (prismSquare a b c d) :=
    (continuous_fst.snd : Continuous (fun p : PrismPoint => p.1.2)).continuousOn
  have hz : ContinuousOn (fun p : PrismPoint => p.2) (prismSquare a b c d) :=
    (continuous_snd : Continuous (fun p : PrismPoint => p.2)).continuousOn
  exact (((continuousOn_const.div hx (fun p hp=>(ha.trans_le hp.1.1.1).ne')).mul
    (continuousOn_const.div hy (fun p hp=>(ha.trans_le hp.1.2.1).ne'))).const_mul 4).mul
    (continuousOn_const.div (hz.pow 2) (fun p hp=>pow_ne_zero 2 (hc.trans_le hp.2.1).ne'))

private theorem continuous_prism_affine (a b c d : ℝ) (hc : 0<c) (A B C E : ℝ) :
    ContinuousOn (prismAffine A B C E) (prismSquare a b c d) := by
  have hx : ContinuousOn (fun p : PrismPoint => p.1.1) (prismSquare a b c d) :=
    (continuous_fst.fst : Continuous (fun p : PrismPoint => p.1.1)).continuousOn
  have hy : ContinuousOn (fun p : PrismPoint => p.1.2) (prismSquare a b c d) :=
    (continuous_fst.snd : Continuous (fun p : PrismPoint => p.1.2)).continuousOn
  have hz : ContinuousOn (fun p : PrismPoint => p.2) (prismSquare a b c d) :=
    (continuous_snd : Continuous (fun p : PrismPoint => p.2)).continuousOn
  exact (((continuousOn_const.add (hx.const_mul B)).add (hy.const_mul C)).div hz
    (fun p hp=>(hc.trans_le hp.2.1).ne')).add continuousOn_const

private theorem integrable_prism_continuous {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) {g : PrismPoint → ℝ}
    (hcont : ContinuousOn g (prismSquare a b c d)) :
    Integrable g (prismProbability a b c d) := by
  have hp := positive_a_c hg
  have hw : Measurable prismWeight :=
    (((measurable_const.div measurable_fst.fst).mul
      (measurable_const.div measurable_fst.snd)).const_mul 4).mul
      (measurable_const.div (measurable_snd.pow_const 2))
  unfold prismProbability
  apply (integrable_withDensity_iff_integrable_smul' ((hw.div_const _).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top))).2
  have hi := ((((continuous_prism_weight a b c d hp.1 hp.2).div_const
    (prismMass a b c d)).mul hcont).integrableOn_compact (μ := volume)
      ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)).mono_set
        (show prismRegion a b c d⊆prismSquare a b c d from fun p h=>⟨h.1.1,h.2⟩)
  apply hi.congr
  filter_upwards [ae_restrict_mem (measurable_prism a b c d)] with p h
  have hx : 0<p.1.1 := hp.1.trans_le h.1.1.1.1
  have hy : 0<p.1.2 := hp.1.trans_le h.1.1.2.1
  have hw0 : 0≤prismWeight p := by unfold prismWeight xyWeight; positivity
  rw [ENNReal.toReal_ofReal (div_nonneg hw0 (mass_pos hg).le),smul_eq_mul]
  rfl

/-- All affine mixed means are supplied by the true ordered moments. -/
theorem prism_affine_mean {a b c d : ℝ} (hg : SymmetricFullBox a b c d)
    (A B C E : ℝ) :
    (∫ p, prismAffine A B C E p ∂prismProbability a b c d)=
      (A+B*maxMean a b+C*minMean a b)*invZMean c d+E := by
  have hp := positive_a_c hg
  let := prismProbability_isProbability hp.1 hg.width_xy hp.2 hg.width_z
  have hz : ContinuousOn (fun p : PrismPoint => p.2) (prismSquare a b c d) :=
    (continuous_snd : Continuous (fun p : PrismPoint => p.2)).continuousOn
  have hn : ∀ p∈prismSquare a b c d, p.2≠0 := fun p h=>(hp.2.trans_le h.2.1).ne'
  have hi : Integrable (fun p : PrismPoint=>1/p.2) (prismProbability a b c d) :=
    integrable_prism_continuous hg (continuousOn_const.div hz hn)
  have hx : Integrable (fun p : PrismPoint=>p.1.1/p.2) (prismProbability a b c d) :=
    integrable_prism_continuous hg
    ((continuous_fst.fst : Continuous (fun p : PrismPoint=>p.1.1)).continuousOn.div hz hn)
  have hy : Integrable (fun p : PrismPoint=>p.1.2/p.2) (prismProbability a b c d) :=
    integrable_prism_continuous hg
    ((continuous_fst.snd : Continuous (fun p : PrismPoint=>p.1.2)).continuousOn.div hz hn)
  have heq : prismAffine A B C E=(fun p=>A*(1/p.2)+B*(p.1.1/p.2)+C*(p.1.2/p.2)+E) := by
    funext p; unfold prismAffine; simp only [div_eq_mul_inv]; ring
  rw [heq,integral_add
    (f := fun p : PrismPoint=>A*(1/p.2)+B*(p.1.1/p.2)+C*(p.1.2/p.2))
    (((hi.const_mul A).add (hx.const_mul B)).add (hy.const_mul C))
    (integrable_const E),integral_add
    (f := fun p : PrismPoint=>A*(1/p.2)+B*(p.1.1/p.2))
    ((hi.const_mul A).add (hx.const_mul B))
    (hy.const_mul C),integral_add (hi.const_mul A) (hx.const_mul B)]
  simp only [integral_const_mul,integral_const,measureReal_def,measure_univ,
    ENNReal.toReal_one,one_smul]
  have hm := prism_mixed_moments hp.1 hg.width_xy hp.2 hg.width_z
  rw [hm.1,hm.2.1,hm.2.2]
  ring

/-- Explicit E[min] under the TRUE triangle law, retaining the original order. -/
theorem prism_min_mean {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    (∫ p, min p.1.1 p.1.2 ∂prismProbability a b c d)=minMean a b := by
  have hp := positive_a_c hg
  calc
    _ = ∫ p, p.1.2 ∂prismProbability a b c d := by
      apply integral_congr_ae
      filter_upwards [prism_ae_mem a b c d] with p h
      exact min_eq_right h.1.2
    _ = _ := (prism_min_sum_moments hp.1 hg.width_xy hp.2 hg.width_z).1

/-- The exact mixed E[(x+y)/z] used by the original NEW mean. -/
theorem prism_sum_div_z_mean {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    (∫ p, (p.1.1+p.1.2)/p.2 ∂prismProbability a b c d)=
      sumMean a b*invZMean c d := by
  have hm := prism_affine_mean hg 0 1 1 0
  simp only [prismAffine,zero_add,one_mul,add_zero] at hm
  rw [hm]
  unfold minMean
  ring
/-- Above-mu OLD minorant and exact endpoint range come from actual geometry.
The mu wall is included: only a minorant is used, not a false cap equality. -/
theorem actual_prism_old_minorant_range {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : VariableEnvelope.mu≤a)
    {p : PrismPoint} (h : p∈prismRegion a b c d) :
    prismAffine (57/64) (-(5/2)) (-1) (-1) p≤actualPrismOld p ∧
    prismAffine (57/64) (-(5/2)) (-1) (-1) p∈Icc (oldLow b d) (oldHigh a c) := by
  have hp := positive_a_c hg
  have hz : 0<p.2 := hp.2.trans_le h.2.1
  have hxm : VariableEnvelope.mu≤p.1.1 := hmu.trans h.1.1.1.1
  have hv := v_le_actualExtendedThirdEnvelope p.1.1 p.1.2 p.2
  rw [VariableEnvelope.v_eq_C hxm] at hv
  have hroot : VariableEnvelope.C p.1.1≤thirdPrefixTheta := by
    dsimp [VariableEnvelope.C,VariableEnvelope.mu,thirdPrefixTheta] at hxm ⊢
    linarith
  have hcap : VariableEnvelope.C p.1.1≤
      actualExtendedThirdBufferedCap 0 p.1.1 p.1.2 p.2 := by
    simpa only [actualExtendedThirdBufferedCap,thirdPrefixBufferedCap,mul_zero,sub_zero]
      using le_min hroot hv
  have hloN : 0≤57/64-(7/2)*b := by
    have hb := hg.upper_rho
    dsimp [thirdPrefixRho] at hb
    linarith
  have hlow : 57/64-(7/2)*b≤57/64-(5/2)*p.1.1-p.1.2 := by
    linarith [h.1.1.1.2,h.1.1.2.2]
  have hhigh : 57/64-(5/2)*p.1.1-p.1.2≤57/64-(7/2)*a := by
    linarith [h.1.1.1.1,h.1.1.2.1]
  have hn := hloN.trans hlow
  have hl := div_le_div₀ hn hlow hz h.2.2
  have hh := div_le_div₀ (hn.trans hhigh) hhigh hp.2 h.2.1
  constructor
  · have heq : prismAffine (57/64) (-(5/2)) (-1) (-1) p=
        (VariableEnvelope.C p.1.1-p.1.1-p.1.2-p.2)/p.2 := by
      unfold prismAffine VariableEnvelope.C
      field_simp [hz.ne']
      ; ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith [hcap]) hz.le
  · have heq : prismAffine (57/64) (-(5/2)) (-1) (-1) p=
        (57/64-(5/2)*p.1.1-p.1.2)/p.2-1 := by
      unfold prismAffine
      ring
    rw [heq]
    exact ⟨sub_le_sub_right hl 1,sub_le_sub_right hh 1⟩

private theorem integrable_actual_prism_old {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) :
    Integrable (fun p=>actualExtendedThirdLowerFactor (actualPrismOld p))
      (prismProbability a b c d) := by
  have hp := positive_a_c hg
  let := prismProbability_isProbability hp.1 hg.width_xy hp.2 hg.width_z
  have hm : Measurable (prismPoint : PrismPoint → Fin 3 → ℝ) := by
    apply measurable_pi_iff.2
    intro i
    fin_cases i
    · exact measurable_fst.fst
    · exact measurable_fst.snd
    · exact measurable_snd
  have hcap := (measurable_actualExtendedThirdBufferedCap 0).comp hm
  have ho : Measurable actualPrismOld :=
    (((hcap.sub measurable_fst.fst).sub measurable_fst.snd).sub measurable_snd).div measurable_snd
  apply Integrable.of_bound (measurable_actualExtendedThirdLowerFactor.comp ho).aestronglyMeasurable
    (1/(2*Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun p=>by
    change ‖actualExtendedThirdLowerFactor (actualPrismOld p)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (actualExtendedThirdLowerFactor_nonneg _)]
    exact actualExtendedThirdLowerFactor_le_normalization _)

/-- The actual symmetric NEW Jensen minus OLD lower-endpoint chord candidate,
under the correctly normalized ordered-prism probability. -/
theorem symmetric_prism_mean_upper {a b c d flo fhi out : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : VariableEnvelope.mu≤a)
    (hlo : 2≤oldLow b d) (hspan : oldLow b d<oldHigh a c)
    (hfl : flo≤actualExtendedThirdLowerFactor (oldLow b d))
    (hfh : fhi≤actualExtendedThirdLowerFactor (oldHigh a c))
    (hout : actualExtendedThirdLowerFactor (newMean a b c d)≤out) :
    (∫ p, actualExtendedThirdLowerFactor
        (prismAffine thirdPrefixTheta (-1) (-1) (-1) p)-
      actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d)≤
      max 0 (out-symmetricChordMean a b c d flo fhi) := by
  have hp := positive_a_c hg
  let := prismProbability_isProbability hp.1 hg.width_xy hp.2 hg.width_z
  have hn := continuous_prism_affine a b c d hp.2 thirdPrefixTheta (-1) (-1) (-1)
  have ho := continuous_prism_affine a b c d hp.2 (57/64) (-(5/2)) (-1) (-1)
  have hin := integrable_prism_continuous hg hn
  have hfn := integrable_prism_continuous hg
    (continuous_actualExtendedThirdLowerFactor.comp_continuousOn hn)
  have hio := integrable_prism_continuous hg ho
  have hfo := integrable_actual_prism_old hg
  have hnewrange : ∀ᵐ p ∂prismProbability a b c d,
      2≤prismAffine thirdPrefixTheta (-1) (-1) (-1) p := by
    filter_upwards [prism_ae_mem a b c d] with p h
    have hz : 0<p.2 := hp.2.trans_le h.2.1
    have hraw : p.1.1+p.1.2+3*p.2≤thirdPrefixTheta := by
      linarith [h.1.1.1.2,h.1.1.2.2,h.2.2,hg.raw_full]
    have hdiv := (le_div_iff₀ hz).2 (show 3*p.2≤thirdPrefixTheta-p.1.1-p.1.2 by linarith)
    simpa only [prismAffine,neg_one_mul,←sub_eq_add_neg] using
      (show 2≤(thirdPrefixTheta-p.1.1-p.1.2)/p.2-1 by linarith)
  have hJ := actual_lower_Jensen_probability (prismProbability a b c d)
    (prismAffine thirdPrefixTheta (-1) (-1) (-1)) hnewrange hin hfn
  rw [prism_affine_mean hg] at hJ
  have hnewmean : (thirdPrefixTheta+(-1)*maxMean a b+(-1)*minMean a b)*invZMean c d+(-1)=
      newMean a b c d := by unfold newMean minMean; ring
  rw [hnewmean] at hJ
  have hchord := (integrable_const flo).add
    (((hio.sub (integrable_const (oldLow b d))).div_const
      (oldHigh a c-oldLow b d)).mul_const (fhi-flo))
  have hOld := integral_mono_ae hchord hfo (show
      (fun p=>flo+(prismAffine (57/64) (-(5/2)) (-1) (-1) p-oldLow b d)/
        (oldHigh a c-oldLow b d)*(fhi-flo)) ≤ᵐ[prismProbability a b c d]
      (fun p=>actualExtendedThirdLowerFactor (actualPrismOld p)) from by
    filter_upwards [prism_ae_mem a b c d] with p h
    have hm := actual_prism_old_minorant_range hg hmu h
    exact (actual_lower_query_endpoint_chord hlo hspan hm.2 hfl hfh).trans
      (monotone_actualExtendedThirdLowerFactor hm.1))
  rw [integral_add' (integrable_const flo)
    (((hio.sub (integrable_const (oldLow b d))).div_const
      (oldHigh a c-oldLow b d)).mul_const (fhi-flo)),integral_mul_const,integral_div,
    integral_sub' hio (integrable_const (oldLow b d))] at hOld
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hOld
  rw [prism_affine_mean hg] at hOld
  have hom : (57/64+(-(5/2))*maxMean a b+(-1)*minMean a b)*invZMean c d+(-1)=
      oldMean a b c d := by unfold oldMean minMean; ring
  rw [hom] at hOld
  change symmetricChordMean a b c d flo fhi≤_ at hOld
  rw [integral_sub
    (f := fun p=>actualExtendedThirdLowerFactor (prismAffine thirdPrefixTheta (-1) (-1) (-1) p))
    hfn hfo]
  exact (sub_le_sub (hJ.trans hout) hOld).trans (le_max_right _ _)

/-- Remove the actual prism probability normalizer, retaining factor4 in the
original reciprocal density. This is a genuine actual-kernel integral bound. -/
theorem symmetric_prism_actual_integral_upper {a b c d flo fhi out : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : VariableEnvelope.mu≤a)
    (hlo : 2≤oldLow b d) (hspan : oldLow b d<oldHigh a c)
    (hfl : flo≤actualExtendedThirdLowerFactor (oldLow b d))
    (hfh : fhi≤actualExtendedThirdLowerFactor (oldHigh a c))
    (hout : actualExtendedThirdLowerFactor (newMean a b c d)≤out) :
    (∫ p in prismRegion a b c d, compactKernel (prismPoint p))≤
      prismMass a b c d*max 0 (out-symmetricChordMean a b c d flo fhi) := by
  have hp := positive_a_c hg
  let g : PrismPoint → ℝ := fun p=>actualExtendedThirdLowerFactor
      (prismAffine thirdPrefixTheta (-1) (-1) (-1) p)-
    actualExtendedThirdLowerFactor (actualPrismOld p)
  have heq : (∫ p in prismRegion a b c d, compactKernel (prismPoint p))=
      ∫ p in prismRegion a b c d, prismWeight p*g p := by
    apply setIntegral_congr_fun (measurable_prism a b c d)
    intro p h
    have hz := (hp.2.trans_le h.2.1).ne'
    have ha : (thirdPrefixTheta-2*0-p.1.1-p.1.2-p.2)/p.2=
        prismAffine thirdPrefixTheta (-1) (-1) (-1) p := by
      unfold prismAffine
      field_simp [hz]
      ; ring
    simp only [compactKernel,prismPoint,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,actualExtendedThirdOrderedKernel]
    rw [ha]
    change 4*g p/(p.1.1*p.1.2*p.2^2)=prismWeight p*g p
    simp only [prismWeight,xyWeight,div_eq_mul_inv,mul_inv_rev]
    ring
  have hmean := symmetric_prism_mean_upper hg hmu hlo hspan hfl hfh hout
  have hprob := integral_prismProbability hp.1 hg.width_xy hp.2 hg.width_z g
  rw [heq,← (eq_div_iff (mass_pos hg).ne').mp hprob]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hmean (mass_pos hg).le

end
end ImbalancedChen.OriginalThirdSymmetricJensenSourceOnly

/-! SOURCEONLY / UNCOMPILED / OPEN30. Actual Fin3/prism transport and the
symmetric above-mu leaf candidate. No mass-only kernel halving shortcut. -/
namespace ImbalancedChen.OriginalThirdSymmetricJensenSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly

def finPrismEquiv : (Fin 3 → ℝ) ≃ᵐ PrismPoint :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3=>ℝ) 2).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2=>ℝ)))).trans
      MeasurableEquiv.prodComm

theorem finPrismEquiv_apply (t : Fin 3 → ℝ) :
    finPrismEquiv t=((t 0,t 1),t 2) := by
  rfl

theorem finPrismEquiv_symm_apply (p : PrismPoint) :
    finPrismEquiv.symm p=prismPoint p := by
  apply finPrismEquiv.injective
  rw [finPrismEquiv.apply_symm_apply,finPrismEquiv_apply]
  rfl

/-- The product-space triangle measure is the actual Fin3 Lebesgue measure
in the literal x,y,z coordinate order. -/
theorem finPrismEquiv_volume_preserving : MeasurePreserving finPrismEquiv volume volume := by
  have hid : MeasurePreserving (id : ℝ → ℝ) volume volume := by
    constructor
    · exact measurable_id
    · simp
  have htwo := volume_preserving_piFinTwo (fun _ : Fin 2=>ℝ)
  have hthree := volume_preserving_piFinSuccAbove (fun _ : Fin 3=>ℝ) (2 : Fin 3)
  have hprod : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.piFinTwo (fun _ : Fin 2=>ℝ))) volume volume := by
    simpa only [Measure.volume_eq_prod] using hid.prod htwo
  have hswap : MeasurePreserving (Prod.swap : ℝ × (ℝ × ℝ) → PrismPoint) volume volume := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap : MeasurePreserving
        (Prod.swap : ℝ × (ℝ × ℝ) → PrismPoint) (volume.prod volume) (volume.prod volume))
  exact hswap.comp (hprod.comp hthree)

theorem prism_preimage_orderedHalf (a b c d : ℝ) :
    finPrismEquiv.symm ⁻¹' orderedHalf a b c d=prismRegion a b c d := by
  ext p
  simp only [mem_preimage,finPrismEquiv_symm_apply,orderedHalf,symmetricBox,
    prismRegion,xyTriangle,xySquare,prismPoint,mem_inter_iff,mem_ofPred_eq,mem_prod,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  constructor
  · rintro ⟨⟨hx,hy,hz⟩,horder⟩
    exact ⟨⟨⟨hx,hy⟩,horder⟩,hz⟩
  · rintro ⟨⟨⟨hx,hy⟩,horder⟩,hz⟩
    exact ⟨⟨hx,hy,hz⟩,horder⟩

theorem prism_actual_integral_eq_ordered (a b c d : ℝ) :
    (∫ p in prismRegion a b c d, compactKernel (prismPoint p))=
      ∫ t in orderedHalf a b c d, compactKernel t := by
  have hs : MeasurePreserving finPrismEquiv.symm volume volume :=
    finPrismEquiv_volume_preserving.symm finPrismEquiv
  have hi := hs.setIntegral_preimage_emb finPrismEquiv.symm.measurableEmbedding
    compactKernel (orderedHalf a b c d)
  rw [prism_preimage_orderedHalf] at hi
  simpa only [finPrismEquiv_symm_apply] using hi

/-- Actual prism-kernel integrability is transported from the existing actual
compact-domain theorem, not presumed from a finite numerical allowance. -/
theorem actual_prism_kernel_integrable {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    IntegrableOn (fun p=>compactKernel (prismPoint p)) (prismRegion a b c d) := by
  have hs : MeasurePreserving finPrismEquiv.symm volume volume :=
    finPrismEquiv_volume_preserving.symm finPrismEquiv
  have hi := (hs.integrableOn_comp_preimage finPrismEquiv.symm.measurableEmbedding).2
    (actualKernel_integrable_orderedHalf a b c d hg)
  rw [prism_preimage_orderedHalf] at hi
  simpa only [Function.comp_def,finPrismEquiv_symm_apply] using hi
/-- Original symmetric leaf candidate with actual cap/minorant and range
geometry supplied, correct triangle moments, NEW Jensen and OLD subtraction.
Endpoint numbers are normalized real query bounds; fixed-point rounding is
not silently asserted here. -/
theorem original_symmetric_above_mu_leaf_upper {a b c d flo fhi out : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : VariableEnvelope.mu≤a)
    (hlo : 2≤oldLow b d) (hspan : oldLow b d<oldHigh a c)
    (hfl : flo≤actualExtendedThirdLowerFactor (oldLow b d))
    (hfh : fhi≤actualExtendedThirdLowerFactor (oldHigh a c))
    (hout : actualExtendedThirdLowerFactor (newMean a b c d)≤out) :
    (∫ t in compactRegion ∩ symmetricBox a b c d, compactKernel t)≤
      prismMass a b c d*max 0 (out-symmetricChordMean a b c d flo fhi) := by
  rw [compact_inter_symmetricBox a b c d hg,← prism_actual_integral_eq_ordered]
  exact symmetric_prism_actual_integral_upper hg hmu hlo hspan hfl hfh hout

/-- The original mass is half the full reciprocal box mass, including factor4.
This algebraic identity is separate from the proved kernel transport. -/
theorem symmetric_mass_formula (a b c d : ℝ) :
    prismMass a b c d=(Real.log (b/a))^2*(4*(d-c)/(c*d))/2 := by
  unfold prismMass triangleMass OriginalThirdBoxMomentsSourceOnly.zMass
  ring

/-- Link the NEW mean to an outward rational query without assuming an
upper bound at a nonrational argument supplied directly by the table. -/
theorem symmetric_new_upper_of_query (a b c d : ℝ) (q : ℚ) (out : ℝ)
    (hmean : newMean a b c d≤(q:ℝ))
    (hquery : actualExtendedThirdLowerFactor (q:ℝ)≤out) :
    actualExtendedThirdLowerFactor (newMean a b c d)≤out := by
  exact (monotone_actualExtendedThirdLowerFactor hmean).trans hquery

end
end ImbalancedChen.OriginalThirdSymmetricJensenSourceOnly
