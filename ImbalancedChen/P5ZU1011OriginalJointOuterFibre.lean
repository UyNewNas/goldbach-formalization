import ImbalancedChen.P5ZU1011OriginalJointHarmonic
import ImbalancedChen.P5ZU1011OriginalSixteenPointwiseFibre

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
ONE raw original16 nonlinear fibre for the true joint U10+retained-U11
support. Low x<h is NEVER masked; high h<=x reads the original last-pair
mask once. The earlier raw fibre had no high-band indicator; only its old
outer/source restriction did. We reuse that raw function and prove new
joint geometry, genuine independent D10 bounds, every-pair integrability,
nested Fubini and the actual joint weighted integral dictionary.
No D10-subset-D11, slice/Fubini/mean assumption or moving-mask limit.
-/

namespace ImbalancedChen.P5Z.U1011OriginalJointOuterFibre

noncomputable section

open Set MeasureTheory Filter Classical
open U11Integral U11Canonical U11H248
open U1011OriginalSixteenOuterFibre (Outer Inner join innerDomain split split_symm_apply
  split_measurePreserving harmonicDensity_join measurableSet_innerDomain ascendingMask measurableSet_ascendingMask)

abbrev jointKernel := U1011OriginalJointHarmonic.actualMinimum

/-- Both old APIs are the identical RAW bank, with no source indicator. -/
theorem jointKernel_eq_raw_high_kernel : jointKernel = U1011OriginalSixteenReassembly.actualMinimum := rfl

def jointDomain (M : Set Outer) : Set LogFour :=
  U1011OriginalSixteenU10Geometry.domain10 ∪ originalDomain M

def outerDomain (M : Set Outer) : Set Outer :=
  {q | (417/5000 : ℝ)<q.1 ∧ q.1<(59/250 : ℝ) ∧
    (417/5000 : ℝ)<q.2 ∧ q.2<min q.1 (19/125 : ℝ) ∧
    (q.1<(19/125 : ℝ) ∨ q∉M)}

theorem measurableSet_jointDomain (M : Set Outer) (hM : MeasurableSet M) :
    MeasurableSet (jointDomain M) :=
  U1011OriginalSixteenU10Geometry.measurableSet_domain10.union
    (measurableSet_originalDomain M hM)

theorem measurableSet_outerDomain (M : Set Outer) (hM : MeasurableSet M) :
    MeasurableSet (outerDomain M) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_lt measurable_snd (measurable_fst.min measurable_const)).inter
          ((measurableSet_lt measurable_fst measurable_const).union hM.compl))))

/-- The low band has no mask test; the high band has exactly one. -/
theorem mem_jointDomain_join_iff (M : Set Outer) (q : Outer) (r : Inner) :
    join q r ∈ jointDomain M ↔ q ∈ outerDomain M ∧ r ∈ innerDomain q.2 := by
  constructor
  · intro hv
    rcases hv with h10 | h11
    · change (417/5000 : ℝ)≤r 1 ∧ r 1<r 0 ∧ r 0<q.2 ∧ q.2<q.1 ∧ q.1<19/125 at h10
      exact ⟨⟨h10.1.trans_lt (h10.2.1.trans (h10.2.2.1.trans h10.2.2.2.1)),
        h10.2.2.2.2.trans (by norm_num), h10.1.trans_lt (h10.2.1.trans h10.2.2.1),
        lt_min h10.2.2.2.1 (h10.2.2.2.1.trans h10.2.2.2.2), Or.inl h10.2.2.2.2⟩,
        h10.1,h10.2.1,h10.2.2.1⟩
    · change (417/5000 : ℝ)≤r 1 ∧ r 1<r 0 ∧ r 0<q.2 ∧ q.2<19/125 ∧
        (19/125 : ℝ)≤q.1 ∧ q.1<59/250 ∧ q∉M at h11
      exact ⟨⟨lt_of_lt_of_le (by norm_num) h11.2.2.2.2.1, h11.2.2.2.2.2.1,
        h11.1.trans_lt (h11.2.1.trans h11.2.2.1),
        lt_min (h11.2.2.2.1.trans_le h11.2.2.2.2.1) h11.2.2.2.1,
        Or.inr h11.2.2.2.2.2.2⟩,h11.1,h11.2.1,h11.2.2.1⟩
  · rintro ⟨⟨hxa,hxd,hya,hym,hkeep⟩,ha,hwz,hzy⟩
    rcases hkeep with hlow | hmask
    · exact Or.inl ⟨ha,hwz,hzy,(lt_min_iff.mp hym).1,hlow⟩
    · by_cases hlow : q.1<(19/125 : ℝ)
      · exact Or.inl ⟨ha,hwz,hzy,(lt_min_iff.mp hym).1,hlow⟩
      · exact Or.inr ⟨ha,hwz,hzy,(lt_min_iff.mp hym).2,le_of_not_gt hlow,hxd,hmask⟩

theorem outerDomain_ascending_iff (E : Set Outer) (q : Outer) :
    q ∈ outerDomain (ascendingMask E) ↔
      (417/5000 : ℝ)<q.1 ∧ q.1<(59/250 : ℝ) ∧ (417/5000 : ℝ)<q.2 ∧
        q.2<min q.1 (19/125 : ℝ) ∧ (q.1<(19/125 : ℝ) ∨ (q.2,q.1)∉E) := Iff.rfl

theorem outer_coordinates_pos {M : Set Outer} {q : Outer} (hq : q ∈ outerDomain M) :
    0<q.1 ∧ 0<q.2 := by constructor <;> linarith [hq.1,hq.2.2.1]

theorem outerDomain_subset_unmasked (M : Set Outer) : outerDomain M ⊆ outerDomain ∅ := by
  intro q hq
  exact ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,Or.inr (by simp)⟩

theorem high_outerDomain_iff (M : Set Outer) {q : Outer} (hq : (19/125 : ℝ)≤q.1) :
    q ∈ outerDomain M ↔ q ∈ U1011OriginalSixteenOuterFibre.outerDomain M := by
  constructor
  · rintro ⟨hxa,hxd,hya,hym,hkeep⟩
    have hn : q∉M := hkeep.resolve_left (not_lt_of_ge hq)
    exact ⟨hq,hxd,hya,(lt_min_iff.mp hym).2,hn⟩
  · rintro ⟨hxh,hxd,hya,hyh,hm⟩
    exact ⟨lt_of_lt_of_le (by norm_num) hxh,hxd,hya,
      lt_min (hyh.trans_le hxh) hyh,Or.inr hm⟩

/-- Independent true low-band bound. The U11 high support never enters. -/
theorem ordinary_nonneg_D10 (j : ℕ) (v : LogFour)
    (hv : v ∈ U1011OriginalSixteenU10Geometry.domain10)
    (he : U1011OriginalSixteenPolicyBank.eligible j v) :
    0≤ordinaryKernel Part5UpperTables.H248 U1011OriginalSixteenPolicyBank.residual j v := by
  have hj : j<16 := by
    by_contra hn
    simp only [U1011OriginalSixteenPolicyBank.eligible,dif_neg hn] at he
  have he' : U1011OriginalSixteenPolicyBank.TypedEligible ⟨j,hj⟩ v := by
    simpa only [U1011OriginalSixteenPolicyBank.eligible,dif_pos hj] using he
  have hr : v 3<U1011OriginalSixteenPolicyBank.residual j v := by
    simpa only [U1011OriginalSixteenPolicyBank.residual,dif_pos hj] using
      U1011OriginalSixteenPolicyBank.typedEligible_residual_gt_smallest ⟨j,hj⟩ v he'
  have hp : 0<U1011OriginalSixteenPolicyBank.residual j v :=
    (U1011OriginalSixteenU10Geometry.domain10_smallest_pos hv).trans hr
  have hH := H248_max_two_bounds (U1011OriginalSixteenPolicyBank.residual j v/v 3)
  exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hH.2)) hp.le

theorem switched_bounds_D10 {v : LogFour} (hv : v ∈ U1011OriginalSixteenU10Geometry.domain10) :
    0≤switchedKernel currentK LiLiuPrereqBuchstab.buchstab v ∧
      switchedKernel currentK LiLiuPrereqBuchstab.buchstab v≤|currentK|/(417/5000 : ℝ) := by
  have ha : (0 : ℝ)<417/5000 := by norm_num
  have hza : (417/5000 : ℝ)≤v 2 := hv.1.trans hv.2.1.le
  have hz := ha.trans_le hza
  have hs : 1≤(1-(v 0+v 1+v 2+v 3))/v 2 :=
    (by norm_num : (1 : ℝ)≤49/19).trans (U1011OriginalSixteenU10Geometry.domain10_argument_bounds hv).1
  have hω0 := LiLiuPrereqBuchstab.buchstab_nonneg hs
  have hω1 := LiLiuPrereqBuchstab.buchstab_le_one hs
  have hK : (0 : ℝ)≤currentK := by norm_num [currentK]
  constructor
  · exact div_nonneg (mul_nonneg hK hω0) hz.le
  · calc
      _ ≤ currentK/v 2 := div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hω1 hK) hz.le
      _ ≤ currentK/(417/5000 : ℝ) := div_le_div_of_nonneg_left hK ha hza
      _ ≤ _ := div_le_div_of_nonneg_right (le_abs_self _) ha.le

theorem jointKernel_bounds_D10 {v : LogFour} (hv : v ∈ U1011OriginalSixteenU10Geometry.domain10) :
    0≤jointKernel v ∧ jointKernel v≤|currentK|/(417/5000 : ℝ) := by
  have h := guarded_envelope_bounds U1011OriginalSixteenU10Geometry.domain10
    U1011OriginalSixteenPolicyBank.bank U1011OriginalSixteenPolicyBank.eligible
    (switchedKernel currentK LiLiuPrereqBuchstab.buchstab)
    (ordinaryKernel Part5UpperTables.H248 U1011OriginalSixteenPolicyBank.residual)
    (fun v hv => (switched_bounds_D10 hv).1)
    (fun j _ v hv he => ordinary_nonneg_D10 j v hv he) v hv
  exact ⟨h.1,h.2.trans (switched_bounds_D10 hv).2⟩

theorem jointKernel_bounds {M : Set Outer} {v : LogFour} (hv : v ∈ jointDomain M) :
    0≤jointKernel v ∧ jointKernel v≤|currentK|/(417/5000 : ℝ) := by
  rcases hv with h10 | h11
  · exact jointKernel_bounds_D10 h10
  · have h := U1011OriginalSixteenReassembly.actualMinimum_bounds M v h11
    exact ⟨h.1,h.2.trans ((le_abs_self _).trans (abs_canonical_switched_le M currentK v h11))⟩

def innerIntegrand (q : Outer) (r : Inner) : ℝ := jointKernel (join q r)/(r 0*r 1)
def jointFibreCost (q : Outer) : ℝ := ∫ r in innerDomain q.2,innerIntegrand q r
def jointOuterCost (q : Outer) : ℝ := jointFibreCost q/(q.1*q.2)

/-- There was no high flag inside the previous RAW fibre. The new joint
geometry, not a replacement low-band function, enlarges its domain. -/
theorem jointFibreCost_eq_raw_old (q : Outer) :
    jointFibreCost q=U1011OriginalSixteenOuterFibre.fibreCost q := rfl
theorem jointOuterCost_eq_raw_old (q : Outer) :
    jointOuterCost q=U1011OriginalSixteenOuterFibre.outerCost q := rfl

theorem measurable_innerIntegrand (q : Outer) : Measurable (innerIntegrand q) := by
  exact (U1011OriginalSixteenReassembly.measurable_actualMinimum.comp
    (U1011OriginalSixteenPointwiseFibre.continuous_join q).measurable).div
      ((measurable_pi_apply 0).mul (measurable_pi_apply 1))

theorem innerIntegrand_bounds {q : Outer} (hq : q ∈ outerDomain ∅)
    {r : Inner} (hr : r ∈ innerDomain q.2) :
    0≤innerIntegrand q r ∧ innerIntegrand q r≤U1011OriginalSixteenPointwiseFibre.fibreBound := by
  have hv := (mem_jointDomain_join_iff ∅ q r).2 ⟨hq,hr⟩
  have hK := jointKernel_bounds hv
  have hw : 0<r 1 := by linarith [hr.1]
  have hz := hw.trans hr.2.1
  have hza : (417/5000 : ℝ)≤r 0 := hr.1.trans hr.2.1.le
  have hden : (417/5000 : ℝ)^2≤r 0*r 1 := by
    simpa only [pow_two] using mul_le_mul hza hr.1 (by norm_num : (0 : ℝ)≤417/5000) hz.le
  refine ⟨div_nonneg hK.1 (mul_pos hz hw).le,?_⟩
  calc
    _ ≤ (|currentK|/(417/5000 : ℝ))/(r 0*r 1) :=
      div_le_div_of_nonneg_right hK.2 (mul_pos hz hw).le
    _ ≤ (|currentK|/(417/5000 : ℝ))/((417/5000 : ℝ)^2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by norm_num [U1011OriginalSixteenPointwiseFibre.fibreBound] <;> ring

theorem innerDomain_subset_compact {q : Outer} (hq : q ∈ outerDomain ∅) :
    innerDomain q.2 ⊆ Icc (fun _ : Fin 2 => (417/5000 : ℝ)) (fun _ => (19/125 : ℝ)) := by
  intro r hr
  have hy := (lt_min_iff.mp hq.2.2.2.1).2
  constructor <;> intro i <;> fin_cases i <;> dsimp
  all_goals linarith [hr.1,hr.2.1,hr.2.2]

/-- Every low OR high outer pair has an integrable complete inner pair. -/
theorem integrableOn_innerIntegrand {q : Outer} (hq : q ∈ outerDomain ∅) :
    IntegrableOn (innerIntegrand q) (innerDomain q.2) := by
  have hi : IntegrableOn (fun _ : Inner => U1011OriginalSixteenPointwiseFibre.fibreBound)
      (Icc (fun _ : Fin 2 => (417/5000 : ℝ)) (fun _ => (19/125 : ℝ))) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  apply (hi.mono_set (innerDomain_subset_compact hq)).mono_nonneg
    (measurable_innerIntegrand q).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_innerDomain q.2)] with r hr
    exact (innerIntegrand_bounds hq hr).1
  · filter_upwards [ae_restrict_mem (measurableSet_innerDomain q.2)] with r hr
    exact (innerIntegrand_bounds hq hr).2

theorem integrableOn_retained_innerIntegrand {M : Set Outer} {q : Outer}
    (hq : q ∈ outerDomain M) : IntegrableOn (innerIntegrand q) (innerDomain q.2) :=
  integrableOn_innerIntegrand (outerDomain_subset_unmasked M hq)

theorem jointFibreCost_nonneg {q : Outer} (hq : q ∈ outerDomain ∅) : 0≤jointFibreCost q := by
  apply setIntegral_nonneg (measurableSet_innerDomain q.2)
  intro r hr
  exact (innerIntegrand_bounds hq hr).1

theorem jointFibreCost_eq_nested {q : Outer} (hq : q ∈ outerDomain ∅) :
    jointFibreCost q=∫ z in Ioo (417/5000 : ℝ) q.2,
      ∫ w in Ico (417/5000 : ℝ) z,jointKernel ![q.1,q.2,z,w]/(z*w) := by
  let F := (innerDomain q.2).indicator (innerIntegrand q)
  have hF : Integrable F := (integrableOn_innerIntegrand hq).integrable_indicator
    (measurableSet_innerDomain q.2)
  have htwo : (∫ r : Inner,F r)=∫ z : ℝ,∫ w : ℝ,F ![z,w] := by
    calc
      _ = ∫ z : ℝ,∫ w : ℝ,∫ v : Fin 0 → ℝ,F (Fin.cons z (Fin.cons w v)) := integral_fin_pair F hF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        apply integral_congr_ae
        filter_upwards [] with w
        rw [integral_fin_zero]
        rfl
  have hpoint (z w : ℝ) : F ![z,w]=
      (Ioo (417/5000 : ℝ) q.2).indicator (fun z =>
        (Ico (417/5000 : ℝ) z).indicator (fun w => jointKernel ![q.1,q.2,z,w]/(z*w)) w) z := by
    by_cases hz : z ∈ Ioo (417/5000 : ℝ) q.2 <;>
      by_cases hw : w ∈ Ico (417/5000 : ℝ) z <;>
      simp_all only [F,Set.indicator_apply,U1011OriginalSixteenPointwiseFibre.mem_innerDomain_vec,
        and_self,and_true,and_false,true_and,false_and,if_true,if_false,innerIntegrand,join]
  calc
    _ = ∫ r : Inner,F r := (integral_indicator (measurableSet_innerDomain q.2)).symm
    _ = ∫ z : ℝ,∫ w : ℝ,F ![z,w] := htwo
    _ = ∫ z : ℝ,(Ioo (417/5000 : ℝ) q.2).indicator
        (fun z => ∫ w in Ico (417/5000 : ℝ) z,jointKernel ![q.1,q.2,z,w]/(z*w)) z := by
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ Ioo (417/5000 : ℝ) q.2
      · rw [indicator_of_mem hz]
        simp_rw [hpoint,indicator_of_mem hz]
        exact integral_indicator measurableSet_Ico
      · rw [indicator_of_notMem hz]
        simp_rw [hpoint,indicator_of_notMem hz]
        simp only [integral_zero]
    _ = _ := integral_indicator measurableSet_Ioo

def zeroExtended (M : Set Outer) : LogFour → ℝ :=
  (jointDomain M).indicator (fun v => jointKernel v*harmonicDensity v)
def jointZeroExtended (M : Set Outer) (p : Outer × Inner) : ℝ := zeroExtended M (join p.1 p.2)

theorem integrableOn_jointWeighted (M : Set Outer) :
    IntegrableOn (fun v => jointKernel v*harmonicDensity v) (jointDomain M) :=
  U1011OriginalJointHarmonic.integrableOn_weighted_D10.union
    (U1011OriginalJointHarmonic.integrableOn_weighted_D11 M)

theorem integrable_zeroExtended (M : Set Outer) (hM : MeasurableSet M) : Integrable (zeroExtended M) :=
  (integrableOn_jointWeighted M).integrable_indicator (measurableSet_jointDomain M hM)

theorem zeroExtended_join (M : Set Outer) (q : Outer) (r : Inner) :
    zeroExtended M (join q r)=(outerDomain M).indicator
      (fun q => (1/(q.1*q.2))*(innerDomain q.2).indicator (innerIntegrand q) r) q := by
  by_cases hq : q ∈ outerDomain M
  · by_cases hr : r ∈ innerDomain q.2
    · have hv := (mem_jointDomain_join_iff M q r).2 ⟨hq,hr⟩
      simp only [zeroExtended,indicator_of_mem hv,indicator_of_mem hq,indicator_of_mem hr]
      rw [harmonicDensity_join]
      unfold innerIntegrand
      ring
    · have hv : join q r ∉ jointDomain M := fun h => hr ((mem_jointDomain_join_iff M q r).1 h).2
      simp only [zeroExtended,indicator_of_notMem hv,indicator_of_mem hq,indicator_of_notMem hr,mul_zero]
  · have hv : join q r ∉ jointDomain M := fun h => hq ((mem_jointDomain_join_iff M q r).1 h).1
    simp only [zeroExtended,indicator_of_notMem hv,indicator_of_notMem hq]

theorem integrable_jointZeroExtended (M : Set Outer) (hM : MeasurableSet M) :
    Integrable (jointZeroExtended M) := by
  have h := split_measurePreserving.symm.integrable_comp_of_integrable (integrable_zeroExtended M hM)
  simpa only [Function.comp_def,split_symm_apply,jointZeroExtended] using h

theorem integral_joint_section (M : Set Outer) (q : Outer) :
    (∫ r : Inner,jointZeroExtended M (q,r))=(outerDomain M).indicator jointOuterCost q := by
  simp only [jointZeroExtended,zeroExtended_join]
  by_cases hq : q ∈ outerDomain M
  · simp only [indicator_of_mem hq]
    rw [integral_const_mul,integral_indicator (measurableSet_innerDomain q.2)]
    unfold jointOuterCost jointFibreCost
    ring
  · simp only [indicator_of_notMem hq,integral_zero]

theorem integrableOn_jointOuterCost (M : Set Outer) (hM : MeasurableSet M) :
    IntegrableOn jointOuterCost (outerDomain M) := by
  have hi := (integrable_jointZeroExtended M hM).integral_prod_left
  have heq : (fun q : Outer => ∫ r : Inner,jointZeroExtended M (q,r))=
      (outerDomain M).indicator jointOuterCost := by
    funext q
    exact integral_joint_section M q
  rw [heq] at hi
  exact (integrable_indicator_iff (measurableSet_outerDomain M hM)).1 hi

/-- True JOINT weighted Fubini with conditional high-band-only deletion. -/
theorem integral_joint_eq_outer_fibre (M : Set Outer) (hM : MeasurableSet M) :
    (∫ v in jointDomain M,jointKernel v*harmonicDensity v)=
      ∫ q in outerDomain M,jointFibreCost q/(q.1*q.2) := by
  calc
    _ = ∫ v,zeroExtended M v := (integral_indicator (measurableSet_jointDomain M hM)).symm
    _ = ∫ p : Outer × Inner,jointZeroExtended M p := by
      have h := (split_measurePreserving.symm.integral_comp' (zeroExtended M)).symm
      simpa only [Function.comp_def,split_symm_apply,jointZeroExtended] using h
    _ = ∫ q : Outer,∫ r : Inner,jointZeroExtended M (q,r) := integral_prod _ (integrable_jointZeroExtended M hM)
    _ = ∫ q : Outer,(outerDomain M).indicator jointOuterCost q := by
      apply integral_congr_ae
      exact Eventually.of_forall (integral_joint_section M)
    _ = _ := integral_indicator (measurableSet_outerDomain M hM)

theorem integral_joint_eq_outer_nested (M : Set Outer) (hM : MeasurableSet M) :
    (∫ v in jointDomain M,jointKernel v*harmonicDensity v)=
      ∫ q in outerDomain M,
        (∫ z in Ioo (417/5000 : ℝ) q.2,
          ∫ w in Ico (417/5000 : ℝ) z,jointKernel ![q.1,q.2,z,w]/(z*w))/(q.1*q.2) := by
  rw [integral_joint_eq_outer_fibre M hM]
  apply setIntegral_congr_fun (measurableSet_outerDomain M hM)
  intro q hq
  rw [jointFibreCost_eq_nested (outerDomain_subset_unmasked M hq)]

/-- Direct actual17572 STATIC-mask joint supplier already proved by sf,
now with its genuine complete inner-fibre integral displayed. -/
theorem actual_jointIntegral_eq_outer (S : Finset U1011OriginalJointHarmonic.Row) :
    U1011OriginalJointHarmonic.jointIntegral S=
      ∫ q in outerDomain (U1011OriginalPairedFixedMaskHarmonic.outerUnion S),jointOuterCost q := by
  have hrow (r : U1011OriginalJointHarmonic.Row) :
      MeasurableSet (Certificates.PairedV2.FullMask.P1E0E1.pairCell r) :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const)))
  have hM : MeasurableSet (U1011OriginalPairedFixedMaskHarmonic.outerUnion S) :=
    Finset.measurableSet_biUnion S (fun r _ => hrow r)
  exact integral_joint_eq_outer_fibre _ hM

end

end ImbalancedChen.P5Z.U1011OriginalJointOuterFibre
