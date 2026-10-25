import ImbalancedChen.P5ZU1011OriginalSixteenOuterFibre

/-!
# Every original outer pair has a genuine integrable inner full16 cost

The Fubini theorem alone gives a.e. slices. Actual boundedness by the
switched fallback removes that exception for every retained last pair.
The resulting pointwise fibre dictionary keeps z strict at both ends and
w weak at a, strict at z. No outer mask or four-tuple selector is introduced.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPointwiseFibre

noncomputable section
open Set MeasureTheory Filter
open Classical
open U11Integral U11Canonical U1011OriginalSixteenOuterFibre

def fibreBound : ℝ := |currentK|/(417/5000 : ℝ)^3

theorem continuous_join (q : Outer) : Continuous (fun r : Inner => join q r) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [join] using (continuous_const : Continuous (fun _ : Inner => q.1))
  · simpa [join] using (continuous_const : Continuous (fun _ : Inner => q.2))
  · simpa [join] using (continuous_apply 0 : Continuous (fun r : Inner => r 0))
  · simpa [join] using (continuous_apply 1 : Continuous (fun r : Inner => r 1))

theorem measurable_innerIntegrand (q : Outer) : Measurable (innerIntegrand q) := by
  exact (U1011OriginalSixteenReassembly.measurable_actualMinimum.comp (continuous_join q).measurable).div
    ((measurable_pi_apply 0).mul (measurable_pi_apply 1))

/-- Exact actual full-bank domination, uniform over every retained outer
pair and every original first-pair point. No slice estimate is assumed. -/
theorem innerIntegrand_bounds {q : Outer} (hq : q ∈ outerDomain ∅)
    {r : Inner} (hr : r ∈ innerDomain q.2) :
    0≤innerIntegrand q r ∧ innerIntegrand q r≤fibreBound := by
  have hv := (mem_originalDomain_join_iff ∅ q r).2 ⟨hq,hr⟩
  have hactual := U1011OriginalSixteenReassembly.actualMinimum_bounds ∅ (join q r) hv
  have hw : 0<r 1 := by have ha := hr.1; linarith
  have hz : 0<r 0 := hw.trans hr.2.1
  have hza : (417/5000 : ℝ)≤r 0 := hr.1.trans hr.2.1.le
  have hden : (417/5000 : ℝ)^2≤r 0*r 1 := by
    simpa only [pow_two] using mul_le_mul hza hr.1 (by norm_num : (0 : ℝ)≤417/5000) hz.le
  have hswitched := abs_canonical_switched_le ∅ currentK (join q r) hv
  have hupper : actualMinimum (join q r)≤|currentK|/(417/5000 : ℝ) :=
    hactual.2.trans ((le_abs_self _).trans hswitched)
  refine ⟨div_nonneg hactual.1 (mul_pos hz hw).le,?_⟩
  calc
    _ ≤ (|currentK|/(417/5000 : ℝ))/(r 0*r 1) :=
      div_le_div_of_nonneg_right hupper (mul_pos hz hw).le
    _ ≤ (|currentK|/(417/5000 : ℝ))/((417/5000 : ℝ)^2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by norm_num [fibreBound] <;> ring

/-- The complete inner fibre is contained in one fixed finite-volume box.
This uses only the actual y<h outer wall and the literal first-pair order. -/
theorem innerDomain_subset_compact {q : Outer} (hq : q ∈ outerDomain ∅) :
    innerDomain q.2 ⊆ Icc (fun _ : Fin 2 => (417/5000 : ℝ)) (fun _ => (19/125 : ℝ)) := by
  intro r hr
  have hy := hq.2.2.2.1
  constructor <;> intro i <;> fin_cases i <;> dsimp
  all_goals have ha := hr.1
  all_goals have hwz := hr.2.1
  all_goals have hzy := hr.2.2
  all_goals linarith

/-- Integrability holds at EVERY retained last pair, not only outside an
unspecified null exceptional set. The actual switched majorant pays it. -/
theorem integrableOn_innerIntegrand {q : Outer} (hq : q ∈ outerDomain ∅) :
    IntegrableOn (innerIntegrand q) (innerDomain q.2) := by
  have hi : IntegrableOn (fun _ : Inner => fibreBound)
      (Icc (fun _ : Fin 2 => (417/5000 : ℝ)) (fun _ => (19/125 : ℝ))) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hc := hi.mono_set (innerDomain_subset_compact hq)
  apply hc.mono_nonneg (measurable_innerIntegrand q).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_innerDomain q.2)] with r hr
    exact (innerIntegrand_bounds hq hr).1
  · filter_upwards [ae_restrict_mem (measurableSet_innerDomain q.2)] with r hr
    exact (innerIntegrand_bounds hq hr).2

theorem mem_innerDomain_vec (y z w : ℝ) :
    (![z,w] : Inner) ∈ innerDomain y ↔
      z ∈ Ioo (417/5000 : ℝ) y ∧ w ∈ Ico (417/5000 : ℝ) z := by
  change ((417/5000 : ℝ)≤w ∧ w<z ∧ z<y) ↔
    (((417/5000 : ℝ)<z ∧ z<y) ∧ ((417/5000 : ℝ)≤w ∧ w<z))
  constructor
  · rintro ⟨ha,hwz,hzy⟩
    exact ⟨⟨ha.trans_lt hwz,hzy⟩,ha,hwz⟩
  · rintro ⟨⟨haz,hzy⟩,ha,hwz⟩
    exact ⟨ha,hwz,hzy⟩

/-- Explicit inner(z,w) dictionary at every actual outer pair. All full16
minima, cap branches, H248 seams and square tests remain INSIDE the integral. -/
theorem fibreCost_eq_nested {q : Outer} (hq : q ∈ outerDomain ∅) :
    fibreCost q=∫ z in Ioo (417/5000 : ℝ) q.2,
      ∫ w in Ico (417/5000 : ℝ) z, actualMinimum ![q.1,q.2,z,w]/(z*w) := by
  let F := (innerDomain q.2).indicator (innerIntegrand q)
  have hF : Integrable F := (integrableOn_innerIntegrand hq).integrable_indicator
    (measurableSet_innerDomain q.2)
  have htwo : (∫ r : Inner, F r)=∫ z : ℝ,∫ w : ℝ,F ![z,w] := by
    calc
      _ = ∫ z : ℝ,∫ w : ℝ,∫ v : Fin 0 → ℝ,F (Fin.cons z (Fin.cons w v)) :=
        integral_fin_pair F hF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        apply integral_congr_ae
        filter_upwards [] with w
        rw [integral_fin_zero]
        rfl
  have hpoint (z w : ℝ) : F ![z,w]=
      (Ioo (417/5000 : ℝ) q.2).indicator
        (fun z => (Ico (417/5000 : ℝ) z).indicator
          (fun w => actualMinimum ![q.1,q.2,z,w]/(z*w)) w) z := by
    by_cases hz : z ∈ Ioo (417/5000 : ℝ) q.2 <;>
      by_cases hw : w ∈ Ico (417/5000 : ℝ) z <;>
      simp_all only [F,Set.indicator_apply,mem_innerDomain_vec,and_self,and_true,and_false,
        true_and,false_and,if_true,if_false,innerIntegrand,join]
  calc
    _ = ∫ r : Inner,F r := (integral_indicator (measurableSet_innerDomain q.2)).symm
    _ = ∫ z : ℝ,∫ w : ℝ,F ![z,w] := htwo
    _ = ∫ z : ℝ,(Ioo (417/5000 : ℝ) q.2).indicator
        (fun z => ∫ w in Ico (417/5000 : ℝ) z,
          actualMinimum ![q.1,q.2,z,w]/(z*w)) z := by
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

/-- The full original weighted integral with the ACTUAL inner(z,w)
limits displayed. A fixed outer mask still removes whole last-pair fibres. -/
theorem integral_original_eq_outer_nested (mask : Set Outer) (hm : MeasurableSet mask) :
    (∫ v in originalDomain mask,actualMinimum v*harmonicDensity v)=
      ∫ q in outerDomain mask,
        (∫ z in Ioo (417/5000 : ℝ) q.2,
          ∫ w in Ico (417/5000 : ℝ) z,actualMinimum ![q.1,q.2,z,w]/(z*w))/(q.1*q.2) := by
  rw [integral_original_eq_outer_fibre mask hm]
  apply setIntegral_congr_fun (measurableSet_outerDomain mask hm)
  intro q hq
  have hbase : q ∈ outerDomain ∅ :=
    ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1,by simp⟩
  rw [fibreCost_eq_nested hbase]

end
end ImbalancedChen.P5Z.U1011OriginalSixteenPointwiseFibre
